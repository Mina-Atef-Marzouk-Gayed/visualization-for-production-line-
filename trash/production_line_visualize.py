#!/usr/bin/env python3
"""
Production Line Visualizer - Complete 6-station pipeline visualization
AUTOMATIC STATION LAUNCH: Launches all station visualizers as separate processes
"""

import sys
import os
import re
import time
import math
import traceback
import collections
import copy
import bisect
import threading
import subprocess
from typing import *
from dataclasses import dataclass, field
from datetime import datetime
from enum import Enum

# ===== CONFIGURATION =====
SEARCH_ROOT = "."
MAX_EVENTS_PER_STATION = 10000
TIMER_FPS = 30
SNAPSHOT_LINES = 2000
IDLE_TIMEOUT = 5.0
LONG_IDLE_TIMEOUT = 15.0
AUTO_SWITCH_ON_IDLE = False

# Station configuration
STATIONS = {
    "ST1": {"name": "ST1 - Loading", "color": "#4FC3F7"},
    "ST2": {"name": "ST2 - Assembly", "color": "#29B6F6"},
    "ST3": {"name": "ST3 - Testing", "color": "#0288D1"},
    "ST4": {"name": "ST4 - Calibration", "color": "#0277BD"},
    "ST5": {"name": "ST5 - Quality", "color": "#01579B"},
    "ST6": {"name": "ST6 - Packaging", "color": "#039BE5"},
}

# ===== QT IMPORTS =====
try:
    from PySide6.QtWidgets import *
    from PySide6.QtCore import *
    from PySide6.QtGui import *
    QT_AVAILABLE = True
except Exception as e:
    print(f"ERROR importing PySide6: {e}")
    print("Python executable:", sys.executable)
    print("\nERROR: PySide6 not installed. Install with: pip install PySide6")
    sys.exit(1)

# ===== DATA MODELS =====
class TokenState(Enum):
    """State of a part token in the pipeline"""
    WAITING = 0
    IN_PROCESS = 1
    PASS = 2
    FAIL = 3
    COMPLETE = 4

@dataclass
class Token:
    """Part token moving through the pipeline"""
    id: int
    current_station: str = "ST1"  # Which station is processing it
    target_station: str = "ST1"   # Where it's moving to
    position: float = 0.0  # 0.0-1.0 between stations
    state: TokenState = TokenState.WAITING
    created_at_ns: int = 0
    started_at_ns: int = 0
    completed_at_ns: int = 0
    batch_id: str = ""
    part_id: str = ""
    inspection_result: str = ""  # "PASS" or "REJECT" for ST5

@dataclass
class StationEvent:
    """Event from a station log"""
    t_ns: int
    station_id: str
    ready: bool = False
    busy: bool = False
    done: bool = False
    fault: bool = False
    cycle_time_ms: Optional[float] = None
    extra: Dict[str, Any] = field(default_factory=dict)

# ===== CARRY-FORWARD PARSER =====
class StationLogParser:
    """Generic carry-forward parser for station logs"""
    
    def __init__(self, station_id: str):
        self.station_id = station_id
        self.reset()
    
    def reset(self):
        """Reset parser state"""
        self.last_vsi_time_ns = None
        self.synthetic_time_ns = 0
        
        # Carry-forward state
        self.carried_state = {
            'ready': None,
            'busy': None,
            'done': None,
            'fault': None,
        }
        self.carried_cycle_time = None
        self.carried_extra = {}
        
        self.has_seen_any_state = False
        
        # Patterns
        self.vsi_time_pattern = re.compile(r"VSI\s+time\s*:\s*(\d+)\s*ns", re.IGNORECASE)
        self.cycle_time_pattern = re.compile(
            r"\bcycle(?:[_\s]*time)(?:[_\s]*ms)?\b\s*[:=]\s*([\d.]+)\s*(?:ms)?\b",
            re.IGNORECASE
        )
        
        # Generic key-value pattern
        self.key_value_pattern = re.compile(
            r"(?!cycle[_\s]*time)(\w+)[_\s]*[:=]\s*([\w.]+)", 
            re.IGNORECASE
        )
        
        # Station-specific patterns
        self.station_patterns = {
            "ready": re.compile(r"\bready\b[_\s]*[:=]\s*([01]|true|false)", re.IGNORECASE),
            "busy": re.compile(r"\bbusy\b[_\s]*[:=]\s*([01]|true|false)", re.IGNORECASE),
            "done": re.compile(r"\bdone\b[_\s]*[:=]\s*([01]|true|false)", re.IGNORECASE),
            "fault": re.compile(r"\bfault\b[_\s]*[:=]\s*([01]|true|false)", re.IGNORECASE),
        }
    
    def seed_from_event(self, event: StationEvent):
        """Seed the parser with an existing event"""
        self.carried_state = {
            'ready': 1 if event.ready else 0,
            'busy': 1 if event.busy else 0,
            'done': 1 if event.done else 0,
            'fault': 1 if event.fault else 0,
        }
        self.carried_cycle_time = event.cycle_time_ms
        self.carried_extra = copy.deepcopy(event.extra)
        self.has_seen_any_state = True
        self.last_vsi_time_ns = event.t_ns
        self.synthetic_time_ns = event.t_ns
    
    def parse_line(self, line: str) -> Optional[StationEvent]:
        """Parse a line and return an event if state was updated"""
        line = line.strip()
        if not line:
            return None
        
        had_signal = False
        had_done_pulse = False
        
        # Check for VSI time
        vsi_match = self.vsi_time_pattern.search(line)
        if vsi_match:
            self.last_vsi_time_ns = int(vsi_match.group(1))
        
        # Determine timestamp
        if self.last_vsi_time_ns is not None:
            timestamp = self.last_vsi_time_ns
        else:
            self.synthetic_time_ns += 10_000_000  # 10ms increment
            timestamp = self.synthetic_time_ns
        
        # Check for station state updates
        for state_name, pattern in self.station_patterns.items():
            match = pattern.search(line)
            if match:
                try:
                    value_str = match.group(1).lower()
                    value = 1 if value_str == 'true' else 0 if value_str == 'false' else int(value_str)
                    self.carried_state[state_name] = value
                    self.has_seen_any_state = True
                    had_signal = True
                    
                    if state_name == 'done' and value == 1:
                        had_done_pulse = True
                except ValueError:
                    pass
        
        # Check for cycle time
        cycle_match = self.cycle_time_pattern.search(line)
        if cycle_match:
            try:
                cycle_time = float(cycle_match.group(1))
                self.carried_cycle_time = cycle_time
                had_signal = True
            except ValueError:
                pass
        
        # Extract key-value pairs
        current_line_extras = {}
        for match in self.key_value_pattern.finditer(line):
            key, value_str = match.groups()
            key_lower = key.lower()
            
            if key_lower in ['vsi', 'time', 'cycle', 'ready', 'busy', 'done', 'fault']:
                continue
            
            try:
                if '.' in value_str:
                    value = float(value_str)
                elif value_str.lower() in ['true', 'false']:
                    value = value_str.lower() == 'true'
                else:
                    value = int(value_str)
            except ValueError:
                value = value_str
            
            current_line_extras[key] = value
        
        # Update carried extras
        if current_line_extras:
            for key, value in current_line_extras.items():
                self.carried_extra[key] = value
            had_signal = True
        
        # Check for "DONE pulse" lines
        if "done" in line.lower() and "pulse" in line.lower():
            self.carried_state['done'] = 1
            had_done_pulse = True
            self.has_seen_any_state = True
            had_signal = True
        
        # Emit event if any signal found
        if had_signal:
            ready = bool(self.carried_state['ready']) if self.carried_state['ready'] is not None else False
            busy = bool(self.carried_state['busy']) if self.carried_state['busy'] is not None else False
            done = bool(self.carried_state['done']) if self.carried_state['done'] is not None else False
            fault = bool(self.carried_state['fault']) if self.carried_state['fault'] is not None else False
            
            event = StationEvent(
                t_ns=timestamp,
                station_id=self.station_id,
                ready=ready,
                busy=busy,
                done=done,
                fault=fault,
                cycle_time_ms=self.carried_cycle_time,
                extra=copy.deepcopy(self.carried_extra)
            )
            
            # Reset done for one-shot pulse behavior
            if had_done_pulse:
                self.carried_state['done'] = 0
            
            return event
        
        return None
    
    def get_current_state(self) -> Optional[StationEvent]:
        """Get current state without parsing a line"""
        if not self.has_seen_any_state and self.carried_cycle_time is None and not self.carried_extra:
            return None
        
        timestamp = self.last_vsi_time_ns if self.last_vsi_time_ns is not None else self.synthetic_time_ns
        
        ready = bool(self.carried_state['ready']) if self.carried_state['ready'] is not None else False
        busy = bool(self.carried_state['busy']) if self.carried_state['busy'] is not None else False
        done = bool(self.carried_state['done']) if self.carried_state['done'] is not None else False
        fault = bool(self.carried_state['fault']) if self.carried_state['fault'] is not None else False
        
        return StationEvent(
            t_ns=timestamp,
            station_id=self.station_id,
            ready=ready,
            busy=busy,
            done=done,
            fault=fault,
            cycle_time_ms=self.carried_cycle_time,
            extra=copy.deepcopy(self.carried_extra)
        )

# ===== LOG DISCOVERY =====
class LogDiscoverer:
    @staticmethod
    def find_station_logs() -> Dict[str, str]:
        """Find newest log files for each station"""
        station_logs = {}
        all_logs = []
        
        # Search recursively from SEARCH_ROOT
        for root, dirs, files in os.walk(SEARCH_ROOT):
            for file in files:
                file_lower = file.lower()
                if file_lower.endswith('.log') and 'check.' in file_lower:
                    full_path = os.path.join(root, file)
                    mtime = os.path.getmtime(full_path)
                    
                    # Determine station ID
                    station_id = None
                    for st_id in STATIONS.keys():
                        if st_id.lower() in file_lower:
                            station_id = st_id
                            break
                    
                    # Also check for PLC coordinator log
                    if 'plc' in file_lower and 'coordinator' in file_lower:
                        station_id = "PLC"
                    
                    if station_id:
                        # Score: prefer files containing station name
                        score = 0
                        station_name = STATIONS.get(station_id, {}).get('name', '').split(' - ')[-1].lower()
                        if station_name and station_name in file_lower:
                            score = 1
                        
                        all_logs.append((score, mtime, station_id, full_path))
        
        # Group by station, pick highest score, then newest
        logs_by_station = {}
        for score, mtime, station_id, path in all_logs:
            if station_id not in logs_by_station:
                logs_by_station[station_id] = []
            logs_by_station[station_id].append((score, mtime, path))
        
        # Select best log for each station
        for station_id, logs in logs_by_station.items():
            logs.sort(key=lambda x: (-x[0], -x[1]))  # Score desc, mtime desc
            if logs:
                station_logs[station_id] = logs[0][2]
        
        print(f"Found logs for stations: {list(station_logs.keys())}")
        return station_logs

# ===== TAIL WORKER =====
class LogTailWorker(QThread):
    """Worker thread to tail a station log file"""
    new_event = Signal(StationEvent)
    activity_detected = Signal(str)  # station_id
    file_reopened = Signal(str)      # station_id
    
    def __init__(self, station_id: str, log_path: str, seed_event: Optional[StationEvent] = None):
        super().__init__()
        self.station_id = station_id
        self.log_path = log_path
        self.seed_event = seed_event
        self.running = True
        self.file_handle = None
        self.file_position = 0
        self.file_inode = None
        self.parser = StationLogParser(station_id)
        self.last_activity_time = time.time()
    
    def run(self):
        """Tail the log file and emit new events"""
        self._open_file(seed=True)
        
        while self.running:
            try:
                if not self.file_handle:
                    time.sleep(0.1)
                    continue
                
                # Check for file rotation/truncation
                try:
                    current_size = os.path.getsize(self.log_path)
                    current_inode = os.stat(self.log_path).st_ino
                    
                    if current_inode != self.file_inode or current_size < self.file_position:
                        print(f"{self.station_id}: File rotated/truncated, reopening...")
                        self._open_file(seed=True)
                        self.file_reopened.emit(self.station_id)
                        continue
                except (OSError, IOError):
                    time.sleep(1)
                    continue
                
                # Read new lines
                try:
                    self.file_handle.seek(self.file_position)
                    new_lines = self.file_handle.readlines()
                    self.file_position = self.file_handle.tell()
                except (OSError, IOError) as e:
                    print(f"{self.station_id}: Error reading file: {e}")
                    self._open_file(seed=True)
                    self.file_reopened.emit(self.station_id)
                    continue
                
                # Parse lines
                if new_lines:
                    self.last_activity_time = time.time()
                    self.activity_detected.emit(self.station_id)
                    
                    for line in new_lines:
                        event = self.parser.parse_line(line)
                        if event:
                            self.new_event.emit(event)
                
                time.sleep(0.05)  # 50ms sleep
                
            except Exception as e:
                print(f"{self.station_id}: Error in tail worker: {e}")
                time.sleep(1)
        
        # Cleanup
        if self.file_handle:
            self.file_handle.close()
    
    def _open_file(self, seed=False):
        """Open or reopen the log file"""
        try:
            if self.file_handle:
                self.file_handle.close()
            
            self.file_handle = open(self.log_path, 'r', encoding='utf-8', errors='ignore')
            self.file_handle.seek(0, os.SEEK_END)
            self.file_position = self.file_handle.tell()
            
            self.file_inode = os.stat(self.log_path).st_ino
            self.parser = StationLogParser(self.station_id)
            
            if seed and self.seed_event:
                self.parser.seed_from_event(self.seed_event)
                
        except Exception as e:
            print(f"{self.station_id}: Error opening {self.log_path}: {e}")
            self.file_handle = None
    
    def reseed_parser(self, seed_event: StationEvent):
        """Reseed the parser with a new event"""
        self.seed_event = seed_event
        self.parser.seed_from_event(seed_event)
    
    def stop(self):
        """Stop the worker thread"""
        self.running = False
        if self.isRunning():
            self.wait()

# ===== STATION PROCESS MANAGER =====
class StationProcessManager(QObject):
    """Manages station visualizer processes"""
    
    process_state_changed = Signal()  # Emitted when any process state changes
    
    def __init__(self, parent=None):
        super().__init__(parent)
        self.processes = {}  # station_id -> QProcess
        self.process_states = {}  # station_id -> state string
        self.working_dir = os.path.dirname(os.path.abspath(__file__))
        self.python_exe = sys.executable
        
    def start_station(self, station_id: str):
        """Start a single station visualizer process"""
        if station_id in self.processes and self.processes[station_id].state() != QProcess.NotRunning:
            print(f"{station_id} is already running")
            return False
        
        script_name = f"{station_id.lower()}_visualizer.py"
        script_path = os.path.join(self.working_dir, script_name)
        
        if not os.path.exists(script_path):
            print(f"Error: {script_name} not found in {self.working_dir}")
            self.process_states[station_id] = "ERROR: File not found"
            self.process_state_changed.emit()
            return False
        
        process = QProcess()
        process.setProcessChannelMode(QProcess.MergedChannels)
        process.setWorkingDirectory(self.working_dir)
        
        # Connect signals
        process.readyReadStandardOutput.connect(
            lambda: self._handle_output(station_id, process)
        )
        process.readyReadStandardError.connect(
            lambda: self._handle_error(station_id, process)
        )
        process.stateChanged.connect(
            lambda state: self._handle_state_change(station_id, state)
        )
        process.errorOccurred.connect(
            lambda error: self._handle_process_error(station_id, error)
        )
        process.finished.connect(
            lambda exitCode, exitStatus: self._handle_finished(station_id, exitCode, exitStatus)
        )
        
        # Start the process
        print(f"Starting {station_id}: {script_path}")
        process.start(self.python_exe, [script_path])
        
        if process.waitForStarted(5000):  # Wait up to 5 seconds
            self.processes[station_id] = process
            self.process_states[station_id] = "Starting..."
            print(f"{station_id} started successfully")
            self.process_state_changed.emit()
            return True
        else:
            error_msg = f"Failed to start {station_id}: Timeout"
            print(error_msg)
            self.process_states[station_id] = error_msg
            self.process_state_changed.emit()
            return False
    
    def stop_station(self, station_id: str):
        """Stop a single station visualizer process"""
        if station_id not in self.processes:
            return True
        
        process = self.processes[station_id]
        
        if process.state() != QProcess.NotRunning:
            print(f"Stopping {station_id}...")
            
            # Try graceful termination first
            process.terminate()
            if not process.waitForFinished(2000):  # Wait 2 seconds
                print(f"{station_id} didn't terminate gracefully, killing...")
                process.kill()
                process.waitForFinished(1000)
            
            self.process_states[station_id] = "Stopped"
            print(f"{station_id} stopped")
            self.process_state_changed.emit()
        
        return True
    
    def restart_station(self, station_id: str):
        """Restart a single station visualizer process"""
        self.stop_station(station_id)
        # Small delay before restart
        QTimer.singleShot(300, lambda: self.start_station(station_id))
    
    def start_all_stations(self):
        """Start all station visualizers with delays between them"""
        print(f"Starting all station visualizers from {self.working_dir}")
        
        # Start each station with increasing delay to avoid spikes
        for i, station_id in enumerate(STATIONS.keys()):
            delay = i * 250  # 250ms between starts
            QTimer.singleShot(delay, lambda st_id=station_id: self.start_station(st_id))
    
    def stop_all_stations(self):
        """Stop all station visualizers"""
        print("Stopping all station visualizers...")
        for station_id in list(self.processes.keys()):
            self.stop_station(station_id)
    
    def restart_all_stations(self):
        """Restart all station visualizers"""
        print("Restarting all station visualizers...")
        self.stop_all_stations()
        QTimer.singleShot(1000, self.start_all_stations)  # Wait 1 second before restarting
    
    def get_status_summary(self) -> str:
        """Get summary of all process states"""
        running = 0
        stopped = 0
        error = 0
        
        for station_id in STATIONS.keys():
            state = self.process_states.get(station_id, "Unknown")
            if "running" in state.lower():
                running += 1
            elif "error" in state.lower() or "failed" in state.lower():
                error += 1
            else:
                stopped += 1
        
        return f"Station UIs: {running} running / {error} error / {stopped} stopped"
    
    def get_detailed_status(self) -> Dict[str, str]:
        """Get detailed status for all stations"""
        status = {}
        for station_id in STATIONS.keys():
            if station_id in self.processes:
                process = self.processes[station_id]
                state = process.state()
                if state == QProcess.Running:
                    status[station_id] = "Running"
                elif state == QProcess.Starting:
                    status[station_id] = "Starting"
                else:
                    status[station_id] = self.process_states.get(station_id, "Stopped")
            else:
                status[station_id] = self.process_states.get(station_id, "Not started")
        return status
    
    def _handle_output(self, station_id: str, process: QProcess):
        """Handle process stdout"""
        if process:
            data = process.readAllStandardOutput().data().decode('utf-8', errors='ignore')
            if data.strip():
                # Add station prefix to output
                for line in data.strip().split('\n'):
                    if line.strip():
                        print(f"[{station_id}] {line}")
    
    def _handle_error(self, station_id: str, process: QProcess):
        """Handle process stderr"""
        if process:
            data = process.readAllStandardError().data().decode('utf-8', errors='ignore')
            if data.strip():
                # Add station prefix to error output
                for line in data.strip().split('\n'):
                    if line.strip():
                        print(f"[{station_id} ERROR] {line}")
    
    def _handle_state_change(self, station_id: str, state: QProcess.ProcessState):
        """Handle process state change"""
        if state == QProcess.Running:
            self.process_states[station_id] = "Running"
            print(f"{station_id} is now running")
        elif state == QProcess.Starting:
            self.process_states[station_id] = "Starting..."
        elif state == QProcess.NotRunning:
            if station_id in self.process_states and "Stopped" not in self.process_states[station_id]:
                self.process_states[station_id] = "Exited"
                print(f"{station_id} has exited")
        
        self.process_state_changed.emit()
    
    def _handle_process_error(self, station_id: str, error: QProcess.ProcessError):
        """Handle process errors"""
        error_msgs = {
            QProcess.FailedToStart: "Failed to start",
            QProcess.Crashed: "Crashed",
            QProcess.Timedout: "Timed out",
            QProcess.WriteError: "Write error",
            QProcess.ReadError: "Read error",
            QProcess.UnknownError: "Unknown error"
        }
        
        error_msg = error_msgs.get(error, "Unknown error")
        full_msg = f"{error_msg}"
        self.process_states[station_id] = full_msg
        print(f"{station_id}: {full_msg}")
        self.process_state_changed.emit()
    
    def _handle_finished(self, station_id: str, exitCode: int, exitStatus: QProcess.ExitStatus):
        """Handle process finished"""
        if exitStatus == QProcess.NormalExit:
            status = f"Exited normally (code: {exitCode})"
        else:
            status = f"Crashed (code: {exitCode})"
        
        self.process_states[station_id] = status
        print(f"{station_id}: {status}")
        self.process_state_changed.emit()

# ===== PIPELINE VISUALIZATION WIDGET =====
class PipelineWidget(QWidget):
    """Widget that draws the 6-station pipeline with tokens"""
    
    def __init__(self, parent=None):
        super().__init__(parent)
        self.station_states = {st_id: {
            'ready': False,
            'busy': False,
            'done': False,
            'fault': False,
            'cycle_time_ms': None,
            'extra': {},
            'last_activity': 0,
            'token_id': None,  # Token currently being processed
            'buffer': []  # Tokens waiting at this station
        } for st_id in STATIONS.keys()}
        
        self.tokens = []  # All tokens in the system
        self.next_token_id = 1
        self.animation_time = 0
        
        # Station geometry
        self.station_width = 180
        self.station_height = 160
        self.station_spacing = 220
        self.conveyor_height = 40
        
        # Colors
        self.colors = {
            'background': QColor(30, 30, 40),
            'station_bg': QColor(45, 45, 55),
            'station_border': QColor(80, 80, 100),
            'conveyor': QColor(60, 60, 70),
            'conveyor_active': QColor(100, 100, 120),
            'text': QColor(220, 220, 220),
            'text_dim': QColor(150, 150, 150),
            'ready': QColor(100, 255, 100),
            'busy': QColor(255, 200, 50),
            'done': QColor(100, 200, 255),
            'fault': QColor(255, 100, 100),
            'token_waiting': QColor(200, 200, 200),
            'token_processing': QColor(100, 200, 255),
            'token_pass': QColor(100, 255, 100),
            'token_fail': QColor(255, 100, 100),
            'token_complete': QColor(150, 150, 255),
        }
        
        self.setMinimumSize(1400, 600)
    
    def update_station_state(self, event: StationEvent):
        """Update state for a specific station"""
        if event.station_id not in self.station_states:
            return
        
        station = self.station_states[event.station_id]
        
        # Store old states for edge detection
        old_busy = station['busy']
        old_done = station['done']
        
        # Update state
        station['ready'] = event.ready
        station['busy'] = event.busy
        station['done'] = event.done
        station['fault'] = event.fault
        station['cycle_time_ms'] = event.cycle_time_ms
        station['extra'] = event.extra.copy()
        station['last_activity'] = time.time()
        
        # Token logic
        if event.busy and not old_busy:
            # Busy rising edge - pick up token
            self._pick_up_token(event.station_id)
        
        if event.done and not old_done:
            # Done rising edge - release token
            self._release_token(event.station_id)
        
        self.update()
    
    def _pick_up_token(self, station_id: str):
        """Pick up a token when station becomes busy"""
        station = self.station_states[station_id]
        
        # Check if station already has a token
        if station['token_id'] is not None:
            return
        
        # Get token from buffer or create new one
        if station['buffer']:
            # Take from buffer
            token_id = station['buffer'].pop(0)
            token = next((t for t in self.tokens if t.id == token_id), None)
            if token:
                token.current_station = station_id
                token.state = TokenState.IN_PROCESS
                station['token_id'] = token.id
        elif station_id == "ST1":
            # ST1 creates new tokens
            token = Token(
                id=self.next_token_id,
                current_station=station_id,
                state=TokenState.IN_PROCESS,
                created_at_ns=int(time.time() * 1e9),
                started_at_ns=int(time.time() * 1e9),
            )
            # Extract batch/part info from station extra data
            if 'batch_id' in station['extra']:
                token.batch_id = str(station['extra']['batch_id'])
            if 'part_id' in station['extra']:
                token.part_id = str(station['extra']['part_id'])
            
            self.tokens.append(token)
            station['token_id'] = token.id
            self.next_token_id += 1
    
    def _release_token(self, station_id: str):
        """Release token when station is done"""
        station = self.station_states[station_id]
        
        if station['token_id'] is None:
            return
        
        token_id = station['token_id']
        token = next((t for t in self.tokens if t.id == token_id), None)
        
        if not token:
            station['token_id'] = None
            return
        
        # Update token state based on station
        if station_id == "ST5":
            # ST5 determines pass/fail
            last_accept = station['extra'].get('last_accept', 1)
            if last_accept == 1:
                token.state = TokenState.PASS
                token.inspection_result = "PASS"
            else:
                token.state = TokenState.FAIL
                token.inspection_result = "REJECT"
        elif station_id == "ST6":
            # ST6 completes the token
            token.state = TokenState.COMPLETE
            token.completed_at_ns = int(time.time() * 1e9)
        else:
            # Other stations just process
            token.state = TokenState.WAITING
        
        # Move token to next station or buffer
        station_order = list(STATIONS.keys())
        current_idx = station_order.index(station_id)
        
        if current_idx < len(station_order) - 1:
            next_station = station_order[current_idx + 1]
            token.target_station = next_station
            token.position = 0.0  # Start moving
            
            # Add to next station's buffer
            self.station_states[next_station]['buffer'].append(token.id)
        
        # Clear current station
        station['token_id'] = None
        token.current_station = None
    
    def update_tokens_animation(self, time_delta: float):
        """Update token positions for animation"""
        self.animation_time += time_delta
        
        for token in self.tokens:
            if token.current_station is None and token.target_station:
                # Token is moving between stations
                token.position += 0.5 * time_delta  # Move at constant speed
                
                if token.position >= 1.0:
                    token.position = 1.0
                    # Arrived at target station
                    token.current_station = token.target_station
                    token.target_station = None
                    token.position = 0.0
        
        self.update()
    
    def paintEvent(self, event):
        """Draw the entire pipeline"""
        painter = QPainter(self)
        painter.setRenderHint(QPainter.Antialiasing)
        
        # Draw background
        painter.fillRect(self.rect(), self.colors['background'])
        
        # Calculate layout
        width = self.width()
        height = self.height()
        total_width = len(STATIONS) * self.station_spacing
        start_x = (width - total_width) // 2
        start_y = height // 2 - self.station_height // 2
        
        # Draw main conveyor line
        painter.setPen(QPen(self.colors['conveyor'], 4))
        painter.setBrush(QBrush(self.colors['conveyor']))
        
        conveyor_y = start_y + self.station_height + 30
        painter.drawLine(
            start_x - 50, conveyor_y,
            start_x + total_width + 50, conveyor_y
        )
        
        # Draw conveyor animation (moving stripes)
        if any(s['busy'] for s in self.station_states.values()):
            stripe_offset = int(self.animation_time * 50) % 20
            painter.setPen(QPen(self.colors['conveyor_active'], 2))
            for x in range(start_x - 50, start_x + total_width + 50, 20):
                stripe_x = x + stripe_offset
                painter.drawLine(stripe_x, conveyor_y - 8, stripe_x, conveyor_y + 8)
        
        # Draw each station
        for i, (station_id, station_info) in enumerate(STATIONS.items()):
            station_x = start_x + i * self.station_spacing
            station_y = start_y
            
            self._draw_station(painter, station_id, station_info, 
                             station_x, station_y, i == len(STATIONS) - 1)
        
        # Draw tokens
        self._draw_tokens(painter, start_x, start_y)
        
        # Draw statistics
        self._draw_statistics(painter, width, height)
        
        painter.end()
    
    def _draw_station(self, painter: QPainter, station_id: str, station_info: dict, 
                     x: int, y: int, is_last: bool):
        """Draw a single station box"""
        station = self.station_states[station_id]
        
        # Station background
        painter.setPen(QPen(self.colors['station_border'], 2))
        painter.setBrush(QBrush(self.colors['station_bg']))
        painter.drawRoundedRect(
            x, y, self.station_width, self.station_height, 10, 10
        )
        
        # Station title
        painter.setPen(QPen(self.colors['text']))
        font = QFont("Segoe UI", 11, QFont.Bold)
        painter.setFont(font)
        painter.drawText(
            x + 10, y + 25, 
            station_info['name']
        )
        
        # Station ID badge
        painter.setPen(QPen(QColor(station_info['color']), 2))
        painter.setBrush(QBrush(QColor(30, 30, 40, 200)))
        painter.drawRoundedRect(
            x + self.station_width - 50, y + 10, 40, 25, 5, 5
        )
        painter.setPen(QPen(QColor(station_info['color'])))
        painter.drawText(
            x + self.station_width - 40, y + 27,
            station_id
        )
        
        # Status indicators
        indicator_y = y + 45
        indicator_spacing = 25
        
        # Ready indicator
        self._draw_status_indicator(painter, "R", station['ready'], 
                                   x + 15, indicator_y)
        
        # Busy indicator
        self._draw_status_indicator(painter, "B", station['busy'], 
                                   x + 15 + indicator_spacing, indicator_y)
        
        # Done indicator (pulse if recently active)
        done_active = station['done'] or (time.time() - station['last_activity'] < 0.5)
        self._draw_status_indicator(painter, "D", done_active, 
                                   x + 15 + indicator_spacing * 2, indicator_y)
        
        # Fault indicator
        self._draw_status_indicator(painter, "F", station['fault'], 
                                   x + 15 + indicator_spacing * 3, indicator_y)
        
        # Cycle time
        if station['cycle_time_ms']:
            painter.setPen(QPen(self.colors['text']))
            font = QFont("Segoe UI", 9)
            painter.setFont(font)
            painter.drawText(
                x + 15, indicator_y + 25,
                f"Cycle: {station['cycle_time_ms']:.0f} ms"
            )
        
        # Extra fields (up to 2)
        extra_y = indicator_y + 45
        extra_count = 0
        for key, value in station['extra'].items():
            if key not in ['batch_id', 'part_id', 'last_accept']:
                continue
            
            painter.setPen(QPen(self.colors['text_dim']))
            painter.drawText(
                x + 15, extra_y,
                f"{key}: {value}"
            )
            extra_y += 20
            extra_count += 1
            
            if extra_count >= 2:
                break
        
        # Buffer count (if any)
        buffer_count = len(station['buffer'])
        if buffer_count > 0:
            painter.setPen(QPen(QColor(255, 200, 50)))
            painter.setBrush(QBrush(QColor(255, 200, 50, 100)))
            painter.drawEllipse(
                x + self.station_width - 30, y + self.station_height - 30,
                20, 20
            )
            painter.setPen(QPen(QColor(30, 30, 40)))
            painter.drawText(
                x + self.station_width - 25, y + self.station_height - 15,
                str(buffer_count)
            )
        
        # Draw output conveyor for all but last station
        if not is_last:
            painter.setPen(QPen(self.colors['conveyor'], 3))
            painter.drawLine(
                x + self.station_width, y + self.station_height // 2,
                x + self.station_spacing - 20, y + self.station_height // 2
            )
    
    def _draw_status_indicator(self, painter: QPainter, label: str, 
                              active: bool, x: int, y: int):
        """Draw a status indicator (LED + label)"""
        if active:
            color = {
                'R': self.colors['ready'],
                'B': self.colors['busy'],
                'D': self.colors['done'],
                'F': self.colors['fault'],
            }.get(label, self.colors['text'])
            
            # Pulse effect for Done
            if label == 'D' and active:
                pulse_alpha = int(150 + 100 * math.sin(self.animation_time * 5))
                color = QColor(color.red(), color.green(), color.blue(), pulse_alpha)
            
            painter.setPen(QPen(color, 2))
            painter.setBrush(QBrush(color))
        else:
            painter.setPen(QPen(self.colors['text_dim'], 1))
            painter.setBrush(QBrush(QColor(60, 60, 70)))
        
        painter.drawEllipse(x, y, 16, 16)
        painter.setPen(QPen(QColor(30, 30, 40) if active else self.colors['text_dim']))
        font = QFont("Segoe UI", 9, QFont.Bold)
        painter.setFont(font)
        painter.drawText(x + 5, y + 12, label)
    
    def _draw_tokens(self, painter: QPainter, start_x: int, start_y: int):
        """Draw all tokens in the pipeline"""
        for token in self.tokens:
            token_color = {
                TokenState.WAITING: self.colors['token_waiting'],
                TokenState.IN_PROCESS: self.colors['token_processing'],
                TokenState.PASS: self.colors['token_pass'],
                TokenState.FAIL: self.colors['token_fail'],
                TokenState.COMPLETE: self.colors['token_complete'],
            }.get(token.state, self.colors['token_waiting'])
            
            # Calculate token position
            token_x, token_y = self._get_token_position(token, start_x, start_y)
            
            # Draw token
            painter.setPen(QPen(token_color.darker(), 2))
            painter.setBrush(QBrush(token_color))
            painter.drawEllipse(int(token_x - 15), int(token_y - 15), 30, 30)
            
            # Draw token ID
            painter.setPen(QPen(QColor(30, 30, 40)))
            font = QFont("Segoe UI", 9, QFont.Bold)
            painter.setFont(font)
            painter.drawText(
                int(token_x - 8), int(token_y + 4),
                str(token.id)
            )
            
            # Draw inspection result for ST5 tokens
            if token.inspection_result:
                result_color = QColor(30, 30, 40)
                painter.setPen(QPen(result_color))
                painter.drawText(
                    int(token_x - 20), int(token_y + 25),
                    token.inspection_result
                )
    
    def _get_token_position(self, token: Token, start_x: int, start_y: int):
        """Calculate screen position for a token"""
        station_order = list(STATIONS.keys())
        
        if token.current_station:
            # Token is at a station
            station_idx = station_order.index(token.current_station)
            station_x = start_x + station_idx * self.station_spacing + self.station_width // 2
            station_y = start_y + self.station_height // 2
            return station_x, station_y
        elif token.target_station:
            # Token is moving between stations
            # Find source station (previous in line)
            target_idx = station_order.index(token.target_station)
            source_idx = max(0, target_idx - 1)
            
            source_x = start_x + source_idx * self.station_spacing + self.station_width
            target_x = start_x + target_idx * self.station_spacing
            
            # Interpolate position
            token_x = source_x + (target_x - source_x) * token.position
            token_y = start_y + self.station_height // 2
            return token_x, token_y
        
        # Default position (shouldn't happen)
        return start_x, start_y
    
    def _draw_statistics(self, painter: QPainter, width: int, height: int):
        """Draw pipeline statistics"""
        stats_y = height - 30
        
        # Count tokens by state
        tokens_by_state = collections.defaultdict(int)
        for token in self.tokens:
            tokens_by_state[token.state] += 1
        
        # Calculate throughput
        completed_tokens = tokens_by_state[TokenState.COMPLETE]
        failed_tokens = tokens_by_state[TokenState.FAIL]
        total_processed = completed_tokens + failed_tokens
        
        # Draw statistics box
        painter.setPen(QPen(QColor(80, 80, 100), 1))
        painter.setBrush(QBrush(QColor(40, 40, 50, 200)))
        painter.drawRoundedRect(10, stats_y - 25, 250, 40, 5, 5)
        
        # Draw stats text
        painter.setPen(QPen(self.colors['text']))
        font = QFont("Segoe UI", 9)
        painter.setFont(font)
        
        stats_text = f"Tokens: {len(self.tokens)} | Complete: {completed_tokens}"
        if failed_tokens > 0:
            stats_text += f" | Reject: {failed_tokens}"
        
        painter.drawText(20, stats_y, stats_text)

# ===== MAIN WINDOW =====
class MainWindow(QMainWindow):
    def __init__(self):
        super().__init__()
        self.setWindowTitle("Production Line Visualizer - ST1→ST6 Pipeline (Auto-Launch Stations)")
        self.setGeometry(100, 100, 1600, 900)
        
        # Data
        self.log_paths = {}  # station_id -> path
        self.replay_events = []  # Merged events from all stations
        self.replay_timestamps = []  # Fast lookup
        self.replay_min_time = 0
        self.replay_max_time = 0
        self.current_time_ns = 0
        self.is_live_mode = True
        self.is_playing = True
        self.playback_speed = 1.0
        
        # Statistics
        self.raw_event_counts = collections.defaultdict(int)
        self.accepted_event_counts = collections.defaultdict(int)
        self.last_activity_times = collections.defaultdict(float)
        self.is_idle = False
        self.idle_start_time = 0.0
        
        # Workers and parsers
        self.tail_workers = {}  # station_id -> LogTailWorker
        self.station_parsers = {st_id: StationLogParser(st_id) for st_id in STATIONS.keys()}
        self.last_state_snapshots = {}  # station_id -> state dict
        
        # Station Process Manager
        self.process_manager = StationProcessManager(self)
        
        # UI
        self.init_ui()
        
        # Timer for animation and replay
        self.timer = QTimer()
        self.timer.timeout.connect(self.update_animation)
        self.timer.start(1000 // TIMER_FPS)
        
        # Connect process manager signals
        self.process_manager.process_state_changed.connect(self.update_station_status_label)
        
        # Initial log discovery
        self.discover_logs()
        
        # Auto-start all station visualizers after a short delay
        QTimer.singleShot(1000, self.start_all_stations)
    
    def init_ui(self):
        """Initialize the user interface"""
        central_widget = QWidget()
        self.setCentralWidget(central_widget)
        
        main_layout = QVBoxLayout(central_widget)
        main_layout.setSpacing(10)
        main_layout.setContentsMargins(12, 12, 12, 12)
        
        # ===== HEADER BAR =====
        header_frame = QFrame()
        header_frame.setObjectName("headerFrame")
        header_layout = QHBoxLayout(header_frame)
        header_layout.setContentsMargins(15, 10, 15, 10)
        
        # Title
        title_label = QLabel("Production Line Visualizer - ST1→ST6 Pipeline")
        title_font = QFont("Segoe UI", 14, QFont.Bold)
        title_label.setFont(title_font)
        title_label.setStyleSheet("color: #ffffff;")
        header_layout.addWidget(title_label)
        
        header_layout.addSpacing(20)
        
        # Mode badge
        self.mode_badge = QLabel("LIVE")
        self.mode_badge.setFont(QFont("Segoe UI", 10, QFont.Bold))
        self.mode_badge.setAlignment(Qt.AlignCenter)
        self.mode_badge.setMinimumWidth(80)
        self.mode_badge.setStyleSheet("""
            QLabel {
                background-color: #2e7d32;
                color: white;
                padding: 4px 12px;
                border-radius: 12px;
                border: 1px solid #1b5e20;
            }
        """)
        header_layout.addWidget(self.mode_badge)
        
        header_layout.addSpacing(20)
        
        # Station status
        self.station_status_label = QLabel("Stations: 0/6 found")
        self.station_status_label.setFont(QFont("Segoe UI", 9))
        self.station_status_label.setStyleSheet("color: #cccccc;")
        header_layout.addWidget(self.station_status_label)
        
        # Station process status
        self.station_process_label = QLabel("Station UIs: Not started")
        self.station_process_label.setFont(QFont("Segoe UI", 9))
        self.station_process_label.setStyleSheet("color: #cccccc;")
        header_layout.addWidget(self.station_process_label)
        
        header_layout.addSpacing(20)
        
        # Idle status
        self.idle_status_label = QLabel("ACTIVE")
        self.idle_status_label.setFont(QFont("Segoe UI", 10, QFont.Bold))
        self.idle_status_label.setAlignment(Qt.AlignCenter)
        self.idle_status_label.setMinimumWidth(100)
        self.idle_status_label.setStyleSheet("""
            QLabel {
                background-color: #2e7d32;
                color: white;
                padding: 4px 12px;
                border-radius: 12px;
                border: 1px solid #1b5e20;
            }
        """)
        header_layout.addWidget(self.idle_status_label)
        
        header_layout.addStretch()
        
        # Event stats
        self.event_stats_label = QLabel("Events: 0 total")
        self.event_stats_label.setFont(QFont("Segoe UI", 9))
        self.event_stats_label.setStyleSheet("color: #cccccc;")
        header_layout.addWidget(self.event_stats_label)
        
        header_layout.addSpacing(20)
        
        # Station control buttons
        self.start_stations_button = QPushButton("▶ Start Stations")
        self.start_stations_button.setFont(QFont("Segoe UI", 9))
        self.start_stations_button.clicked.connect(self.start_all_stations)
        header_layout.addWidget(self.start_stations_button)
        
        self.stop_stations_button = QPushButton("⏹ Stop Stations")
        self.stop_stations_button.setFont(QFont("Segoe UI", 9))
        self.stop_stations_button.clicked.connect(self.stop_all_stations)
        header_layout.addWidget(self.stop_stations_button)
        
        self.restart_stations_button = QPushButton("↻ Restart Stations")
        self.restart_stations_button.setFont(QFont("Segoe UI", 9))
        self.restart_stations_button.clicked.connect(self.restart_all_stations)
        header_layout.addWidget(self.restart_stations_button)
        
        header_layout.addSpacing(10)
        
        # Reload button
        self.reload_button = QPushButton("🔄 Reload Logs")
        self.reload_button.setFont(QFont("Segoe UI", 9))
        self.reload_button.clicked.connect(self.discover_logs)
        header_layout.addWidget(self.reload_button)
        
        main_layout.addWidget(header_frame)
        
        # ===== PIPELINE VISUALIZATION =====
        self.pipeline_widget = PipelineWidget()
        main_layout.addWidget(self.pipeline_widget, 1)
        
        # ===== CONTROL BAR =====
        controls_frame = QFrame()
        controls_frame.setObjectName("controlsFrame")
        controls_frame.setMinimumHeight(70)
        controls_layout = QHBoxLayout(controls_frame)
        controls_layout.setContentsMargins(20, 10, 20, 10)
        
        # Live toggle
        self.live_toggle = QCheckBox("LIVE Mode")
        self.live_toggle.setChecked(True)
        self.live_toggle.stateChanged.connect(self.on_live_toggled)
        controls_layout.addWidget(self.live_toggle)
        
        controls_layout.addSpacing(30)
        
        # Playback controls
        self.play_button = QPushButton("⏸ Pause")
        self.play_button.clicked.connect(self.toggle_play)
        self.play_button.setEnabled(False)
        controls_layout.addWidget(self.play_button)
        
        controls_layout.addWidget(QLabel("Speed:"))
        self.speed_combo = QComboBox()
        self.speed_combo.addItems(["0.25x", "0.5x", "1x", "2x", "4x", "8x"])
        self.speed_combo.setCurrentIndex(2)
        self.speed_combo.currentIndexChanged.connect(self.on_speed_changed)
        self.speed_combo.setEnabled(False)
        controls_layout.addWidget(self.speed_combo)
        
        controls_layout.addSpacing(30)
        
        # Timeline slider
        controls_layout.addWidget(QLabel("Timeline:"))
        self.timeline_slider = QSlider(Qt.Horizontal)
        self.timeline_slider.setEnabled(False)
        self.timeline_slider.setMinimum(0)
        self.timeline_slider.setMaximum(1000)
        self.timeline_slider.valueChanged.connect(self.on_timeline_changed)
        controls_layout.addWidget(self.timeline_slider, 2)
        
        # Time display
        self.time_label = QLabel("LIVE")
        self.time_label.setFont(QFont("Segoe UI", 10, QFont.Bold))
        controls_layout.addWidget(self.time_label)
        
        main_layout.addWidget(controls_frame)
    
    def start_all_stations(self):
        """Start all station visualizer processes"""
        print("Starting all station visualizers...")
        self.process_manager.start_all_stations()
    
    def stop_all_stations(self):
        """Stop all station visualizer processes"""
        print("Stopping all station visualizers...")
        self.process_manager.stop_all_stations()
    
    def restart_all_stations(self):
        """Restart all station visualizer processes"""
        print("Restarting all station visualizers...")
        self.process_manager.restart_all_stations()
    
    def update_station_status_label(self):
        """Update the station process status label"""
        status = self.process_manager.get_status_summary()
        self.station_process_label.setText(status)
    
    def discover_logs(self):
        """Discover log files for all stations"""
        # Stop existing workers
        self._stop_all_workers()
        
        # Find logs
        self.log_paths = LogDiscoverer.find_station_logs()
        
        # Update UI
        station_count = sum(1 for st_id in STATIONS.keys() if st_id in self.log_paths)
        self.station_status_label.setText(f"Stations: {station_count}/6 found")
        
        if station_count == 0:
            self.event_stats_label.setText("Events: 0 total - No logs found")
            return
        
        # Reset statistics
        self.raw_event_counts.clear()
        self.accepted_event_counts.clear()
        self.update_event_stats()
        
        if self.is_live_mode:
            self.switch_to_live()
        else:
            self.switch_to_replay()
    
    def load_live_snapshot(self, station_id: str) -> Tuple[Optional[StationEvent], int]:
        """Load snapshot of last N lines from a station log"""
        if station_id not in self.log_paths:
            return None, 0
        
        log_path = self.log_paths[station_id]
        if not os.path.exists(log_path):
            return None, 0
        
        try:
            with open(log_path, 'r', encoding='utf-8', errors='ignore') as f:
                lines = collections.deque(f, maxlen=SNAPSHOT_LINES)
            
            parser = self.station_parsers[station_id]
            parser.reset()
            
            raw_count = 0
            latest_event = None
            
            for line in lines:
                event = parser.parse_line(line)
                if event:
                    raw_count += 1
                    latest_event = event
            
            if latest_event is None:
                latest_event = parser.get_current_state()
            
            return latest_event, raw_count
            
        except Exception as e:
            print(f"Error loading snapshot for {station_id}: {e}")
            return None, 0
    
    def switch_to_live(self):
        """Switch to LIVE mode (tail logs)"""
        # Stop existing workers
        self._stop_all_workers()
        
        # Clear replay data
        self.replay_events = []
        self.replay_timestamps = []
        self.current_time_ns = 0
        
        # Update UI
        self.mode_badge.setText("LIVE")
        self.mode_badge.setStyleSheet("""
            QLabel {
                background-color: #2e7d32;
                color: white;
                padding: 4px 12px;
                border-radius: 12px;
                border: 1px solid #1b5e20;
            }
        """)
        
        self.timeline_slider.setEnabled(False)
        self.speed_combo.setEnabled(False)
        self.play_button.setEnabled(False)
        self.is_playing = False
        self.play_button.setText("▶ Play")
        self.time_label.setText("LIVE")
        
        self.is_idle = False
        self.idle_start_time = 0.0
        self.update_idle_status()
        
        # Start tail workers for each found station
        for station_id in STATIONS.keys():
            if station_id in self.log_paths:
                self._start_station_worker(station_id)
        
        self.last_activity_times.clear()
        for station_id in STATIONS.keys():
            self.last_activity_times[station_id] = time.time()
    
    def _start_station_worker(self, station_id: str):
        """Start a tail worker for a specific station"""
        # Load snapshot first
        latest_event, raw_count = self.load_live_snapshot(station_id)
        self.raw_event_counts[station_id] = raw_count
        
        # Initialize state snapshot
        if latest_event:
            self.last_state_snapshots[station_id] = {
                'ready': latest_event.ready,
                'busy': latest_event.busy,
                'done': latest_event.done,
                'fault': latest_event.fault,
                'cycle_time_ms': latest_event.cycle_time_ms,
                'extra': latest_event.extra.copy()
            }
            
            # Update pipeline visualization
            self.pipeline_widget.update_station_state(latest_event)
            
            # Start worker with seeded parser
            worker = LogTailWorker(station_id, self.log_paths[station_id], latest_event)
        else:
            self.last_state_snapshots[station_id] = None
            worker = LogTailWorker(station_id, self.log_paths[station_id])
        
        # Connect signals
        worker.new_event.connect(self.process_new_event)
        worker.activity_detected.connect(self.on_activity_detected)
        worker.file_reopened.connect(self.on_file_reopened)
        
        # Start worker
        worker.start()
        self.tail_workers[station_id] = worker
    
    def switch_to_replay(self):
        """Switch to REPLAY mode (load all events)"""
        # Stop existing workers
        self._stop_all_workers()
        
        # Update UI
        self.mode_badge.setText("REPLAY")
        self.mode_badge.setStyleSheet("""
            QLabel {
                background-color: #7b1fa2;
                color: white;
                padding: 4px 12px;
                border-radius: 12px;
                border: 1px solid #6a1b9a;
            }
        """)
        
        self.timeline_slider.setEnabled(True)
        self.speed_combo.setEnabled(True)
        self.play_button.setEnabled(True)
        self.is_playing = True
        self.play_button.setText("⏸ Pause")
        self.is_idle = False
        
        # Load all events
        self.load_replay_data()
        
        # Setup timeline
        if self.replay_events:
            self.replay_min_time = self.replay_events[0].t_ns
            self.replay_max_time = self.replay_events[-1].t_ns
            self.current_time_ns = self.replay_min_time
            self.timeline_slider.setValue(0)
            self.update_time_label()
            
            # Update to initial state
            self.update_states_from_replay()
        else:
            self.time_label.setText("NO DATA")
    
    def load_replay_data(self):
        """Load and merge events from all station logs for replay"""
        all_events = []
        
        for station_id in STATIONS.keys():
            if station_id not in self.log_paths:
                continue
            
            log_path = self.log_paths[station_id]
            try:
                with open(log_path, 'r', encoding='utf-8', errors='ignore') as f:
                    lines = f.readlines()
                
                parser = StationLogParser(station_id)
                station_events = []
                
                for line in lines:
                    event = parser.parse_line(line)
                    if event:
                        station_events.append(event)
                
                # Sort and limit
                station_events.sort(key=lambda x: x.t_ns)
                station_events = station_events[-MAX_EVENTS_PER_STATION:]
                
                # Count events
                self.raw_event_counts[station_id] = len(station_events)
                
                # Count accepted events (state changes)
                self.accepted_event_counts[station_id] = 0
                last_state_snapshot = None
                
                for event in station_events:
                    new_state = {
                        'ready': event.ready,
                        'busy': event.busy,
                        'done': event.done,
                        'fault': event.fault,
                        'cycle_time_ms': event.cycle_time_ms,
                        'extra': event.extra.copy()
                    }
                    
                    if last_state_snapshot is None or self._state_changed(last_state_snapshot, new_state):
                        last_state_snapshot = new_state
                        self.accepted_event_counts[station_id] += 1
                
                all_events.extend(station_events)
                
                print(f"Loaded {len(station_events)} events for {station_id}")
                
            except Exception as e:
                print(f"Error loading {log_path}: {e}")
                continue
        
        # Merge all events by timestamp
        all_events.sort(key=lambda x: x.t_ns)
        self.replay_events = all_events[-MAX_EVENTS_PER_STATION * 6:]  # Limit total
        self.replay_timestamps = [e.t_ns for e in self.replay_events]
        
        self.update_event_stats()
        print(f"Loaded {len(self.replay_events)} total events for replay")
    
    def _state_changed(self, old_state: dict, new_state: dict) -> bool:
        """Check if state has meaningfully changed"""
        for key in ['ready', 'busy', 'done', 'fault']:
            if old_state.get(key) != new_state.get(key):
                return True
        
        old_cycle = old_state.get('cycle_time_ms')
        new_cycle = new_state.get('cycle_time_ms')
        if old_cycle is not None and new_cycle is not None:
            if abs(old_cycle - new_cycle) > 0.01:
                return True
        elif old_cycle != new_cycle:
            return True
        
        return False
    
    def process_new_event(self, event: StationEvent):
        """Process new event from a tail worker"""
        station_id = event.station_id
        
        # Update raw count
        self.raw_event_counts[station_id] = self.raw_event_counts.get(station_id, 0) + 1
        
        # Update activity time
        self.last_activity_times[station_id] = time.time()
        if self.is_idle:
            self.is_idle = False
            self.update_idle_status()
        
        # Check if state changed
        new_state = {
            'ready': event.ready,
            'busy': event.busy,
            'done': event.done,
            'fault': event.fault,
            'cycle_time_ms': event.cycle_time_ms,
            'extra': event.extra.copy()
        }
        
        prev_state = self.last_state_snapshots.get(station_id)
        
        if prev_state is None or self._state_changed(prev_state, new_state):
            # State changed
            self.accepted_event_counts[station_id] = self.accepted_event_counts.get(station_id, 0) + 1
            self.last_state_snapshots[station_id] = new_state
            
            # Update pipeline visualization
            self.pipeline_widget.update_station_state(event)
            
            self.update_event_stats()
    
    def on_activity_detected(self, station_id: str):
        """Handle activity detection from a station"""
        self.last_activity_times[station_id] = time.time()
        if self.is_idle:
            self.is_idle = False
            self.update_idle_status()
    
    def on_file_reopened(self, station_id: str):
        """Handle file reopening for a station"""
        if not self.is_live_mode:
            return
        
        # Reload snapshot and reseed parser
        latest_event, _ = self.load_live_snapshot(station_id)
        if latest_event and station_id in self.tail_workers:
            worker = self.tail_workers[station_id]
            worker.reseed_parser(latest_event)
            
            # Update pipeline
            self.pipeline_widget.update_station_state(latest_event)
    
    def update_states_from_replay(self):
        """Update states based on current replay time"""
        if not self.replay_events:
            return
        
        # Find events at or before current time
        idx = bisect.bisect_right(self.replay_timestamps, self.current_time_ns) - 1
        if idx < 0:
            return
        
        # Get all events at this timestamp
        current_time = self.replay_timestamps[idx]
        events_at_time = []
        
        # Find all events with this timestamp
        search_idx = idx
        while search_idx >= 0 and self.replay_timestamps[search_idx] == current_time:
            events_at_time.append(self.replay_events[search_idx])
            search_idx -= 1
        
        # Also check forward in case of duplicate timestamps
        search_idx = idx + 1
        while search_idx < len(self.replay_timestamps) and self.replay_timestamps[search_idx] == current_time:
            events_at_time.append(self.replay_events[search_idx])
            search_idx += 1
        
        # Apply events to pipeline
        for event in events_at_time:
            self.pipeline_widget.update_station_state(event)
    
    def update_animation(self):
        """Update animation based on timer"""
        # Update token animation
        time_delta = 1.0 / TIMER_FPS
        self.pipeline_widget.update_tokens_animation(time_delta)
        
        if self.is_playing and not self.is_live_mode and self.replay_events:
            # Advance replay time
            time_delta_ns = int(33_333_333 * self.playback_speed)  # ~30 FPS
            self.current_time_ns += time_delta_ns
            
            # Check bounds
            if self.current_time_ns > self.replay_max_time:
                self.current_time_ns = self.replay_max_time
                self.is_playing = False
                self.play_button.setText("▶ Play")
            
            # Update slider
            time_range = self.replay_max_time - self.replay_min_time
            if time_range > 0:
                slider_value = int((self.current_time_ns - self.replay_min_time) * 1000 / time_range)
                self.timeline_slider.blockSignals(True)
                self.timeline_slider.setValue(slider_value)
                self.timeline_slider.blockSignals(False)
            
            self.update_states_from_replay()
            self.update_time_label()
        
        # Check for idle in LIVE mode
        if self.is_live_mode and not self.is_idle:
            # Check if any station has been active recently
            now = time.time()
            recent_activity = False
            for station_id in self.last_activity_times:
                if now - self.last_activity_times.get(station_id, 0) < IDLE_TIMEOUT:
                    recent_activity = True
                    break
            
            if not recent_activity:
                self.is_idle = True
                self.idle_start_time = now
                self.update_idle_status()
                self.update_time_label()
        
        elif self.is_live_mode and self.is_idle:
            # Update time label with idle status
            self.update_time_label()
    
    def update_event_stats(self):
        """Update event statistics label"""
        total_raw = sum(self.raw_event_counts.values())
        total_accepted = sum(self.accepted_event_counts.values())
        self.event_stats_label.setText(f"Events: {total_raw} raw / {total_accepted} accepted")
    
    def update_idle_status(self):
        """Update idle status indicator"""
        if self.is_idle:
            idle_time = time.time() - self.idle_start_time
            if idle_time > LONG_IDLE_TIMEOUT:
                self.idle_status_label.setText("STOPPED?")
                self.idle_status_label.setStyleSheet("""
                    QLabel {
                        background-color: #f57c00;
                        color: white;
                        padding: 4px 12px;
                        border-radius: 12px;
                        border: 1px solid #e65100;
                    }
                """)
            else:
                self.idle_status_label.setText("IDLE")
                self.idle_status_label.setStyleSheet("""
                    QLabel {
                        background-color: #ff8f00;
                        color: white;
                        padding: 4px 12px;
                        border-radius: 12px;
                        border: 1px solid #ef6c00;
                    }
                """)
        else:
            self.idle_status_label.setText("ACTIVE")
            self.idle_status_label.setStyleSheet("""
                QLabel {
                    background-color: #2e7d32;
                    color: white;
                    padding: 4px 12px;
                    border-radius: 12px;
                    border: 1px solid #1b5e20;
                }
            """)
    
    def update_time_label(self):
        """Update time display label"""
        if self.is_live_mode:
            if self.is_idle:
                idle_time = time.time() - self.idle_start_time
                if idle_time > LONG_IDLE_TIMEOUT:
                    self.time_label.setText("LIVE (STOPPED?)")
                else:
                    self.time_label.setText("LIVE (IDLE)")
            else:
                self.time_label.setText("LIVE")
        else:
            # Show replay time
            if self.replay_events:
                time_s = (self.current_time_ns - self.replay_min_time) / 1e9
                total_s = (self.replay_max_time - self.replay_min_time) / 1e9
                self.time_label.setText(f"{time_s:07.3f}s / {total_s:07.3f}s")
            else:
                self.time_label.setText("NO DATA")
    
    def on_live_toggled(self, state):
        """Handle LIVE mode toggle"""
        self.is_live_mode = state == Qt.Checked
        
        if self.is_live_mode:
            self.switch_to_live()
        else:
            self.switch_to_replay()
    
    def toggle_play(self):
        """Toggle play/pause in REPLAY mode"""
        if not self.is_live_mode:
            self.is_playing = not self.is_playing
            self.play_button.setText("▶ Play" if not self.is_playing else "⏸ Pause")
    
    def on_speed_changed(self, index):
        """Handle playback speed change"""
        speeds = [0.25, 0.5, 1.0, 2.0, 4.0, 8.0]
        self.playback_speed = speeds[index]
    
    def on_timeline_changed(self, value):
        """Handle timeline slider change"""
        if not self.replay_events or self.is_live_mode:
            return
        
        time_range = self.replay_max_time - self.replay_min_time
        if time_range > 0:
            self.current_time_ns = self.replay_min_time + int(time_range * value / 1000)
            self.update_states_from_replay()
            self.update_time_label()
    
    def _stop_all_workers(self):
        """Stop all tail workers"""
        for station_id, worker in list(self.tail_workers.items()):
            worker.stop()
            worker.wait()
        self.tail_workers.clear()
    
    def closeEvent(self, event):
        """Cleanup on close"""
        # Stop all station processes
        print("Shutting down station processes...")
        self.process_manager.stop_all_stations()
        
        # Stop all tail workers
        self._stop_all_workers()
        
        event.accept()

# ===== MAIN APPLICATION =====
def main():
    app = QApplication(sys.argv)
    
    # Apply dark theme
    app.setStyleSheet("""
        /* Global styles */
        QWidget {
            background-color: #1e1e2e;
            color: #e0e0e0;
            font-family: 'Segoe UI', 'Arial', sans-serif;
            font-size: 10pt;
            selection-background-color: #3d5afe;
        }
        
        /* Frames */
        QFrame#headerFrame, QFrame#controlsFrame {
            background-color: #252535;
            border-radius: 8px;
            border: 1px solid #333344;
        }
        
        /* Labels */
        QLabel {
            color: #e0e0e0;
        }
        
        /* Buttons */
        QPushButton {
            background-color: #424242;
            color: #e0e0e0;
            padding: 6px 12px;
            border-radius: 4px;
            border: 1px solid #555;
            font-weight: bold;
        }
        
        QPushButton:hover {
            background-color: #4a4a4a;
            border: 1px solid #666;
        }
        
        QPushButton:pressed {
            background-color: #3a3a3a;
        }
        
        QPushButton:disabled {
            background-color: #333;
            color: #666;
        }
        
        /* Checkboxes */
        QCheckBox {
            spacing: 8px;
        }
        
        QCheckBox::indicator {
            width: 18px;
            height: 18px;
            border-radius: 3px;
            border: 2px solid #555;
            background-color: #333;
        }
        
        QCheckBox::indicator:checked {
            background-color: #2e7d32;
            border-color: #4caf50;
        }
        
        QCheckBox::indicator:hover {
            border-color: #666;
        }
        
        /* Combo boxes */
        QComboBox {
            background-color: #2a2a3a;
            color: #e0e0e0;
            border: 1px solid #444;
            border-radius: 4px;
            padding: 6px 12px;
            min-width: 80px;
        }
        
        QComboBox:hover {
            border-color: #555;
        }
        
        QComboBox::drop-down {
            border: none;
            width: 20px;
        }
        
        QComboBox::down-arrow {
            image: none;
            border-left: 5px solid transparent;
            border-right: 5px solid transparent;
            border-top: 6px solid #aaa;
            width: 0;
            height: 0;
            margin-right: 8px;
        }
        
        QComboBox QAbstractItemView {
            background-color: #2a2a3a;
            color: #e0e0e0;
            border: 1px solid #444;
        }
        
        /* Sliders */
        QSlider::groove:horizontal {
            background-color: #2a2a3a;
            height: 8px;
            border-radius: 4px;
            border: 1px solid #444;
        }
        
        QSlider::sub-page:horizontal {
            background-color: qlineargradient(
                x1:0, y1:0, x2:1, y2:0,
                stop:0 #4db6ac,
                stop:1 #29b6f6
            );
            height: 8px;
            border-radius: 4px;
        }
        
        QSlider::handle:horizontal {
            background-color: #bb86fc;
            width: 18px;
            height: 18px;
            margin: -6px 0;
            border-radius: 9px;
            border: 2px solid #ffffff;
        }
        
        QSlider::handle:horizontal:hover {
            background-color: #d0bfff;
            width: 20px;
            height: 20px;
            border-radius: 10px;
        }
        
        /* Tooltips */
        QToolTip {
            background-color: #252535;
            color: #e0e0e0;
            border: 1px solid #444;
            border-radius: 4px;
            padding: 6px;
        }
    """)
    
    window = MainWindow()
    window.show()
    
    sys.exit(app.exec())

if __name__ == "__main__":
    main()