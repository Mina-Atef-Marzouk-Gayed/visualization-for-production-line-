#!/usr/bin/env python3
"""
Professional Production Line KPI Dashboard
==========================================

Features:
- LIVE mode: Tail log files in real-time
- REPLAY mode: Timeline scrub through historical data
- Embedded charts with dark theme (Plotly-WebEngine OR QtCharts fallback)
- Professional UI with animations
- Multi-threaded parsing for smooth performance
- Recursive log file discovery

Chart Backend Priority:
1. Plotly with PySide6-WebEngine (if available)
2. PySide6.QtCharts (fallback, included with PySide6)
3. Matplotlib (last resort, requires pip install matplotlib)

Requirements:
- PySide6 (always)
- plotly (always)
- pandas (always)
- numpy (always)
- matplotlib (only needed if both WebEngine and QtCharts are unavailable)

Run:
    python3 kpi_dashboard.py

Logs should be placed in current directory or subdirectories with names:
    check.PLC_LineCoordinator.log
    check.ST1_*.log
    check.ST2_*.log
    ... etc.

Author: DeepSeek (Senior Qt/Python Engineer)
Version: 1.3 - With WebEngine Fallback Support
"""

import sys
import os
import re
import time
import math
import json
import traceback
import collections
import copy
import bisect
import threading
from typing import *
from dataclasses import dataclass, field
from datetime import datetime, timedelta
from enum import Enum
from collections import deque
from matplotlib import pyplot as plt
import numpy as np
import pandas as pd

# ===== QT IMPORTS =====
try:
    from PySide6.QtWidgets import *
    from PySide6.QtCore import *
    from PySide6.QtGui import *
    QT_AVAILABLE = True
except Exception as e:
    print(f"ERROR importing PySide6: {e}")
    print("\nInstall requirements:")
    print("  pip install PySide6")
    sys.exit(1)

# ===== DETECT CHART BACKENDS =====
# Try WebEngine first
try:
    from PySide6.QtWebEngineWidgets import QWebEngineView
    from PySide6.QtWebEngineCore import QWebEngineSettings, QWebEnginePage
    WEBENGINE_AVAILABLE = True
except ImportError:
    WEBENGINE_AVAILABLE = False

# Try QtCharts next (included with PySide6)
try:
    from PySide6.QtCharts import (
        QChart, QChartView, QLineSeries, QBarSeries, QBarSet,
        QPieSeries, QValueAxis, QBarCategoryAxis, QCategoryAxis,
        QLegend, QAreaSeries, QSplineSeries, QScatterSeries
    )
    QTCHARTS_AVAILABLE = True
except ImportError:
    QTCHARTS_AVAILABLE = False

# Try matplotlib as last resort
try:
    import matplotlib
    # Use Qt5Agg backend for PySide6 compatibility
    matplotlib.use('Qt5Agg')
    from matplotlib.backends.backend_qt5agg import FigureCanvasQTAgg
    from matplotlib.figure import Figure
    from matplotlib.patches import Wedge, Circle
    MATPLOTLIB_AVAILABLE = True
except ImportError:
    MATPLOTLIB_AVAILABLE = False

# ===== PLOTLY IMPORT =====
try:
    import plotly
    import plotly.graph_objects as go
    import plotly.io as pio
    PLOTLY_AVAILABLE = True
except ImportError as e:
    print(f"ERROR importing plotly: {e}")
    print("\nInstall plotly with: pip install plotly")
    sys.exit(1)

# Determine chart backend
if WEBENGINE_AVAILABLE:
    CHART_BACKEND = "plotly_webengine"
    print("Chart backend: Plotly with WebEngine")
elif QTCHARTS_AVAILABLE:
    CHART_BACKEND = "qtcharts"
    print("Chart backend: QtCharts (fallback)")
elif MATPLOTLIB_AVAILABLE:
    CHART_BACKEND = "matplotlib"
    print("Chart backend: Matplotlib (fallback)")
else:
    CHART_BACKEND = "simple"
    print("Chart backend: Simple QPainter (minimal fallback)")

# ===== CONFIGURATION =====
SEARCH_ROOT = "."
MAX_EVENTS_PER_STATION = 50000
UI_REFRESH_FPS = 20
CHART_REFRESH_FPS = 2
SNAPSHOT_LINES = 3000
IDLE_TIMEOUT = 5.0
CHART_POINT_LIMIT = 1000
CYCLE_TIME_WINDOW = 50  # Last N cycles for trend
DONE_LATCH_MS = 300  # Show DONE state for 300ms after pulse
WIP_TRANSITION_WINDOW_MS = 2000  # Consider part in transition for 2s after DONE

# Station configuration
STATIONS = {
    "ST1": {"name": "ST1 - Loading", "color": "#4FC3F7", "icon": "📦"},
    "ST2": {"name": "ST2 - Assembly", "color": "#29B6F6", "icon": "🔧"},
    "ST3": {"name": "ST3 - Testing", "color": "#0288D1", "icon": "🧪"},
    "ST4": {"name": "ST4 - Calibration", "color": "#0277BD", "icon": "🎚️"},
    "ST5": {"name": "ST5 - Quality", "color": "#01579B", "icon": "✓"},
    "ST6": {"name": "ST6 - Packaging", "color": "#039BE5", "icon": "📦"},
}

# Chart colors for fallback
CHART_COLORS = {
    'background': QColor(30, 30, 40),
    'grid': QColor(80, 80, 100, 128),
    'text': QColor(224, 224, 224),
    'axis': QColor(100, 100, 120),
    'series': [
        QColor(79, 195, 247),   # Blue
        QColor(255, 152, 0),    # Orange
        QColor(76, 175, 80),    # Green
        QColor(244, 67, 54),    # Red
        QColor(156, 39, 176),   # Purple
        QColor(255, 235, 59),   # Yellow
    ]
}

# ===== DATA MODELS =====
class StationState(Enum):
    READY = "ready"
    BUSY = "busy"
    DONE = "done"
    FAULT = "fault"
    IDLE = "idle"

@dataclass
class StationEvent:
    """Parsed event from station log"""
    t_ns: int
    station_id: str
    ready: bool = False
    busy: bool = False
    done: bool = False
    fault: bool = False
    cycle_time_ms: Optional[float] = None
    extra: Dict[str, Any] = field(default_factory=dict)
    
    def to_dict(self):
        """Convert to dictionary for serialization"""
        return {
            't_ns': self.t_ns,
            'station_id': self.station_id,
            'ready': self.ready,
            'busy': self.busy,
            'done': self.done,
            'fault': self.fault,
            'cycle_time_ms': self.cycle_time_ms,
            'extra': self.extra
        }

@dataclass
class KpiSnapshot:
    """Snapshot of KPIs at a point in time"""
    timestamp_ns: int
    timestamp_s: float
    
    # Line-level KPIs
    throughput_ph: float = 0.0  # parts per hour
    throughput_pm: float = 0.0  # parts per minute
    wip: int = 0  # work in progress
    total_completed: int = 0
    total_rejected: int = 0
    availability: float = 0.0  # percentage
    utilization: float = 0.0   # percentage
    bottleneck_station: str = ""
    avg_cycle_times: Dict[str, float] = field(default_factory=dict)
    
    # Per-station KPIs
    station_states: Dict[str, str] = field(default_factory=dict)
    station_utilization: Dict[str, float] = field(default_factory=dict)
    station_availability: Dict[str, float] = field(default_factory=dict)
    station_fault_count: Dict[str, int] = field(default_factory=dict)
    station_extra_fields: Dict[str, Dict[str, Any]] = field(default_factory=dict)
    
    def to_dict(self):
        """Convert to dictionary for UI display"""
        return {
            'timestamp': self.timestamp_s,
            'throughput_ph': self.throughput_ph,
            'throughput_pm': self.throughput_pm,
            'wip': self.wip,
            'total_completed': self.total_completed,
            'total_rejected': self.total_rejected,
            'availability': self.availability,
            'utilization': self.utilization,
            'bottleneck_station': self.bottleneck_station,
            'avg_cycle_times': self.avg_cycle_times,
            'station_states': self.station_states,
            'station_utilization': self.station_utilization,
            'station_availability': self.station_availability,
            'station_fault_count': self.station_fault_count,
            'station_extra_fields': self.station_extra_fields
        }

# ===== PARSER MODULE =====
class StationLogParser:
    """Carry-forward parser for station logs"""
    
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
        self.key_value_pattern = re.compile(r"(\w+)[_\s]*[:=]\s*([\w.-]+)")
        
        # State patterns
        self.state_patterns = {
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
        for state_name, pattern in self.state_patterns.items():
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
    activity_detected = Signal(str)
    file_reopened = Signal(str)
    
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

# ===== KPI CALCULATOR =====
class KpiCalculator(QObject):
    """Calculates KPIs from station events"""
    
    kpis_updated = Signal(KpiSnapshot)  # Emitted when KPIs are calculated
    
    def __init__(self):
        super().__init__()
        # Thread-safe data structures
        self.lock = threading.RLock()
        self.reset()
        
    def reset(self):
        """Reset all KPI calculations"""
        with self.lock:
            self.station_states = {st_id: {
                'ready': False,
                'busy': False,
                'done': False,
                'fault': False,
                'last_change_time': 0,
                'busy_start_time': 0,
                'total_busy_time': 0,
                'total_fault_time': 0,
                'last_activity': 0,
                'cycle_times': deque(maxlen=CYCLE_TIME_WINDOW),
                'fault_count': 0,
                'done_count': 0,
                'reject_count': 0,
                'extra_fields': {},
                'last_done_time': 0,  # For DONE latching
                'last_transition_time': 0,  # For WIP estimation
                'last_accept_state': 1,  # Track last accept state for ST5
                'last_done_pulse_time': 0,  # Track last done pulse for reject counting
            } for st_id in STATIONS.keys()}
            
            self.total_completed = 0
            self.total_rejected = 0
            self.start_time_ns = 0
            self.last_kpi_time_ns = 0
    
    def process_event(self, event: StationEvent):
        """Process a new event and update KPIs"""
        with self.lock:
            station_id = event.station_id
            if station_id not in self.station_states:
                return
            
            station = self.station_states[station_id]
            current_time_ns = event.t_ns
            
            # Update start time if first event
            if self.start_time_ns == 0:
                self.start_time_ns = current_time_ns
            
            # Track state changes
            old_busy = station['busy']
            old_fault = station['fault']
            
            # Update station state
            station['ready'] = event.ready
            station['busy'] = event.busy
            station['done'] = event.done
            station['fault'] = event.fault
            station['last_activity'] = current_time_ns
            
            # Track DONE events for latching
            if event.done:
                station['last_done_time'] = current_time_ns
                station['last_done_pulse_time'] = current_time_ns
            
            # Track any state change for WIP estimation
            if event.ready or event.busy or event.done or event.fault:
                station['last_transition_time'] = current_time_ns
            
            # Update cycle time
            if event.cycle_time_ms:
                station['cycle_times'].append(event.cycle_time_ms)
            
            # Update extra fields and track accept state for ST5
            if event.extra:
                station['extra_fields'].update(event.extra)
                if station_id == "ST5":
                    last_accept = event.extra.get('last_accept', station['last_accept_state'])
                    station['last_accept_state'] = last_accept
            
            # Track busy time
            if event.busy and not old_busy:
                station['busy_start_time'] = current_time_ns
            elif not event.busy and old_busy:
                if station['busy_start_time'] > 0:
                    busy_duration = current_time_ns - station['busy_start_time']
                    station['total_busy_time'] += busy_duration
                    station['busy_start_time'] = 0
            
            # Track fault time
            if event.fault and not old_fault:
                # Count faults
                station['fault_count'] += 1
            elif not event.fault and old_fault:
                # Fault cleared
                pass
            
            # Track completion events - ST6 DONE counts as completed
            if event.done and station_id == "ST6":
                station['done_count'] += 1
                self.total_completed += 1
            
            # Track reject events - ST5 with DONE pulse and last_accept=0
            # Only count on DONE pulse transition when last_accept == 0
            if (station_id == "ST5" and event.done and 
                station['last_accept_state'] == 0 and
                station['last_done_pulse_time'] == current_time_ns):
                station['reject_count'] += 1
                self.total_rejected += 1
            
            # Calculate and emit KPIs
            self.calculate_kpis(current_time_ns)
    
    def calculate_kpis(self, current_time_ns: int):
        """Calculate all KPIs at current time"""
        with self.lock:
            if self.start_time_ns == 0:
                return
            
            elapsed_time_ns = current_time_ns - self.start_time_ns
            elapsed_time_hours = elapsed_time_ns / (1e9 * 3600)
            elapsed_time_minutes = elapsed_time_ns / (1e9 * 60)
            
            # Calculate throughput
            throughput_ph = self.total_completed / elapsed_time_hours if elapsed_time_hours > 0 else 0
            throughput_pm = self.total_completed / elapsed_time_minutes if elapsed_time_minutes > 0 else 0
            
            # Calculate WIP - enhanced estimation
            wip = 0
            transition_wip = 0
            done_latch_ns = DONE_LATCH_MS * 1_000_000
            transition_window_ns = WIP_TRANSITION_WINDOW_MS * 1_000_000
            
            for station_id, station in self.station_states.items():
                # Count busy stations
                if station['busy']:
                    wip += 1
                # Count stations that recently completed (in transition)
                elif (current_time_ns - station['last_transition_time']) < transition_window_ns and not station['busy']:
                    transition_wip += 0.5  # Partial credit for parts between stations
            
            wip = int(wip + transition_wip)
            
            # Calculate station cycle times
            avg_cycle_times = {}
            for station_id, station in self.station_states.items():
                if station['cycle_times']:
                    avg_cycle_times[station_id] = np.mean(station['cycle_times'])
            
            # Find bottleneck (station with longest avg cycle time)
            bottleneck_station = ""
            if avg_cycle_times:
                bottleneck_station = max(avg_cycle_times.items(), key=lambda x: x[1])[0]
            
            # Calculate utilization and availability
            total_utilization = 0
            total_availability = 0
            station_utilization = {}
            station_availability = {}
            station_states = {}
            station_fault_count = {}
            station_extra_fields = {}
            
            done_latch_ns = DONE_LATCH_MS * 1_000_000
            
            for station_id, station in self.station_states.items():
                # Station state with DONE latching - CORRECT PRIORITY: FAULT > DONE > BUSY > READY > IDLE
                if station['fault']:
                    station_states[station_id] = "FAULT"
                elif (current_time_ns - station['last_done_time']) < done_latch_ns:
                    station_states[station_id] = "DONE"
                elif station['busy']:
                    station_states[station_id] = "BUSY"
                elif station['ready']:
                    station_states[station_id] = "READY"
                else:
                    station_states[station_id] = "IDLE"
                
                # Utilization (percentage of time busy)
                if elapsed_time_ns > 0:
                    current_busy_time = station['total_busy_time']
                    if station['busy'] and station['busy_start_time'] > 0:
                        current_busy_time += (current_time_ns - station['busy_start_time'])
                    
                    utilization = (current_busy_time / elapsed_time_ns) * 100
                    station_utilization[station_id] = min(100, max(0, utilization))
                    total_utilization += utilization
                
                # Availability (percentage of time not in fault)
                if elapsed_time_ns > 0:
                    availability = 100  # Assume 100% and subtract fault time
                    station_availability[station_id] = availability
                    total_availability += availability
                
                # Fault count
                station_fault_count[station_id] = station['fault_count']
                
                # Extra fields
                station_extra_fields[station_id] = station['extra_fields']
            
            # Calculate averages
            num_stations = len(STATIONS)
            avg_utilization = total_utilization / num_stations if num_stations > 0 else 0
            avg_availability = total_availability / num_stations if num_stations > 0 else 0
            
            # Create KPI snapshot
            snapshot = KpiSnapshot(
                timestamp_ns=current_time_ns,
                timestamp_s=current_time_ns / 1e9,
                throughput_ph=throughput_ph,
                throughput_pm=throughput_pm,
                wip=wip,
                total_completed=self.total_completed,
                total_rejected=self.total_rejected,
                availability=avg_availability,
                utilization=avg_utilization,
                bottleneck_station=bottleneck_station,
                avg_cycle_times=avg_cycle_times,
                station_states=station_states,
                station_utilization=station_utilization,
                station_availability=station_availability,
                station_fault_count=station_fault_count,
                station_extra_fields=station_extra_fields
            )
            
            self.last_kpi_time_ns = current_time_ns
            
            # Emit signal (will be processed in main thread)
            self.kpis_updated.emit(snapshot)

# ===== CHART MANAGER =====
class ChartManager:
    """Manages chart generation and updates for all backends"""
    
    # Dark theme template for Plotly
    DARK_THEME = {
        'plot_bgcolor': 'rgba(30, 30, 40, 1)',
        'paper_bgcolor': 'rgba(30, 30, 40, 1)',
        'font': {'color': '#e0e0e0'},
        'xaxis': {
            'gridcolor': 'rgba(80, 80, 100, 0.5)',
            'linecolor': 'rgba(100, 100, 120, 0.8)',
            'zerolinecolor': 'rgba(100, 100, 120, 0.5)',
        },
        'yaxis': {
            'gridcolor': 'rgba(80, 80, 100, 0.5)',
            'linecolor': 'rgba(100, 100, 120, 0.8)',
            'zerolinecolor': 'rgba(100, 100, 120, 0.5)',
        }
    }
    
    @staticmethod
    def create_throughput_chart_data(time_data, throughput_data):
        """Create throughput over time chart data"""
        try:
            # For Plotly
            if CHART_BACKEND == "plotly_webengine":
                trace = {
                    'x': time_data,
                    'y': throughput_data,
                    'type': 'scatter',
                    'mode': 'lines',
                    'name': 'Throughput',
                    'line': {'color': '#4FC3F7', 'width': 2},
                    'fill': 'tozeroy',
                    'fillcolor': 'rgba(79, 195, 247, 0.2)'
                }
                
                layout = {
                    'title': 'Throughput Over Time',
                    'xaxis': {'title': 'Time'},
                    'yaxis': {'title': 'Parts per Hour'},
                    'showlegend': True,
                    'height': 400,
                    **ChartManager.DARK_THEME
                }
                
                return [trace], layout
            else:
                # For fallback backends
                return {
                    'type': 'line',
                    'x': time_data,
                    'y': throughput_data,
                    'title': 'Throughput Over Time',
                    'xlabel': 'Time',
                    'ylabel': 'Parts per Hour',
                    'color': '#4FC3F7'
                }
        except Exception as e:
            print(f"Error creating throughput chart: {e}")
            return {}, {}
    
    @staticmethod
    def create_cycle_time_chart_data(station_names, cycle_times):
        """Create cycle time comparison chart data"""
        try:
            if CHART_BACKEND == "plotly_webengine":
                colors = [STATIONS[st_id]['color'] for st_id in station_names]
                
                trace = {
                    'x': station_names,
                    'y': cycle_times,
                    'type': 'bar',
                    'name': 'Cycle Time',
                    'marker': {'color': colors},
                    'text': [f"{ct:.1f}" for ct in cycle_times],
                    'textposition': 'outside'
                }
                
                layout = {
                    'title': 'Average Cycle Time per Station',
                    'xaxis': {'title': 'Station'},
                    'yaxis': {'title': 'Cycle Time (ms)'},
                    'showlegend': False,
                    'height': 400,
                    **ChartManager.DARK_THEME
                }
                
                return [trace], layout
            else:
                # For fallback backends
                colors = [STATIONS[st_id]['color'] for st_id in station_names]
                return {
                    'type': 'bar',
                    'categories': station_names,
                    'values': cycle_times,
                    'title': 'Average Cycle Time per Station',
                    'xlabel': 'Station',
                    'ylabel': 'Cycle Time (ms)',
                    'colors': colors
                }
        except Exception as e:
            print(f"Error creating cycle time chart: {e}")
            return {}, {}
    
    @staticmethod
    def create_utilization_chart_data(station_names, utilization_data):
        """Create utilization bar chart data"""
        try:
            if CHART_BACKEND == "plotly_webengine":
                colors = ['#4CAF50' if u >= 70 else '#FFC107' if u >= 40 else '#F44336' 
                         for u in utilization_data]
                
                trace = {
                    'x': station_names,
                    'y': utilization_data,
                    'type': 'bar',
                    'name': 'Utilization',
                    'marker': {'color': colors},
                    'text': [f"{u:.1f}%" for u in utilization_data],
                    'textposition': 'outside'
                }
                
                layout = {
                    'title': 'Station Utilization',
                    'xaxis': {'title': 'Station'},
                    'yaxis': {'title': 'Utilization (%)', 'range': [0, 100]},
                    'showlegend': False,
                    'height': 400,
                    **ChartManager.DARK_THEME
                }
                
                return [trace], layout
            else:
                # For fallback backends
                colors = []
                for u in utilization_data:
                    if u >= 70:
                        colors.append('#4CAF50')  # Green
                    elif u >= 40:
                        colors.append('#FFC107')  # Yellow
                    else:
                        colors.append('#F44336')  # Red
                
                return {
                    'type': 'bar',
                    'categories': station_names,
                    'values': utilization_data,
                    'title': 'Station Utilization',
                    'xlabel': 'Station',
                    'ylabel': 'Utilization (%)',
                    'colors': colors
                }
        except Exception as e:
            print(f"Error creating utilization chart: {e}")
            return {}, {}
    
    @staticmethod
    def create_pass_reject_chart_data(passed, rejected):
        """Create pass/reject pie chart data"""
        try:
            if CHART_BACKEND == "plotly_webengine":
                labels = ['Pass', 'Reject']
                values = [passed, rejected]
                colors = ['#4CAF50', '#F44336']
                
                trace = {
                    'labels': labels,
                    'values': values,
                    'type': 'pie',
                    'hole': 0.4,
                    'marker': {'colors': colors},
                    'textinfo': 'label+percent',
                    'textposition': 'inside'
                }
                
                layout = {
                    'title': 'Pass/Reject Ratio',
                    'showlegend': True,
                    'height': 400,
                    **ChartManager.DARK_THEME
                }
                
                return [trace], layout
            else:
                # For fallback backends
                return {
                    'type': 'pie',
                    'labels': ['Pass', 'Reject'],
                    'values': [passed, rejected],
                    'title': 'Pass/Reject Ratio',
                    'colors': ['#4CAF50', '#F44336']
                }
        except Exception as e:
            print(f"Error creating pass/reject chart: {e}")
            return {}, {}
    
    @staticmethod
    def create_station_cycle_trend_data(time_data, cycle_data_dict):
        """Create station cycle time trend chart data"""
        try:
            if CHART_BACKEND == "plotly_webengine":
                traces = []
                for station_id, cycle_data in cycle_data_dict.items():
                    color = STATIONS.get(station_id, {}).get('color', '#888888')
                    trace = {
                        'x': time_data,
                        'y': cycle_data,
                        'type': 'scatter',
                        'mode': 'lines',
                        'name': station_id,
                        'line': {'color': color, 'width': 2}
                    }
                    traces.append(trace)
                
                layout = {
                    'title': 'Cycle Time Trend',
                    'xaxis': {'title': 'Time'},
                    'yaxis': {'title': 'Cycle Time (ms)'},
                    'showlegend': True,
                    'height': 400,
                    **ChartManager.DARK_THEME
                }
                
                return traces, layout
            else:
                # For fallback backends
                series = []
                for station_id, cycle_data in cycle_data_dict.items():
                    color = STATIONS.get(station_id, {}).get('color', '#888888')
                    series.append({
                        'name': station_id,
                        'x': time_data,
                        'y': cycle_data,
                        'color': color
                    })
                
                return {
                    'type': 'multiline',
                    'series': series,
                    'title': 'Cycle Time Trend',
                    'xlabel': 'Time',
                    'ylabel': 'Cycle Time (ms)'
                }
        except Exception as e:
            print(f"Error creating station cycle trend chart: {e}")
            return [], {}
    
    @staticmethod
    def create_busy_idle_chart_data(station_names, busy_percent, idle_percent):
        """Create busy/idle stacked bar chart data"""
        try:
            if CHART_BACKEND == "plotly_webengine":
                busy_trace = {
                    'x': station_names,
                    'y': busy_percent,
                    'type': 'bar',
                    'name': 'Busy',
                    'marker': {'color': '#FF9800'},
                    'text': [f"{b:.0f}%" for b in busy_percent],
                    'textposition': 'inside'
                }
                
                idle_trace = {
                    'x': station_names,
                    'y': idle_percent,
                    'type': 'bar',
                    'name': 'Idle',
                    'marker': {'color': '#2196F3'},
                    'text': [f"{i:.0f}%" for i in idle_percent],
                    'textposition': 'inside'
                }
                
                layout = {
                    'title': 'Busy/Idle Time Distribution',
                    'xaxis': {'title': 'Station'},
                    'yaxis': {'title': 'Percentage (%)', 'range': [0, 100]},
                    'barmode': 'stack',
                    'showlegend': True,
                    'height': 400,
                    **ChartManager.DARK_THEME
                }
                
                return [busy_trace, idle_trace], layout
            else:
                # For fallback backends
                return {
                    'type': 'stacked_bar',
                    'categories': station_names,
                    'series': [
                        {'name': 'Busy', 'values': busy_percent, 'color': '#FF9800'},
                        {'name': 'Idle', 'values': idle_percent, 'color': '#2196F3'}
                    ],
                    'title': 'Busy/Idle Time Distribution',
                    'xlabel': 'Station',
                    'ylabel': 'Percentage (%)'
                }
        except Exception as e:
            print(f"Error creating busy/idle chart: {e}")
            return [], {}

# ===== CHART WIDGET BASE CLASS =====
class ChartWidget(QWidget):
    """Base class for all chart widgets"""
    
    def __init__(self, parent=None):
        super().__init__(parent)
    
    def update_chart(self, data, layout=None):
        """Update chart with new data"""
        pass
    
    def clear_chart(self):
        """Clear the chart"""
        pass

# ===== WEB ENGINE PAGE WITH CONSOLE LOGGING =====
if WEBENGINE_AVAILABLE:
    class PlotlyWebEnginePage(QWebEnginePage):
        """Custom QWebEnginePage that captures JavaScript console messages"""
        
        js_console_message = Signal(str, str, int, str)  # Fixed: renamed signal
        
        def __init__(self, parent=None):
            super().__init__(parent)
        
        def javaScriptConsoleMessage(self, level, message, lineNumber, sourceID):
            """Capture JavaScript console messages and emit signal"""
            level_str = {0: "DEBUG", 1: "LOG", 2: "WARNING", 3: "ERROR"}.get(level, "UNKNOWN")
            self.js_console_message.emit(level_str, message, lineNumber, sourceID)
            
            # Also print to terminal for debugging
            print(f"JS {level_str}: {message} at line {lineNumber} in {sourceID}")

# ===== PLOTLY WIDGET WITH OFFLINE SUPPORT =====
if WEBENGINE_AVAILABLE:
    class PlotlyWidget(ChartWidget):
        """Widget for embedding Plotly charts with offline support"""
        
        def __init__(self, parent=None):
            super().__init__(parent)
            
            self.div_id = f"plotly_chart_{id(self)}"
            self.initialized = False
            
            layout = QVBoxLayout(self)
            layout.setContentsMargins(0, 0, 0, 0)
            
            # Web view for Plotly
            self.web_view = QWebEngineView()
            self.web_view.setContextMenuPolicy(Qt.NoContextMenu)
            
            # Create custom page for console logging
            self.web_page = PlotlyWebEnginePage()
            self.web_view.setPage(self.web_page)
            
            # Connect console message signal
            self.web_page.js_console_message.connect(self.on_js_console_message)
            
            # Safe WebEngine settings initialization
            settings = self.web_view.settings()
            try:
                # Try new attribute style (PySide6 >= 6.5.0)
                settings.setAttribute(QWebEngineSettings.WebAttribute.JavascriptEnabled, True)
                settings.setAttribute(QWebEngineSettings.WebAttribute.LocalStorageEnabled, True)
            except AttributeError:
                # Fallback to old attribute style
                settings.setAttribute(QWebEngineSettings.JavascriptEnabled, True)
                settings.setAttribute(QWebEngineSettings.LocalStorageEnabled, True)
            
            layout.addWidget(self.web_view)
            
            # Set initial HTML with embedded plotly.js
            self.set_base_html()
        
        def on_js_console_message(self, level, message, lineNumber, sourceID):
            """Handle JavaScript console messages"""
            # You can log these or show them in a debug panel
            pass
        
        def set_base_html(self):
            """Set base HTML with embedded plotly.js"""
            # Create base HTML with dark theme
            html = f"""
            <!DOCTYPE html>
            <html>
            <head>
                <meta charset="utf-8">
                <style>
                    body {{
                        background-color: #1e1e2e;
                        color: #e0e0e0;
                        margin: 0;
                        padding: 0;
                        font-family: 'Segoe UI', Arial, sans-serif;
                    }}
                    #plot-container {{
                        width: 100%;
                        height: 100%;
                    }}
                    #{self.div_id} {{
                        width: 100%;
                        height: 100%;
                    }}
                </style>
                <script src="https://cdn.plot.ly/plotly-2.24.1.min.js"></script>
            </head>
            <body>
                <div id="plot-container">
                    <div id="{self.div_id}"></div>
                </div>
                <script type="text/javascript">
                    // Plotly.js is loaded from CDN
                    let plotlyInitialized = false;
                    
                    function loadPlotly() {{
                        if (typeof Plotly !== 'undefined') {{
                            plotlyInitialized = true;
                            return Promise.resolve();
                        }}
                        
                        return new Promise((resolve, reject) => {{
                            // Check again after a delay
                            setTimeout(() => {{
                                if (typeof Plotly !== 'undefined') {{
                                    plotlyInitialized = true;
                                    resolve();
                                }} else {{
                                    reject("Failed to load Plotly.js");
                                }}
                            }}, 100);
                        }});
                    }}
                    
                    function updateChart(data, layout) {{
                        if (!plotlyInitialized) {{
                            loadPlotly().then(() => {{
                                Plotly.react('{self.div_id}', data, layout, {{responsive: true}});
                            }}).catch(err => {{
                                console.error("Failed to load plotly:", err);
                            }});
                        }} else {{
                            Plotly.react('{self.div_id}', data, layout, {{responsive: true}});
                        }}
                    }}
                    
                    // Initial load
                    loadPlotly().then(() => {{
                        console.log("Plotly ready for chart updates");
                    }}).catch(err => {{
                        console.error("Failed to initialize plotly:", err);
                    }});
                </script>
            </body>
            </html>
            """
            
            self.web_view.setHtml(html)
            self.initialized = True
        
        def update_chart(self, data, layout):
            """Update chart with new data using Plotly.react()"""
            if not self.initialized:
                return
            
            try:
                # Convert data and layout to JSON
                data_json = json.dumps(data, default=self._json_serializer)
                layout_json = json.dumps(layout, default=self._json_serializer)
                
                # Update chart using JavaScript
                js_code = f"updateChart({data_json}, {layout_json});"
                self.web_view.page().runJavaScript(js_code)
            except Exception as e:
                print(f"Error updating chart: {e}")
        
        def _json_serializer(self, obj):
            """Custom JSON serializer for numpy types"""
            if isinstance(obj, np.integer):
                return int(obj)
            elif isinstance(obj, np.floating):
                return float(obj)
            elif isinstance(obj, np.ndarray):
                return obj.tolist()
            elif isinstance(obj, (datetime, timedelta)):
                return str(obj)
            raise TypeError(f"Type {type(obj)} not serializable")

# ===== QTCHARTS WIDGET =====
if QTCHARTS_AVAILABLE:
    class QtChartsWidget(ChartWidget):
        """Widget using QtCharts for rendering"""
        
        def __init__(self, parent=None):
            super().__init__(parent)
            self.chart = None
            self.chart_view = None
            self.init_ui()
        
        def init_ui(self):
            """Initialize the UI"""
            layout = QVBoxLayout(self)
            layout.setContentsMargins(0, 0, 0, 0)
            
            # Create chart view
            self.chart = QChart()
            self.chart.setBackgroundBrush(QBrush(CHART_COLORS['background']))
            self.chart.setTitleBrush(QBrush(CHART_COLORS['text']))
            self.chart.setAnimationOptions(QChart.SeriesAnimations)
            
            # Create chart view
            self.chart_view = QChartView(self.chart)
            self.chart_view.setRenderHint(QPainter.Antialiasing)
            self.chart_view.setRubberBand(QChartView.RectangleRubberBand)
            
            layout.addWidget(self.chart_view)
        
        def update_chart(self, data, layout=None):
            """Update chart with new data"""
            if not data:
                return
            
            try:
                # Clear existing series
                self.chart.removeAllSeries()
                self.chart.removeAxis(self.chart.axisX())
                self.chart.removeAxis(self.chart.axisY())
                
                chart_type = data.get('type', '')
                
                if chart_type == 'line':
                    self._update_line_chart(data)
                elif chart_type == 'bar':
                    self._update_bar_chart(data)
                elif chart_type == 'pie':
                    self._update_pie_chart(data)
                elif chart_type == 'multiline':
                    self._update_multiline_chart(data)
                elif chart_type == 'stacked_bar':
                    self._update_stacked_bar_chart(data)
                
                # Update title
                if 'title' in data:
                    self.chart.setTitle(data['title'])
                
                # Update legend
                self.chart.legend().setVisible(True)
                self.chart.legend().setLabelColor(CHART_COLORS['text'])
                
            except Exception as e:
                print(f"Error updating QtCharts widget: {e}")
        
        def _update_line_chart(self, data):
            """Update line chart"""
            series = QLineSeries()
            
            # Add points
            x_data = data.get('x', [])
            y_data = data.get('y', [])
            for x, y in zip(x_data, y_data):
                series.append(x, y)
            
            # Set color
            color = QColor(data.get('color', '#4FC3F7'))
            pen = QPen(color, 2)
            series.setPen(pen)
            
            # Add area series for fill
            area_series = QAreaSeries(series)
            area_series.setColor(color.lighter(150))
            area_series.setOpacity(0.3)
            
            self.chart.addSeries(area_series)
            self.chart.addSeries(series)
            
            # Create axes
            axis_x = QValueAxis()
            axis_x.setTitleText(data.get('xlabel', ''))
            axis_x.setLabelsColor(CHART_COLORS['text'])
            axis_x.setTitleBrush(QBrush(CHART_COLORS['text']))
            axis_x.setGridLineColor(CHART_COLORS['grid'])
            
            axis_y = QValueAxis()
            axis_y.setTitleText(data.get('ylabel', ''))
            axis_y.setLabelsColor(CHART_COLORS['text'])
            axis_y.setTitleBrush(QBrush(CHART_COLORS['text']))
            axis_y.setGridLineColor(CHART_COLORS['grid'])
            
            self.chart.addAxis(axis_x, Qt.AlignBottom)
            self.chart.addAxis(axis_y, Qt.AlignLeft)
            
            series.attachAxis(axis_x)
            series.attachAxis(axis_y)
            area_series.attachAxis(axis_x)
            area_series.attachAxis(axis_y)
        
        def _update_bar_chart(self, data):
            """Update bar chart"""
            series = QBarSeries()
            bar_set = QBarSet("")
            
            # Add values
            values = data.get('values', [])
            for value in values:
                bar_set.append(value)
            
            # Set colors
            colors = data.get('colors', [QColor('#4FC3F7')])
            for i, color in enumerate(colors):
                if i < bar_set.count():
                    bar_set.setColor(QColor(color))
            
            series.append(bar_set)
            self.chart.addSeries(series)
            
            # Create axes
            axis_x = QBarCategoryAxis()
            categories = data.get('categories', [])
            axis_x.append(categories)
            axis_x.setTitleText(data.get('xlabel', ''))
            axis_x.setLabelsColor(CHART_COLORS['text'])
            axis_x.setTitleBrush(QBrush(CHART_COLORS['text']))
            
            axis_y = QValueAxis()
            axis_y.setTitleText(data.get('ylabel', ''))
            axis_y.setLabelsColor(CHART_COLORS['text'])
            axis_y.setTitleBrush(QBrush(CHART_COLORS['text']))
            axis_y.setGridLineColor(CHART_COLORS['grid'])
            
            self.chart.addAxis(axis_x, Qt.AlignBottom)
            self.chart.addAxis(axis_y, Qt.AlignLeft)
            
            series.attachAxis(axis_x)
            series.attachAxis(axis_y)
        
        def _update_pie_chart(self, data):
            """Update pie chart"""
            series = QPieSeries()
            series.setHoleSize(0.4)  # Donut chart
            
            labels = data.get('labels', [])
            values = data.get('values', [])
            colors = data.get('colors', ['#4CAF50', '#F44336'])
            
            for label, value, color in zip(labels, values, colors):
                slice_ = series.append(label, value)
                slice_.setColor(QColor(color))
                slice_.setLabelVisible(True)
                slice_.setLabelColor(QColor('#FFFFFF'))
            
            self.chart.addSeries(series)
        
        def _update_multiline_chart(self, data):
            """Update multi-line chart"""
            series_list = []
            
            for series_data in data.get('series', []):
                series = QLineSeries()
                series.setName(series_data.get('name', ''))
                
                # Add points
                x_data = series_data.get('x', [])
                y_data = series_data.get('y', [])
                for x, y in zip(x_data, y_data):
                    series.append(x, y)
                
                # Set color
                color = QColor(series_data.get('color', '#888888'))
                pen = QPen(color, 2)
                series.setPen(pen)
                
                series_list.append(series)
                self.chart.addSeries(series)
            
            # Create axes
            axis_x = QValueAxis()
            axis_x.setTitleText(data.get('xlabel', ''))
            axis_x.setLabelsColor(CHART_COLORS['text'])
            axis_x.setTitleBrush(QBrush(CHART_COLORS['text']))
            axis_x.setGridLineColor(CHART_COLORS['grid'])
            
            axis_y = QValueAxis()
            axis_y.setTitleText(data.get('ylabel', ''))
            axis_y.setLabelsColor(CHART_COLORS['text'])
            axis_y.setTitleBrush(QBrush(CHART_COLORS['text']))
            axis_y.setGridLineColor(CHART_COLORS['grid'])
            
            self.chart.addAxis(axis_x, Qt.AlignBottom)
            self.chart.addAxis(axis_y, Qt.AlignLeft)
            
            for series in series_list:
                series.attachAxis(axis_x)
                series.attachAxis(axis_y)
        
        def _update_stacked_bar_chart(self, data):
            """Update stacked bar chart"""
            categories = data.get('categories', [])
            series_data = data.get('series', [])
            
            # Create bar series
            bar_series = QBarSeries()
            bar_series.setLabelsPosition(QBarSeries.LabelsCenter)
            
            # Create bar sets for each series
            bar_sets = []
            for i, s in enumerate(series_data):
                bar_set = QBarSet(s.get('name', f'Series {i}'))
                bar_set.setColor(QColor(s.get('color', '#888888')))
                bar_sets.append(bar_set)
            
            # Add values to bar sets
            for i in range(len(categories)):
                for j, bar_set in enumerate(bar_sets):
                    if i < len(series_data[j].get('values', [])):
                        bar_set.append(series_data[j]['values'][i])
                    else:
                        bar_set.append(0)
            
            # Add bar sets to series
            for bar_set in bar_sets:
                bar_series.append(bar_set)
            
            self.chart.addSeries(bar_series)
            
            # Create axes
            axis_x = QBarCategoryAxis()
            axis_x.append(categories)
            axis_x.setTitleText(data.get('xlabel', ''))
            axis_x.setLabelsColor(CHART_COLORS['text'])
            axis_x.setTitleBrush(QBrush(CHART_COLORS['text']))
            
            axis_y = QValueAxis()
            axis_y.setTitleText(data.get('ylabel', ''))
            axis_y.setLabelsColor(CHART_COLORS['text'])
            axis_y.setTitleBrush(QBrush(CHART_COLORS['text']))
            axis_y.setGridLineColor(CHART_COLORS['grid'])
            
            self.chart.addAxis(axis_x, Qt.AlignBottom)
            self.chart.addAxis(axis_y, Qt.AlignLeft)
            
            bar_series.attachAxis(axis_x)
            bar_series.attachAxis(axis_y)
        
        def clear_chart(self):
            """Clear the chart"""
            self.chart.removeAllSeries()
            self.chart.removeAxis(self.chart.axisX())
            self.chart.removeAxis(self.chart.axisY())

# ===== MATPLOTLIB WIDGET =====
if MATPLOTLIB_AVAILABLE:
    class MatplotlibWidget(ChartWidget):
        """Widget using Matplotlib for rendering"""
        
        def __init__(self, parent=None):
            super().__init__(parent)
            self.figure = None
            self.canvas = None
            self.ax = None
            self.init_ui()
        
        def init_ui(self):
            """Initialize the UI"""
            layout = QVBoxLayout(self)
            layout.setContentsMargins(0, 0, 0, 0)
            
            # Create matplotlib figure
            self.figure = Figure(facecolor='#1e1e2e')
            self.canvas = FigureCanvasQTAgg(self.figure)
            self.ax = self.figure.add_subplot(111)
            
            # Set dark theme
            self.ax.set_facecolor('#1e1e2e')
            self.ax.tick_params(colors='#e0e0e0')
            self.ax.xaxis.label.set_color('#e0e0e0')
            self.ax.yaxis.label.set_color('#e0e0e0')
            self.ax.title.set_color('#e0e0e0')
            self.ax.spines['bottom'].set_color('#646478')
            self.ax.spines['top'].set_color('#646478')
            self.ax.spines['left'].set_color('#646478')
            self.ax.spines['right'].set_color('#646478')
            self.ax.grid(True, color='#505064', alpha=0.5)
            
            layout.addWidget(self.canvas)
        
        def update_chart(self, data, layout=None):
            """Update chart with new data"""
            if not data:
                return
            
            try:
                # Clear existing plot
                self.ax.clear()
                
                chart_type = data.get('type', '')
                
                if chart_type == 'line':
                    self._update_line_chart(data)
                elif chart_type == 'bar':
                    self._update_bar_chart(data)
                elif chart_type == 'pie':
                    self._update_pie_chart(data)
                elif chart_type == 'multiline':
                    self._update_multiline_chart(data)
                elif chart_type == 'stacked_bar':
                    self._update_stacked_bar_chart(data)
                
                # Update title
                if 'title' in data:
                    self.ax.set_title(data['title'], color='#e0e0e0')
                
                # Update labels
                if 'xlabel' in data:
                    self.ax.set_xlabel(data['xlabel'], color='#e0e0e0')
                if 'ylabel' in data:
                    self.ax.set_ylabel(data['ylabel'], color='#e0e0e0')
                
                # Set dark theme again
                self.ax.set_facecolor('#1e1e2e')
                self.ax.tick_params(colors='#e0e0e0')
                self.ax.xaxis.label.set_color('#e0e0e0')
                self.ax.yaxis.label.set_color('#e0e0e0')
                self.ax.title.set_color('#e0e0e0')
                self.ax.spines['bottom'].set_color('#646478')
                self.ax.spines['top'].set_color('#646478')
                self.ax.spines['left'].set_color('#646478')
                self.ax.spines['right'].set_color('#646478')
                self.ax.grid(True, color='#505064', alpha=0.5)
                
                # Redraw
                self.figure.tight_layout()
                self.canvas.draw()
                
            except Exception as e:
                print(f"Error updating Matplotlib widget: {e}")
        
        def _update_line_chart(self, data):
            """Update line chart"""
            x_data = data.get('x', [])
            y_data = data.get('y', [])
            color = data.get('color', '#4FC3F7')
            
            self.ax.plot(x_data, y_data, color=color, linewidth=2)
            self.ax.fill_between(x_data, y_data, color=color, alpha=0.2)
        
        def _update_bar_chart(self, data):
            """Update bar chart"""
            categories = data.get('categories', [])
            values = data.get('values', [])
            colors = data.get('colors', ['#4FC3F7'] * len(categories))
            
            bars = self.ax.bar(categories, values, color=colors)
            
            # Add value labels on top of bars
            for i, (bar, value) in enumerate(zip(bars, values)):
                height = bar.get_height()
                self.ax.text(bar.get_x() + bar.get_width()/2., height + 0.1,
                           f'{value:.1f}', ha='center', va='bottom',
                           color='#e0e0e0')
        
        def _update_pie_chart(self, data):
            """Update pie chart"""
            labels = data.get('labels', [])
            values = data.get('values', [])
            colors = data.get('colors', ['#4CAF50', '#F44336'])
            
            # Create donut chart
            wedges, texts = self.ax.pie(values, colors=colors, startangle=90)
            
            # Draw circle for donut effect
            centre_circle = plt.Circle((0,0),0.70,fc='#1e1e2e')
            self.ax.add_artist(centre_circle)
            
            # Add legend
            self.ax.legend(wedges, labels, loc="center", frameon=False)
        
        def _update_multiline_chart(self, data):
            """Update multi-line chart"""
            for series_data in data.get('series', []):
                x_data = series_data.get('x', [])
                y_data = series_data.get('y', [])
                color = series_data.get('color', '#888888')
                name = series_data.get('name', '')
                
                self.ax.plot(x_data, y_data, color=color, linewidth=2, label=name)
            
            # Add legend
            self.ax.legend()
        
        def _update_stacked_bar_chart(self, data):
            """Update stacked bar chart"""
            categories = data.get('categories', [])
            series_data = data.get('series', [])
            
            # Prepare data for stacking
            bottom = [0] * len(categories)
            bar_width = 0.8
            
            for i, s in enumerate(series_data):
                values = s.get('values', [0] * len(categories))
                color = s.get('color', '#888888')
                name = s.get('name', f'Series {i}')
                
                bars = self.ax.bar(categories, values, bar_width, 
                                  bottom=bottom, color=color, label=name)
                bottom = [b + v for b, v in zip(bottom, values)]
            
            # Add legend
            self.ax.legend()
        
        def clear_chart(self):
            """Clear the chart"""
            self.ax.clear()
            self.canvas.draw()

# ===== SIMPLE CHART WIDGET (FALLBACK) =====
class SimpleChartWidget(ChartWidget):
    """Simple chart widget using QPainter as last resort"""
    
    def __init__(self, parent=None):
        super().__init__(parent)
        self.chart_data = {}
        self.chart_type = ''
        self.setMinimumSize(300, 200)
    
    def paintEvent(self, event):
        """Paint the chart"""
        painter = QPainter(self)
        painter.setRenderHint(QPainter.Antialiasing)
        
        # Draw background
        painter.fillRect(self.rect(), CHART_COLORS['background'])
        
        if not self.chart_data:
            # Draw placeholder text
            painter.setPen(QPen(CHART_COLORS['text']))
            painter.setFont(QFont("Segoe UI", 10))
            painter.drawText(self.rect(), Qt.AlignCenter, "No chart data available")
            return
        
        # Draw chart based on type
        if self.chart_type == 'line':
            self._draw_line_chart(painter)
        elif self.chart_type == 'bar':
            self._draw_bar_chart(painter)
        elif self.chart_type == 'pie':
            self._draw_pie_chart(painter)
        else:
            # Draw title
            title = self.chart_data.get('title', 'Chart')
            painter.setPen(QPen(CHART_COLORS['text']))
            painter.setFont(QFont("Segoe UI", 12, QFont.Bold))
            painter.drawText(10, 25, title)
            
            # Draw data summary
            painter.setFont(QFont("Segoe UI", 10))
            if 'values' in self.chart_data:
                values = self.chart_data['values']
                for i, value in enumerate(values):
                    painter.drawText(20, 50 + i * 20, f"Value {i+1}: {value:.2f}")
    
    def update_chart(self, data, layout=None):
        """Update chart with new data"""
        self.chart_data = data
        self.chart_type = data.get('type', '')
        self.update()
    
    def _draw_line_chart(self, painter):
        """Draw a simple line chart"""
        # Draw title
        title = self.chart_data.get('title', 'Line Chart')
        painter.setPen(QPen(CHART_COLORS['text']))
        painter.setFont(QFont("Segoe UI", 12, QFont.Bold))
        painter.drawText(10, 25, title)
        
        # Get data
        x_data = self.chart_data.get('x', [])
        y_data = self.chart_data.get('y', [])
        
        if len(x_data) < 2 or len(y_data) < 2:
            return
        
        # Calculate drawing area
        margin = 50
        chart_rect = QRect(margin, margin + 20, 
                          self.width() - 2 * margin, 
                          self.height() - 2 * margin - 20)
        
        # Draw grid
        painter.setPen(QPen(CHART_COLORS['grid'], 1))
        for i in range(1, 5):
            x = chart_rect.left() + i * chart_rect.width() // 5
            painter.drawLine(x, chart_rect.top(), x, chart_rect.bottom())
            y = chart_rect.top() + i * chart_rect.height() // 5
            painter.drawLine(chart_rect.left(), y, chart_rect.right(), y)
        
        # Calculate min/max values
        y_min = min(y_data) if y_data else 0
        y_max = max(y_data) if y_data else 1
        
        # Draw line
        color = QColor(self.chart_data.get('color', '#4FC3F7'))
        painter.setPen(QPen(color, 2))
        
        points = []
        for i, (x, y) in enumerate(zip(x_data, y_data)):
            if i >= len(y_data):
                break
            
            # Normalize coordinates
            x_norm = (i / max(1, len(x_data) - 1))
            y_norm = ((y_data[i] - y_min) / max(1, y_max - y_min))
            
            x_pos = chart_rect.left() + x_norm * chart_rect.width()
            y_pos = chart_rect.bottom() - y_norm * chart_rect.height()
            
            points.append(QPointF(x_pos, y_pos))
            
            # Draw point
            painter.drawEllipse(QPointF(x_pos, y_pos), 3, 3)
        
        # Draw line connecting points
        if len(points) > 1:
            painter.drawPolyline(points)
        
        # Draw labels
        painter.setPen(QPen(CHART_COLORS['text']))
        painter.setFont(QFont("Segoe UI", 9))
        
        # X label
        xlabel = self.chart_data.get('xlabel', 'X')
        painter.drawText(chart_rect.left() + chart_rect.width() // 2 - 20,
                        self.height() - 10, xlabel)
        
        # Y label
        ylabel = self.chart_data.get('ylabel', 'Y')
        painter.save()
        painter.translate(10, chart_rect.top() + chart_rect.height() // 2)
        painter.rotate(-90)
        painter.drawText(0, 0, ylabel)
        painter.restore()
    
    def _draw_bar_chart(self, painter):
        """Draw a simple bar chart"""
        # Draw title
        title = self.chart_data.get('title', 'Bar Chart')
        painter.setPen(QPen(CHART_COLORS['text']))
        painter.setFont(QFont("Segoe UI", 12, QFont.Bold))
        painter.drawText(10, 25, title)
        
        # Get data
        categories = self.chart_data.get('categories', [])
        values = self.chart_data.get('values', [])
        colors = self.chart_data.get('colors', ['#4FC3F7'] * len(categories))
        
        if not categories or not values:
            return
        
        # Calculate drawing area
        margin = 60
        chart_rect = QRect(margin, margin + 20, 
                          self.width() - 2 * margin, 
                          self.height() - 2 * margin - 20)
        
        bar_width = min(50, chart_rect.width() // (len(categories) * 2))
        bar_spacing = chart_rect.width() // len(categories)
        
        # Find max value for scaling
        max_value = max(values) if values else 1
        
        # Draw bars
        for i, (category, value, color_str) in enumerate(zip(categories, values, colors)):
            # Calculate bar position and height
            x = chart_rect.left() + i * bar_spacing + (bar_spacing - bar_width) // 2
            bar_height = (value / max_value) * chart_rect.height() * 0.8
            y = chart_rect.bottom() - bar_height
            
            # Draw bar
            color = QColor(color_str)
            painter.fillRect(QRectF(x, y, bar_width, bar_height), color)
            
            # Draw outline
            painter.setPen(QPen(color.darker(), 1))
            painter.drawRect(QRectF(x, y, bar_width, bar_height))
            
            # Draw value label
            painter.setPen(QPen(CHART_COLORS['text']))
            painter.setFont(QFont("Segoe UI", 8))
            painter.drawText(x, y - 5, f"{value:.1f}")
            
            # Draw category label
            painter.drawText(x - bar_width // 2, chart_rect.bottom() + 20, 
                           category[:10])  # Truncate long names
        
        # Draw labels
        painter.setPen(QPen(CHART_COLORS['text']))
        painter.setFont(QFont("Segoe UI", 9))
        
        # X label
        xlabel = self.chart_data.get('xlabel', 'Categories')
        painter.drawText(chart_rect.left() + chart_rect.width() // 2 - 30,
                        self.height() - 10, xlabel)
        
        # Y label
        ylabel = self.chart_data.get('ylabel', 'Values')
        painter.save()
        painter.translate(15, chart_rect.top() + chart_rect.height() // 2)
        painter.rotate(-90)
        painter.drawText(0, 0, ylabel)
        painter.restore()
    
    def _draw_pie_chart(self, painter):
        """Draw a simple pie chart"""
        # Draw title
        title = self.chart_data.get('title', 'Pie Chart')
        painter.setPen(QPen(CHART_COLORS['text']))
        painter.setFont(QFont("Segoe UI", 12, QFont.Bold))
        painter.drawText(10, 25, title)
        
        # Get data
        labels = self.chart_data.get('labels', [])
        values = self.chart_data.get('values', [])
        colors = self.chart_data.get('colors', ['#4CAF50', '#F44336'])
        
        if not labels or not values:
            return
        
        # Calculate total
        total = sum(values)
        if total == 0:
            return
        
        # Calculate center and radius
        center_x = self.width() // 2
        center_y = self.height() // 2 + 20
        radius = min(center_x, center_y) - 40
        
        # Draw pie slices
        start_angle = 0
        for i, (label, value, color_str) in enumerate(zip(labels, values, colors)):
            # Calculate angle for this slice
            angle = (value / total) * 360 * 16  # Qt uses 1/16th of a degree
            
            # Draw slice
            color = QColor(color_str)
            painter.setBrush(color)
            painter.setPen(QPen(color.darker(), 1))
            painter.drawPie(center_x - radius, center_y - radius, 
                           radius * 2, radius * 2, 
                           int(start_angle), int(angle))
            
            # Calculate label position
            mid_angle = start_angle + angle / 2
            label_x = center_x + (radius + 20) * math.cos(math.radians(mid_angle / 16))
            label_y = center_y + (radius + 20) * math.sin(math.radians(mid_angle / 16))
            
            # Draw label
            percentage = (value / total) * 100
            label_text = f"{label}: {percentage:.1f}%"
            painter.setPen(QPen(CHART_COLORS['text']))
            painter.setFont(QFont("Segoe UI", 9))
            
            text_rect = painter.boundingRect(0, 0, 100, 20, Qt.AlignLeft, label_text)
            text_rect.moveCenter(QPoint(int(label_x), int(label_y)))
            painter.drawText(text_rect, label_text)
            
            start_angle += angle
        
        # Draw donut hole for donut chart
        hole_radius = radius * 0.4
        painter.setBrush(CHART_COLORS['background'])
        painter.setPen(QPen(CHART_COLORS['background']))
        painter.drawEllipse(QPoint(center_x, center_y), int(hole_radius), int(hole_radius))
    
    def clear_chart(self):
        """Clear the chart"""
        self.chart_data = {}
        self.chart_type = ''
        self.update()

# ===== CHART WIDGET FACTORY =====
def create_chart_widget(parent=None):
    """Create appropriate chart widget based on available backends"""
    if WEBENGINE_AVAILABLE:
        return PlotlyWidget(parent)
    elif QTCHARTS_AVAILABLE:
        return QtChartsWidget(parent)
    elif MATPLOTLIB_AVAILABLE:
        return MatplotlibWidget(parent)
    else:
        return SimpleChartWidget(parent)

# ===== UI WIDGETS =====
class KpiCard(QFrame):
    """Custom widget for displaying KPI cards"""
    
    def __init__(self, title: str, value: Any, unit: str = "", icon: str = "", 
                 color: str = "#4FC3F7", parent=None):
        super().__init__(parent)
        
        self.title = title
        self.unit = unit
        self.icon = icon
        self.color = color
        
        # Target value for animation
        self.is_numeric = True  # Track if value is numeric
        self.target_value = self._parse_value(value)
        self.current_value = self.target_value
        
        # Animation
        self.animation_timer = QTimer()
        self.animation_timer.timeout.connect(self._update_animation)
        self.animation_speed = 0.1
        
        self.init_ui()
        self.set_value(value)
    
    def _parse_value(self, value):
        """Parse value for animation"""
        if isinstance(value, (int, float)):
            return float(value)
        elif isinstance(value, str):
            try:
                return float(value)
            except:
                return 0.0
        return 0.0
    
    def init_ui(self):
        """Initialize the card UI"""
        self.setObjectName("kpiCard")
        self.setMinimumSize(200, 120)
        
        layout = QVBoxLayout(self)
        layout.setContentsMargins(15, 15, 15, 15)
        layout.setSpacing(8)
        
        # Title row
        title_layout = QHBoxLayout()
        title_layout.setSpacing(10)
        
        # Icon
        if self.icon:
            icon_label = QLabel(self.icon)
            icon_label.setStyleSheet(f"font-size: 20px; color: {self.color};")
            title_layout.addWidget(icon_label)
        
        # Title
        title_label = QLabel(self.title)
        title_font = QFont("Segoe UI", 10)
        title_label.setFont(title_font)
        title_label.setStyleSheet("color: #aaaaaa;")
        title_layout.addWidget(title_label)
        title_layout.addStretch()
        
        layout.addLayout(title_layout)
        
        # Value
        self.value_label = QLabel("0")
        value_font = QFont("Segoe UI", 24, QFont.Bold)
        self.value_label.setFont(value_font)
        self.value_label.setStyleSheet(f"color: {self.color};")
        self.value_label.setAlignment(Qt.AlignLeft)
        layout.addWidget(self.value_label)
        
        # Unit
        if self.unit:
            unit_label = QLabel(self.unit)
            unit_font = QFont("Segoe UI", 9)
            unit_label.setFont(unit_font)
            unit_label.setStyleSheet("color: #888888;")
            layout.addWidget(unit_label)
        
        layout.addStretch()
        
        # Set style
        self.setStyleSheet(f"""
            QFrame#kpiCard {{
                background-color: rgba(40, 40, 50, 0.8);
                border: 1px solid rgba(60, 60, 70, 0.8);
                border-radius: 10px;
            }}
            QFrame#kpiCard:hover {{
                border: 1px solid {self.color};
                background-color: rgba(45, 45, 55, 0.9);
            }}
        """)
    
    def set_value(self, value: Any):
        """Set the KPI value with animation"""
        # Check if value is numeric
        try:
            # Try to convert to float for animation
            numeric_value = float(value)
            self.is_numeric = True
            self.target_value = numeric_value
            
            if not self.animation_timer.isActive():
                self.animation_timer.start(16)  # ~60 FPS
        except (ValueError, TypeError):
            # Non-numeric value (like bottleneck station name)
            self.is_numeric = False
            self.animation_timer.stop()
            self.value_label.setText(str(value))
    
    def _update_animation(self):
        """Update value with smooth animation"""
        if not self.is_numeric:
            self.animation_timer.stop()
            return
            
        diff = self.target_value - self.current_value
        
        if abs(diff) < 0.1:
            self.current_value = self.target_value
            self.animation_timer.stop()
        else:
            self.current_value += diff * self.animation_speed
        
        # Format and display
        if isinstance(self.target_value, float) and self.target_value != int(self.target_value):
            display_text = f"{self.current_value:.1f}"
        else:
            display_text = f"{int(self.current_value)}"
        
        self.value_label.setText(display_text)

class StationBadge(QFrame):
    """Badge for displaying station state"""
    
    def __init__(self, station_id: str, parent=None):
        super().__init__(parent)
        self.station_id = station_id
        self.state = "IDLE"
        
        self.setObjectName(f"StationBadge_{station_id}")
        
        self.init_ui()
    
    def init_ui(self):
        """Initialize badge UI"""
        self.setFixedSize(80, 60)
        
        layout = QVBoxLayout(self)
        layout.setContentsMargins(5, 5, 5, 5)
        layout.setSpacing(3)
        
        # Station ID
        self.id_label = QLabel(self.station_id)
        id_font = QFont("Segoe UI", 10, QFont.Bold)
        self.id_label.setFont(id_font)
        self.id_label.setAlignment(Qt.AlignCenter)
        layout.addWidget(self.id_label)
        
        # State indicator
        self.state_label = QLabel("IDLE")
        state_font = QFont("Segoe UI", 8)
        self.state_label.setFont(state_font)
        self.state_label.setAlignment(Qt.AlignCenter)
        layout.addWidget(self.state_label)
        
        # Set initial style
        self.update_style("IDLE")
    
    def update_style(self, state: str):
        """Update badge style based on state"""
        self.state = state
        
        colors = {
            "READY": ("#4CAF50", "#1B5E20"),
            "BUSY": ("#FF9800", "#E65100"),
            "DONE": ("#2196F3", "#0D47A1"),
            "FAULT": ("#F44336", "#B71C1C"),
            "IDLE": ("#9E9E9E", "#424242")
        }
        
        color, dark_color = colors.get(state, ("#9E9E9E", "#424242"))
        
        self.state_label.setText(state)
        self.setStyleSheet(f"""
            QFrame#StationBadge_{self.station_id} {{
                background-color: qlineargradient(
                    x1:0, y1:0, x2:0, y2:1,
                    stop:0 {color},
                    stop:1 {dark_color}
                );
                border: 2px solid rgba(255, 255, 255, 0.2);
                border-radius: 8px;
            }}
            QLabel {{
                color: white;
                background: transparent;
            }}
        """)

# ===== MAIN WINDOW =====
class KpiDashboard(QMainWindow):
    """Main KPI Dashboard window"""
    
    def __init__(self):
        super().__init__()
        self.setWindowTitle("Production Line KPI Dashboard")
        self.setGeometry(100, 50, 1600, 1000)
        
        # Data
        self.log_paths = {}
        self.replay_events = {}
        self.replay_min_time = 0
        self.replay_max_time = 0
        self.current_time_ns = 0  # Current VSI time (updated from events)
        self.is_live_mode = True
        self.is_playing = False
        self.playback_speed = 1.0
        
        # Replay performance - incremental processing
        self.replay_cursors = {}  # station_id -> current event index
        self.last_replay_time = 0  # Last processed replay time
        
        # UI component storage
        self.station_ui = {}  # station_id -> dict of UI components
        
        # Recent events storage
        self.recent_events = {station_id: deque(maxlen=50) for station_id in STATIONS.keys()}
        
        # Workers and managers
        self.tail_workers = {}
        self.kpi_calculator = KpiCalculator()
        self.chart_manager = ChartManager()
        
        # Data buffers for charts
        self.kpi_history = deque(maxlen=CHART_POINT_LIMIT)
        self.station_history = {st_id: deque(maxlen=CHART_POINT_LIMIT) 
                               for st_id in STATIONS.keys()}
        
        # UI
        self.init_ui()
        
        # Timers
        self.ui_timer = QTimer()
        self.ui_timer.timeout.connect(self.update_ui)
        self.ui_timer.start(1000 // UI_REFRESH_FPS)
        
        self.chart_timer = QTimer()
        self.chart_timer.timeout.connect(self.update_charts)
        self.chart_timer.start(1000 // CHART_REFRESH_FPS)
        
        # Connect signals
        self.kpi_calculator.kpis_updated.connect(self.on_kpis_updated)
        
        # Initial log discovery
        QTimer.singleShot(500, self.discover_logs)
    
    def init_ui(self):
        """Initialize the user interface"""
        # Central widget
        central_widget = QWidget()
        self.setCentralWidget(central_widget)
        
        main_layout = QHBoxLayout(central_widget)
        main_layout.setSpacing(0)
        main_layout.setContentsMargins(0, 0, 0, 0)
        
        # ===== LEFT NAVIGATION =====
        nav_widget = QWidget()
        nav_widget.setFixedWidth(220)
        nav_widget.setObjectName("navWidget")
        
        nav_layout = QVBoxLayout(nav_widget)
        nav_layout.setContentsMargins(10, 20, 10, 20)
        nav_layout.setSpacing(10)
        
        # Title
        title_label = QLabel("KPI Dashboard")
        title_font = QFont("Segoe UI", 14, QFont.Bold)
        title_label.setFont(title_font)
        title_label.setStyleSheet("color: #4FC3F7; padding: 10px 0;")
        title_label.setAlignment(Qt.AlignCenter)
        nav_layout.addWidget(title_label)
        
        nav_layout.addSpacing(20)
        
        # Navigation buttons
        self.nav_buttons = {}
        
        # ALL view button
        all_button = QPushButton("📊 ALL Stations")
        all_button.setObjectName("allNavButton")
        all_button.clicked.connect(lambda: self.switch_view("ALL"))
        nav_layout.addWidget(all_button)
        self.nav_buttons["ALL"] = all_button
        
        nav_layout.addSpacing(10)
        
        # Station buttons
        for station_id, station_info in STATIONS.items():
            btn = QPushButton(f"{station_info['icon']} {station_id}")
            btn.setObjectName(f"{station_id}NavButton")
            btn.clicked.connect(lambda checked=False, sid=station_id: self.switch_view(sid))
            nav_layout.addWidget(btn)
            self.nav_buttons[station_id] = btn
        
        nav_layout.addStretch()
        
        # Version label
        version_label = QLabel(f"v1.3 - {CHART_BACKEND}")
        version_label.setStyleSheet("color: #666666; font-size: 9px;")
        version_label.setAlignment(Qt.AlignCenter)
        nav_layout.addWidget(version_label)
        
        main_layout.addWidget(nav_widget)
        
        # ===== MAIN CONTENT =====
        content_widget = QWidget()
        content_layout = QVBoxLayout(content_widget)
        content_layout.setContentsMargins(0, 0, 0, 0)
        content_layout.setSpacing(0)
        
        # Header
        header = self.create_header()
        content_layout.addWidget(header)
        
        # Stacked widget for views
        self.stacked_widget = QStackedWidget()
        content_layout.addWidget(self.stacked_widget, 1)
        
        # Create views
        self.all_view = self.create_all_view()
        self.station_views = {}
        
        for station_id in STATIONS.keys():
            self.station_views[station_id] = self.create_station_view(station_id)
        
        self.stacked_widget.addWidget(self.all_view)
        for station_id, view in self.station_views.items():
            self.stacked_widget.addWidget(view)
        
        main_layout.addWidget(content_widget, 1)
        
        # Apply styles
        self.apply_styles()
    
    def create_header(self):
        """Create the header bar"""
        header = QFrame()
        header.setObjectName("header")
        header.setFixedHeight(60)
        
        layout = QHBoxLayout(header)
        layout.setContentsMargins(20, 10, 20, 10)
        
        # Title
        title_label = QLabel("Production Line KPI Dashboard")
        title_font = QFont("Segoe UI", 16, QFont.Bold)
        title_label.setFont(title_font)
        title_label.setStyleSheet("color: white;")
        layout.addWidget(title_label)
        
        layout.addStretch()
        
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
        layout.addWidget(self.mode_badge)
        
        layout.addSpacing(20)
        
        # Status label
        self.status_label = QLabel("● ACTIVE")
        self.status_label.setFont(QFont("Segoe UI", 10))
        self.status_label.setStyleSheet("color: #4CAF50;")
        layout.addWidget(self.status_label)
        
        layout.addSpacing(20)
        
        # Timeline controls (hidden in LIVE mode)
        self.timeline_widget = QWidget()
        timeline_layout = QHBoxLayout(self.timeline_widget)
        timeline_layout.setContentsMargins(0, 0, 0, 0)
        timeline_layout.setSpacing(10)
        
        self.play_button = QPushButton("⏸")
        self.play_button.setFixedSize(40, 30)
        self.play_button.clicked.connect(self.toggle_play)
        self.play_button.setEnabled(False)
        timeline_layout.addWidget(self.play_button)
        
        self.timeline_slider = QSlider(Qt.Horizontal)
        self.timeline_slider.setFixedWidth(300)
        self.timeline_slider.setEnabled(False)
        self.timeline_slider.setMinimum(0)
        self.timeline_slider.setMaximum(1000)
        self.timeline_slider.valueChanged.connect(self.on_timeline_changed)
        timeline_layout.addWidget(self.timeline_slider)
        
        self.time_label = QLabel("00:00.000")
        self.time_label.setFixedWidth(100)
        self.time_label.setStyleSheet("color: #cccccc; font-family: monospace;")
        timeline_layout.addWidget(self.time_label)
        
        # Speed control combo box
        speed_label = QLabel("Speed:")
        speed_label.setStyleSheet("color: #cccccc;")
        timeline_layout.addWidget(speed_label)
        
        self.speed_combo = QComboBox()
        self.speed_combo.addItems(["0.5x", "1x", "2x", "5x"])
        self.speed_combo.setCurrentIndex(1)
        self.speed_combo.currentIndexChanged.connect(self.on_speed_changed)
        self.speed_combo.setFixedWidth(80)
        timeline_layout.addWidget(self.speed_combo)
        
        layout.addWidget(self.timeline_widget)
        self.timeline_widget.hide()
        
        layout.addSpacing(20)
        
        # Control buttons
        self.live_toggle = QCheckBox("LIVE Mode")
        self.live_toggle.setChecked(True)
        self.live_toggle.stateChanged.connect(self.on_live_toggled)
        layout.addWidget(self.live_toggle)
        
        reload_button = QPushButton("🔄 Reload Logs")
        reload_button.clicked.connect(self.discover_logs)
        layout.addWidget(reload_button)
        
        return header
    
    def create_all_view(self):
        """Create the ALL stations view"""
        scroll_widget = QScrollArea()
        scroll_widget.setWidgetResizable(True)
        scroll_widget.setHorizontalScrollBarPolicy(Qt.ScrollBarAsNeeded)
        scroll_widget.setVerticalScrollBarPolicy(Qt.ScrollBarAsNeeded)
        
        content = QWidget()
        scroll_widget.setWidget(content)
        
        layout = QVBoxLayout(content)
        layout.setSpacing(20)
        layout.setContentsMargins(20, 20, 20, 20)
        
        # ===== KPI CARDS ROW =====
        cards_layout = QHBoxLayout()
        cards_layout.setSpacing(15)
        
        # Create KPI cards
        self.kpi_cards = {
            'throughput': KpiCard("Throughput", "0", "parts/hr", "⚡", "#4FC3F7"),
            'wip': KpiCard("WIP", "0", "parts", "📦", "#FF9800"),
            'completed': KpiCard("Completed", "0", "parts", "✓", "#4CAF50"),
            'rejects': KpiCard("Rejects", "0", "parts", "✗", "#F44336"),
            'bottleneck': KpiCard("Bottleneck", "ST1", "", "⏱️", "#9C27B0")
        }
        
        for card in self.kpi_cards.values():
            cards_layout.addWidget(card)
        
        layout.addLayout(cards_layout)
        
        # ===== PIPELINE STRIP =====
        pipeline_frame = QFrame()
        pipeline_frame.setObjectName("pipelineFrame")
        pipeline_frame.setFixedHeight(80)
        
        pipeline_layout = QHBoxLayout(pipeline_frame)
        pipeline_layout.setContentsMargins(20, 10, 20, 10)
        pipeline_layout.setSpacing(20)
        
        # Create station badges
        self.station_badges = {}
        for station_id in STATIONS.keys():
            badge = StationBadge(station_id)
            pipeline_layout.addWidget(badge)
            self.station_badges[station_id] = badge
        
        pipeline_layout.addStretch()
        layout.addWidget(pipeline_frame)
        
        # ===== CHARTS GRID =====
        charts_grid = QGridLayout()
        charts_grid.setSpacing(15)
        
        # Throughput chart
        self.throughput_chart = create_chart_widget()
        charts_grid.addWidget(self.throughput_chart, 0, 0)
        
        # Cycle time chart
        self.cycle_time_chart = create_chart_widget()
        charts_grid.addWidget(self.cycle_time_chart, 0, 1)
        
        # Utilization chart
        self.utilization_chart = create_chart_widget()
        charts_grid.addWidget(self.utilization_chart, 1, 0)
        
        # Pass/Reject chart
        self.pass_reject_chart = create_chart_widget()
        charts_grid.addWidget(self.pass_reject_chart, 1, 1)
        
        layout.addLayout(charts_grid, 1)
        
        return scroll_widget
    
    def create_station_view(self, station_id: str):
        """Create a station-specific view"""
        scroll_widget = QScrollArea()
        scroll_widget.setWidgetResizable(True)
        
        content = QWidget()
        scroll_widget.setWidget(content)
        
        layout = QVBoxLayout(content)
        layout.setSpacing(20)
        layout.setContentsMargins(20, 20, 20, 20)
        
        # Station header
        station_info = STATIONS[station_id]
        header = QLabel(f"{station_info['icon']} {station_info['name']}")
        header_font = QFont("Segoe UI", 18, QFont.Bold)
        header.setFont(header_font)
        header.setStyleSheet(f"color: {station_info['color']}; padding: 10px 0;")
        layout.addWidget(header)
        
        # ===== STATE CARD =====
        state_card = QFrame()
        state_card.setObjectName("stateCard")
        state_card.setFixedHeight(120)
        
        state_layout = QHBoxLayout(state_card)
        state_layout.setContentsMargins(30, 20, 30, 20)
        
        # State indicators
        state_indicators = {}
        for state_name in ["READY", "BUSY", "DONE", "FAULT"]:
            frame = QFrame()
            frame.setFixedSize(80, 60)
            frame.setObjectName(f"state{state_name}")
            
            frame_layout = QVBoxLayout(frame)
            frame_layout.setContentsMargins(5, 5, 5, 5)
            
            label = QLabel(state_name)
            label.setAlignment(Qt.AlignCenter)
            label.setStyleSheet("color: #888888; font-weight: bold;")
            frame_layout.addWidget(label)
            
            state_layout.addWidget(frame)
            state_indicators[state_name] = frame
        
        state_layout.addStretch()
        
        # Cycle time display
        cycle_frame = QFrame()
        cycle_frame.setFixedWidth(200)
        
        cycle_layout = QVBoxLayout(cycle_frame)
        cycle_layout.setContentsMargins(0, 0, 0, 0)
        
        cycle_label = QLabel("Cycle Time")
        cycle_label.setStyleSheet("color: #aaaaaa; font-size: 12px;")
        cycle_layout.addWidget(cycle_label)
        
        cycle_time_label = QLabel("0.0 ms")
        cycle_time_label.setStyleSheet("color: #4FC3F7; font-size: 24px; font-weight: bold;")
        cycle_layout.addWidget(cycle_time_label)
        
        state_layout.addWidget(cycle_frame)
        
        layout.addWidget(state_card)
        
        # ===== CHARTS ROW =====
        charts_layout = QHBoxLayout()
        charts_layout.setSpacing(15)
        
        # Cycle time trend chart
        cycle_trend_chart = create_chart_widget()
        cycle_trend_chart.setMinimumHeight(400)
        charts_layout.addWidget(cycle_trend_chart, 1)
        
        # Busy/Idle chart
        busy_idle_chart = create_chart_widget()
        busy_idle_chart.setMinimumHeight(400)
        charts_layout.addWidget(busy_idle_chart, 1)
        
        layout.addLayout(charts_layout, 1)
        
        # ===== BOTTOM PANELS =====
        bottom_layout = QHBoxLayout()
        bottom_layout.setSpacing(15)
        
        # Extra fields panel
        extra_frame = QFrame()
        extra_frame.setObjectName("extraFrame")
        extra_frame.setMinimumWidth(300)
        
        extra_layout = QVBoxLayout(extra_frame)
        extra_layout.setContentsMargins(15, 15, 15, 15)
        
        extra_title = QLabel("Extra Fields")
        extra_title.setStyleSheet("color: #4FC3F7; font-weight: bold; font-size: 14px;")
        extra_layout.addWidget(extra_title)
        
        extra_fields_widget = QWidget()
        extra_fields_layout = QVBoxLayout(extra_fields_widget)
        extra_fields_layout.setContentsMargins(0, 10, 0, 0)
        extra_layout.addWidget(extra_fields_widget)
        
        extra_layout.addStretch()
        bottom_layout.addWidget(extra_frame)
        
        # Recent events table
        events_frame = QFrame()
        events_frame.setObjectName("eventsFrame")
        
        events_layout = QVBoxLayout(events_frame)
        events_layout.setContentsMargins(15, 15, 15, 15)
        
        events_title = QLabel("Recent Events (Last 50)")
        events_title.setStyleSheet("color: #4FC3F7; font-weight: bold; font-size: 14px;")
        events_layout.addWidget(events_title)
        
        events_table = QTableWidget()
        events_table.setColumnCount(4)
        events_table.setHorizontalHeaderLabels(["Time", "State", "Cycle Time", "Extra"])
        events_table.horizontalHeader().setStretchLastSection(True)
        events_table.setEditTriggers(QTableWidget.NoEditTriggers)
        events_table.setAlternatingRowColors(True)
        events_table.setMaximumHeight(300)
        events_layout.addWidget(events_table)
        
        bottom_layout.addWidget(events_frame, 1)
        
        layout.addLayout(bottom_layout)
        
        # Store UI components for this station
        self.station_ui[station_id] = {
            "state_indicators": state_indicators,
            "cycle_time_label": cycle_time_label,
            "cycle_trend_chart": cycle_trend_chart,
            "busy_idle_chart": busy_idle_chart,
            "extra_fields_layout": extra_fields_layout,
            "extra_fields_widget": extra_fields_widget,
            "events_table": events_table
        }
        
        return scroll_widget
    
    def apply_styles(self):
        """Apply styles to the application"""
        self.setStyleSheet("""
            QMainWindow {
                background-color: #1e1e2e;
            }
            
            /* Navigation */
            QWidget#navWidget {
                background-color: #252535;
                border-right: 1px solid #333344;
            }
            
            QPushButton {
                background-color: #3a3a4a;
                color: #cccccc;
                border: none;
                padding: 10px 15px;
                border-radius: 5px;
                text-align: left;
                font-weight: bold;
            }
            
            QPushButton:hover {
                background-color: #4a4a5a;
            }
            
            QPushButton:pressed {
                background-color: #2a2a3a;
            }
            
            QPushButton#allNavButton {
                background-color: #2a3a4a;
                color: #4FC3F7;
                font-size: 13px;
            }
            
            /* Header */
            QFrame#header {
                background-color: #252535;
                border-bottom: 1px solid #333344;
            }
            
            QCheckBox {
                color: #cccccc;
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
            
            QComboBox {
                background-color: #3a3a4a;
                color: #cccccc;
                border: 1px solid #555;
                border-radius: 3px;
                padding: 3px 6px;
            }
            
            QComboBox::drop-down {
                border: none;
            }
            
            QComboBox QAbstractItemView {
                background-color: #3a3a4a;
                color: #cccccc;
                selection-background-color: #4a4a5a;
            }
            
            /* Pipeline strip */
            QFrame#pipelineFrame {
                background-color: rgba(40, 40, 50, 0.8);
                border: 1px solid rgba(60, 60, 70, 0.8);
                border-radius: 10px;
            }
            
            /* State card */
            QFrame#stateCard {
                background-color: rgba(40, 40, 50, 0.8);
                border: 1px solid rgba(60, 60, 70, 0.8);
                border-radius: 10px;
            }
            
            QFrame#stateREADY {
                background-color: rgba(76, 175, 80, 0.2);
                border: 2px solid #4CAF50;
                border-radius: 8px;
            }
            
            QFrame#stateBUSY {
                background-color: rgba(255, 152, 0, 0.2);
                border: 2px solid #FF9800;
                border-radius: 8px;
            }
            
            QFrame#stateDONE {
                background-color: rgba(33, 150, 243, 0.2);
                border: 2px solid #2196F3;
                border-radius: 8px;
            }
            
            QFrame#stateFAULT {
                background-color: rgba(244, 67, 54, 0.2);
                border: 2px solid #F44336;
                border-radius: 8px;
            }
            
            /* Extra frames */
            QFrame#extraFrame, QFrame#eventsFrame {
                background-color: rgba(40, 40, 50, 0.8);
                border: 1px solid rgba(60, 60, 70, 0.8);
                border-radius: 10px;
            }
            
            /* Table */
            QTableWidget {
                background-color: rgba(30, 30, 40, 0.8);
                color: #cccccc;
                border: 1px solid rgba(60, 60, 70, 0.5);
                gridline-color: rgba(80, 80, 90, 0.5);
            }
            
            QTableWidget::item {
                padding: 5px;
            }
            
            QTableWidget::item:selected {
                background-color: rgba(79, 195, 247, 0.3);
            }
            
            QHeaderView::section {
                background-color: #2a2a3a;
                color: #cccccc;
                padding: 5px;
                border: none;
                font-weight: bold;
            }
            
            QScrollBar:vertical {
                background-color: #2a2a3a;
                width: 12px;
                border-radius: 6px;
            }
            
            QScrollBar::handle:vertical {
                background-color: #555;
                border-radius: 6px;
                min-height: 20px;
            }
            
            QScrollBar::handle:vertical:hover {
                background-color: #666;
            }
            
            /* Slider */
            QSlider::groove:horizontal {
                background-color: #3a3a4a;
                height: 6px;
                border-radius: 3px;
            }
            
            QSlider::handle:horizontal {
                background-color: #4FC3F7;
                width: 16px;
                height: 16px;
                margin: -5px 0;
                border-radius: 8px;
                border: 2px solid #ffffff;
            }
        """)
    
    def discover_logs(self):
        """Discover and load log files"""
        # Stop existing workers
        self._stop_all_workers()
        
        # Find logs
        self.log_paths = LogDiscoverer.find_station_logs()
        
        # Reset KPI calculator
        self.kpi_calculator.reset()
        self.kpi_history.clear()
        for station_id in STATIONS.keys():
            self.recent_events[station_id].clear()
        
        if self.is_live_mode:
            self.switch_to_live()
        else:
            self.switch_to_replay()
    
    def switch_to_live(self):
        """Switch to LIVE mode"""
        # Stop existing workers
        self._stop_all_workers()
        
        # Clear replay data
        self.replay_events = {}
        self.current_time_ns = 0
        self.replay_cursors = {}
        self.last_replay_time = 0
        
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
        
        self.timeline_widget.hide()
        self.play_button.setEnabled(False)
        self.timeline_slider.setEnabled(False)
        self.is_playing = False
        self.play_button.setText("⏸")
        self.time_label.setText("LIVE")
        
        self.status_label.setText("● ACTIVE")
        self.status_label.setStyleSheet("color: #4CAF50;")
        
        # Start tail workers for each found station
        for station_id in STATIONS.keys():
            if station_id in self.log_paths:
                self._start_station_worker(station_id)
    
    def _start_station_worker(self, station_id: str):
        """Start a tail worker for a station"""
        # Load snapshot first
        latest_event = self.load_live_snapshot(station_id)
        
        # Start worker
        if latest_event:
            worker = LogTailWorker(station_id, self.log_paths[station_id], latest_event)
            # Update initial state immediately from snapshot
            self.kpi_calculator.process_event(latest_event)
            # Also add to recent events
            self.recent_events[station_id].append(latest_event)
        else:
            worker = LogTailWorker(station_id, self.log_paths[station_id])
        
        # Connect signals
        worker.new_event.connect(self.process_new_event)
        worker.activity_detected.connect(self.on_activity_detected)
        
        # Start worker
        worker.start()
        self.tail_workers[station_id] = worker
    
    def load_live_snapshot(self, station_id: str) -> Optional[StationEvent]:
        """Load snapshot of last N lines from a station log"""
        if station_id not in self.log_paths:
            return None
        
        log_path = self.log_paths[station_id]
        if not os.path.exists(log_path):
            return None
        
        try:
            with open(log_path, 'r', encoding='utf-8', errors='ignore') as f:
                lines = collections.deque(f, maxlen=SNAPSHOT_LINES)
            
            parser = StationLogParser(station_id)
            latest_event = None
            
            for line in lines:
                event = parser.parse_line(line)
                if event:
                    latest_event = event
            
            if latest_event is None:
                latest_event = parser.get_current_state()
            
            return latest_event
            
        except Exception as e:
            print(f"Error loading snapshot for {station_id}: {e}")
            return None
    
    def switch_to_replay(self):
        """Switch to REPLAY mode"""
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
        
        self.timeline_widget.show()
        self.play_button.setEnabled(True)
        self.timeline_slider.setEnabled(True)
        self.is_playing = True
        self.play_button.setText("⏸")
        
        self.status_label.setText("● REPLAY")
        self.status_label.setStyleSheet("color: #9C27B0;")
        
        # Load all events
        self.load_replay_data()
        
        # Setup timeline
        if self.replay_events:
            all_times = []
            for events in self.replay_events.values():
                if events:
                    all_times.append(events[0].t_ns)
                    all_times.append(events[-1].t_ns)
            
            if all_times:
                self.replay_min_time = min(all_times)
                self.replay_max_time = max(all_times)
                self.current_time_ns = self.replay_min_time
                self.last_replay_time = self.replay_min_time
                self.timeline_slider.setValue(0)
                self.update_time_label()
    
    def load_replay_data(self):
        """Load events for replay mode"""
        self.replay_events = {}
        self.replay_cursors = {}
        
        for station_id in STATIONS.keys():
            if station_id not in self.log_paths:
                continue
            
            log_path = self.log_paths[station_id]
            try:
                with open(log_path, 'r', encoding='utf-8', errors='ignore') as f:
                    lines = f.readlines()
                
                parser = StationLogParser(station_id)
                events = []
                
                for line in lines:
                    event = parser.parse_line(line)
                    if event:
                        events.append(event)
                
                # Sort by time
                events.sort(key=lambda x: x.t_ns)
                
                # Limit events
                if len(events) > MAX_EVENTS_PER_STATION:
                    events = events[-MAX_EVENTS_PER_STATION:]
                
                self.replay_events[station_id] = events
                self.replay_cursors[station_id] = 0
                
                print(f"Loaded {len(events)} events for {station_id}")
                
            except Exception as e:
                print(f"Error loading {log_path}: {e}")
                continue
    
    def process_new_event(self, event: StationEvent):
        """Process a new event from tail worker"""
        # Update current VSI time
        self.current_time_ns = event.t_ns
        
        # Store in recent events
        self.recent_events[event.station_id].append(event)
        
        # Process in KPI calculator
        self.kpi_calculator.process_event(event)
    
    def on_kpis_updated(self, snapshot: KpiSnapshot):
        """Handle KPI updates from calculator"""
        # Update current VSI time from snapshot
        self.current_time_ns = snapshot.timestamp_ns
        
        # Store in history
        self.kpi_history.append(snapshot)
        
        # Update current view
        current_view = self.stacked_widget.currentWidget()
        if current_view == self.all_view:
            self.update_all_view(snapshot)
        else:
            # Find which station view is active
            for station_id, view in self.station_views.items():
                if view == current_view:
                    self.update_station_view(station_id, snapshot)
                    break
    
    def update_all_view(self, snapshot: KpiSnapshot):
        """Update the ALL stations view"""
        # Update KPI cards
        self.kpi_cards['throughput'].set_value(f"{snapshot.throughput_ph:.1f}")
        self.kpi_cards['wip'].set_value(snapshot.wip)
        self.kpi_cards['completed'].set_value(snapshot.total_completed)
        self.kpi_cards['rejects'].set_value(snapshot.total_rejected)
        self.kpi_cards['bottleneck'].set_value(snapshot.bottleneck_station)
        
        # Update station badges with correct state priority
        for station_id, state in snapshot.station_states.items():
            if station_id in self.station_badges:
                self.station_badges[station_id].update_style(state)
    
    def update_station_view(self, station_id: str, snapshot: KpiSnapshot):
        """Update a station-specific view"""
        if station_id not in self.station_ui:
            return
            
        ui = self.station_ui[station_id]
        
        # Update state indicators with correct priority
        current_state = snapshot.station_states.get(station_id, "IDLE")
        
        # Color mapping for states
        state_colors = {
            "READY": ("rgba(76, 175, 80, 0.4)", "#4CAF50"),
            "BUSY": ("rgba(255, 152, 0, 0.4)", "#FF9800"),
            "DONE": ("rgba(33, 150, 243, 0.4)", "#2196F3"),
            "FAULT": ("rgba(244, 67, 54, 0.4)", "#F44336")
        }
        
        for state_name, frame in ui["state_indicators"].items():
            if state_name == current_state:
                bg_color, border_color = state_colors.get(state_name, ("rgba(40, 40, 50, 0.8)", "#888888"))
                frame.setStyleSheet(f"""
                    QFrame {{
                        background-color: {bg_color};
                        border: 2px solid {border_color};
                        border-radius: 8px;
                    }}
                    QLabel {{
                        color: white;
                        font-weight: bold;
                    }}
                """)
            else:
                frame.setStyleSheet(f"""
                    QFrame {{
                        background-color: rgba(40, 40, 50, 0.8);
                        border: 2px solid rgba(60, 60, 70, 0.8);
                        border-radius: 8px;
                    }}
                    QLabel {{
                        color: #888888;
                    }}
                """)
        
        # Update cycle time
        cycle_time = snapshot.avg_cycle_times.get(station_id, 0.0)
        ui["cycle_time_label"].setText(f"{cycle_time:.1f} ms")
        
        # Update extra fields
        extra_fields = snapshot.station_extra_fields.get(station_id, {})
        self.update_extra_fields(station_id, extra_fields)
        
        # Update events table
        self.update_events_table(station_id)
    
    def update_extra_fields(self, station_id: str, extra_fields: Dict[str, Any]):
        """Update extra fields display for specific station"""
        if station_id not in self.station_ui:
            return
            
        ui = self.station_ui[station_id]
        
        # Clear existing layout completely
        while ui["extra_fields_layout"].count():
            item = ui["extra_fields_layout"].takeAt(0)
            if item.widget():
                item.widget().deleteLater()
        
        # Add new fields
        for key, value in extra_fields.items():
            field_widget = QWidget()
            field_layout = QHBoxLayout(field_widget)
            field_layout.setContentsMargins(0, 2, 0, 2)
            
            key_label = QLabel(f"{key}:")
            key_label.setStyleSheet("color: #aaaaaa; font-weight: bold;")
            key_label.setFixedWidth(120)
            field_layout.addWidget(key_label)
            
            value_label = QLabel(str(value))
            value_label.setStyleSheet("color: #4FC3F7;")
            field_layout.addWidget(value_label)
            
            field_layout.addStretch()
            ui["extra_fields_layout"].addWidget(field_widget)
    
    def update_events_table(self, station_id: str):
        """Update events table for specific station - FIXED DONE latching timing"""
        if station_id not in self.station_ui:
            return
            
        ui = self.station_ui[station_id]
        table = ui["events_table"]
        
        # Clear table
        table.setRowCount(0)
        
        # Add recent events with DONE latching using VSI time
        events = list(self.recent_events[station_id])
        done_latch_ns = DONE_LATCH_MS * 1_000_000
        
        for event in events:
            row = table.rowCount()
            table.insertRow(row)
            
            # Format time
            time_str = datetime.fromtimestamp(event.t_ns / 1e9).strftime("%H:%M:%S.%f")[:-3]
            
            # Determine state with DONE latching using VSI timestamps
            # Use current_time_ns (VSI time) for latching calculation
            current_vsi_time = self.current_time_ns
            time_since_done = current_vsi_time - event.t_ns
            
            # Check if this event should be shown as DONE due to latching
            show_done = event.done and time_since_done < done_latch_ns
            
            # Apply state priority: FAULT > DONE (latched) > BUSY > READY > IDLE
            if event.fault:
                state = "FAULT"
            elif show_done:
                state = "DONE"
            elif event.busy:
                state = "BUSY"
            elif event.ready:
                state = "READY"
            else:
                state = "IDLE"
            
            # Format cycle time
            cycle_time = f"{event.cycle_time_ms:.1f}" if event.cycle_time_ms else ""
            
            # Format extra fields
            extra = json.dumps(event.extra) if event.extra else ""
            
            # Add items
            table.setItem(row, 0, QTableWidgetItem(time_str))
            table.setItem(row, 1, QTableWidgetItem(state))
            table.setItem(row, 2, QTableWidgetItem(cycle_time))
            table.setItem(row, 3, QTableWidgetItem(extra))
    
    def update_charts(self):
        """Update all charts"""
        if not self.kpi_history:
            return
        
        latest_snapshot = self.kpi_history[-1]
        
        # Update ALL view charts
        if self.stacked_widget.currentWidget() == self.all_view:
            self.update_all_charts()
        
        # Update station view charts if applicable
        for station_id, view in self.station_views.items():
            if view == self.stacked_widget.currentWidget():
                self.update_station_charts(station_id)
                break
    
    def update_all_charts(self):
        """Update charts in ALL view"""
        if len(self.kpi_history) < 2:
            return
        
        try:
            # Prepare data
            times = [s.timestamp_s for s in self.kpi_history]
            throughputs = [s.throughput_ph for s in self.kpi_history]
            
            # Get latest cycle times
            latest = self.kpi_history[-1]
            station_names = list(STATIONS.keys())
            cycle_times = [latest.avg_cycle_times.get(st, 0.0) for st in station_names]
            utilizations = [latest.station_utilization.get(st, 0.0) for st in station_names]
            
            # Generate chart data based on backend
            if CHART_BACKEND == "plotly_webengine":
                # Plotly format
                throughput_data, throughput_layout = self.chart_manager.create_throughput_chart_data(times, throughputs)
                cycle_data, cycle_layout = self.chart_manager.create_cycle_time_chart_data(station_names, cycle_times)
                util_data, util_layout = self.chart_manager.create_utilization_chart_data(station_names, utilizations)
                pass_reject_data, pass_reject_layout = self.chart_manager.create_pass_reject_chart_data(
                    latest.total_completed, latest.total_rejected
                )
                
                # Update charts
                self.throughput_chart.update_chart(throughput_data, throughput_layout)
                self.cycle_time_chart.update_chart(cycle_data, cycle_layout)
                self.utilization_chart.update_chart(util_data, util_layout)
                self.pass_reject_chart.update_chart(pass_reject_data, pass_reject_layout)
            else:
                # Fallback format
                throughput_data = self.chart_manager.create_throughput_chart_data(times, throughputs)
                cycle_data = self.chart_manager.create_cycle_time_chart_data(station_names, cycle_times)
                util_data = self.chart_manager.create_utilization_chart_data(station_names, utilizations)
                pass_reject_data = self.chart_manager.create_pass_reject_chart_data(
                    latest.total_completed, latest.total_rejected
                )
                
                # Update charts
                self.throughput_chart.update_chart(throughput_data)
                self.cycle_time_chart.update_chart(cycle_data)
                self.utilization_chart.update_chart(util_data)
                self.pass_reject_chart.update_chart(pass_reject_data)
            
        except Exception as e:
            print(f"Error updating charts: {e}")
            import traceback
            traceback.print_exc()
    
    def update_station_charts(self, station_id: str):
        """Update charts in station view"""
        if len(self.kpi_history) < 2:
            return
        
        if station_id not in self.station_ui:
            return
            
        ui = self.station_ui[station_id]
        
        try:
            # Prepare data for this station
            times = [s.timestamp_s for s in self.kpi_history]
            cycle_times = []
            busy_percent = []
            idle_percent = []
            
            for snapshot in self.kpi_history:
                # Cycle time
                ct = snapshot.avg_cycle_times.get(station_id, 0.0)
                cycle_times.append(ct)
                
                # Busy/Idle percentage
                util = snapshot.station_utilization.get(station_id, 0.0)
                busy_percent.append(util)
                idle_percent.append(100 - util)
            
            # Create cycle time trend data for all stations (for comparison)
            all_cycle_data = {}
            for st_id in STATIONS.keys():
                st_cycle_times = []
                for snapshot in self.kpi_history:
                    ct = snapshot.avg_cycle_times.get(st_id, 0.0)
                    st_cycle_times.append(ct)
                all_cycle_data[st_id] = st_cycle_times
            
            # For busy/idle chart, use latest snapshot for all stations
            latest = self.kpi_history[-1]
            all_station_names = list(STATIONS.keys())
            all_busy_percent = [latest.station_utilization.get(st, 0.0) for st in all_station_names]
            all_idle_percent = [100 - p for p in all_busy_percent]
            
            # Generate charts based on backend
            if CHART_BACKEND == "plotly_webengine":
                # Plotly format
                cycle_trend_data, cycle_trend_layout = self.chart_manager.create_station_cycle_trend_data(times, all_cycle_data)
                busy_idle_data, busy_idle_layout = self.chart_manager.create_busy_idle_chart_data(
                    all_station_names, all_busy_percent, all_idle_percent
                )
                
                # Update charts
                ui["cycle_trend_chart"].update_chart(cycle_trend_data, cycle_trend_layout)
                ui["busy_idle_chart"].update_chart(busy_idle_data, busy_idle_layout)
            else:
                # Fallback format
                cycle_trend_data = self.chart_manager.create_station_cycle_trend_data(times, all_cycle_data)
                busy_idle_data = self.chart_manager.create_busy_idle_chart_data(
                    all_station_names, all_busy_percent, all_idle_percent
                )
                
                # Update charts
                ui["cycle_trend_chart"].update_chart(cycle_trend_data)
                ui["busy_idle_chart"].update_chart(busy_idle_data)
            
        except Exception as e:
            print(f"Error updating station charts for {station_id}: {e}")
            import traceback
            traceback.print_exc()
    
    def switch_view(self, view_name: str):
        """Switch between views"""
        if view_name == "ALL":
            self.stacked_widget.setCurrentWidget(self.all_view)
        elif view_name in self.station_views:
            self.stacked_widget.setCurrentWidget(self.station_views[view_name])
        
        # Update navigation button styles
        for name, button in self.nav_buttons.items():
            if name == view_name:
                button.setStyleSheet("""
                    QPushButton {
                        background-color: #3a4a5a;
                        color: #4FC3F7;
                        border-left: 3px solid #4FC3F7;
                    }
                """)
            else:
                button.setStyleSheet("""
                    QPushButton {
                        background-color: #3a3a4a;
                        color: #cccccc;
                        border: none;
                    }
                """)
    
    def on_live_toggled(self, state):
        """Handle LIVE/REPLAY toggle"""
        self.is_live_mode = state == Qt.Checked
        
        if self.is_live_mode:
            self.switch_to_live()
        else:
            self.switch_to_replay()
    
    def toggle_play(self):
        """Toggle play/pause in REPLAY mode"""
        if not self.is_live_mode:
            self.is_playing = not self.is_playing
            self.play_button.setText("▶" if not self.is_playing else "⏸")
    
    def on_speed_changed(self, index):
        """Handle speed combo box change"""
        speeds = [0.5, 1.0, 2.0, 5.0]
        if 0 <= index < len(speeds):
            self.playback_speed = speeds[index]
    
    def on_timeline_changed(self, value):
        """Handle timeline slider change"""
        if not self.is_live_mode and self.replay_events:
            time_range = self.replay_max_time - self.replay_min_time
            if time_range > 0:
                self.current_time_ns = self.replay_min_time + int(time_range * value / 1000)
                self.update_time_label()
                
                # Update KPIs based on current time
                self.update_replay_state()
    
    def update_time_label(self):
        """Update the time display label"""
        if self.is_live_mode:
            self.time_label.setText("LIVE")
        else:
            time_s = (self.current_time_ns - self.replay_min_time) / 1e9
            total_s = (self.replay_max_time - self.replay_min_time) / 1e9
            minutes = int(time_s // 60)
            seconds = time_s % 60
            self.time_label.setText(f"{minutes:02d}:{seconds:06.3f}")
    
    def update_replay_state(self):
        """Update state based on current replay time - IMPROVED incremental processing"""
        if not self.replay_events:
            return
        
        # Check if moving forward or backward
        if self.current_time_ns < self.last_replay_time:
            # Moving backward - reset and replay from beginning
            self.kpi_calculator.reset()
            self.replay_cursors = {station_id: 0 for station_id in self.replay_events.keys()}
            
            # Clear recent events
            for station_id in STATIONS.keys():
                self.recent_events[station_id].clear()
        
        # Process events for each station up to current time
        for station_id, events in self.replay_events.items():
            if not events:
                continue
                
            # Get current cursor
            cursor = self.replay_cursors.get(station_id, 0)
            
            # Find events up to current time
            while cursor < len(events) and events[cursor].t_ns <= self.current_time_ns:
                event = events[cursor]
                self.kpi_calculator.process_event(event)
                
                # Store in recent events
                self.recent_events[station_id].append(event)
                
                cursor += 1
            
            # Update cursor
            self.replay_cursors[station_id] = cursor
        
        # Update last replay time
        self.last_replay_time = self.current_time_ns
        
        # Update UI if a station view is active
        current_view = self.stacked_widget.currentWidget()
        if current_view != self.all_view:
            for station_id, view in self.station_views.items():
                if view == current_view:
                    # Update events table for active station
                    self.update_events_table(station_id)
                    break
    
    def on_activity_detected(self, station_id: str):
        """Handle activity detection"""
        # Update status
        self.status_label.setText("● ACTIVE")
        self.status_label.setStyleSheet("color: #4CAF50;")
    
    def update_ui(self):
        """Update UI elements"""
        # Update replay if playing
        if not self.is_live_mode and self.is_playing and self.replay_events:
            # Advance time based on current speed
            time_delta_ns = int(33_333_333 * self.playback_speed)  # 33ms base * speed
            self.current_time_ns += time_delta_ns
            
            # Check bounds
            if self.current_time_ns > self.replay_max_time:
                self.current_time_ns = self.replay_max_time
                self.is_playing = False
                self.play_button.setText("▶")
            
            # Update slider
            time_range = self.replay_max_time - self.replay_min_time
            if time_range > 0:
                slider_value = int((self.current_time_ns - self.replay_min_time) * 1000 / time_range)
                self.timeline_slider.blockSignals(True)
                self.timeline_slider.setValue(slider_value)
                self.timeline_slider.blockSignals(False)
            
            self.update_time_label()
            self.update_replay_state()
    
    def _stop_all_workers(self):
        """Stop all tail workers"""
        for station_id, worker in list(self.tail_workers.items()):
            worker.stop()
            if worker.isRunning():
                worker.wait()
        self.tail_workers.clear()
    
    def closeEvent(self, event):
        """Handle window close event"""
        # Stop all workers
        self._stop_all_workers()
        
        # Stop timers
        self.ui_timer.stop()
        self.chart_timer.stop()
        
        event.accept()

# ===== MAIN APPLICATION =====
def main():
    """Main application entry point"""
    app = QApplication(sys.argv)
    
    # Set application name
    app.setApplicationName("Production Line KPI Dashboard")
    app.setOrganizationName("DeepSeek Engineering")
    
    # Check for required packages
    if not PLOTLY_AVAILABLE:
        print("ERROR: plotly is not available")
        print("\nInstall with: pip install plotly")
        return 1
    
    # Create and show main window
    window = KpiDashboard()
    window.show()
    
    # Start application
    return app.exec()

if __name__ == "__main__":
    sys.exit(main())