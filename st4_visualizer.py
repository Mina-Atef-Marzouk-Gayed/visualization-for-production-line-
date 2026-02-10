#!/usr/bin/env python3
"""
ST4 Calibration & Testing Visualizer
Enhanced with minimal 3D scene and view toggles
"""

# ===== ENVIRONMENT SETUP =====
import sys
import os
import re
import time
import math
import traceback
import collections
import copy
from typing import *
from dataclasses import dataclass, field
from datetime import datetime

# Add user site-packages to sys.path for PySide6
import site
user_site = site.getusersitepackages()
if user_site not in sys.path:
    sys.path.insert(0, user_site)

# ===== THEME CONSTANTS =====
# UI Colors (Dark Theme)
UI_BG = "#1e1e1e"
UI_PANEL_BG = "#252526"
UI_TEXT = "#d4d4d4"
UI_MUTED = "#858585"
UI_GREEN = "#4ec9b0"
UI_YELLOW = "#dcdcaa"
UI_RED = "#f48771"
UI_BLUE = "#9cdcfe"
UI_ACCENT = "#007acc"
UI_SUCCESS = "#6a9955"
UI_WARNING = "#ce9178"
UI_ERROR = "#f14c4c"

# GL Scene Colors
GL_BG_TOP = (0.1, 0.1, 0.15, 1.0)
GL_BG_BOTTOM = (0.05, 0.05, 0.08, 1.0)
GL_GRID = (0.2, 0.2, 0.25, 1.0)
GL_GRID_FADE = (0.15, 0.15, 0.2, 0.3)
GL_STATION_FRAME = (0.3, 0.3, 0.35, 1.0)
GL_PLATFORM = (0.25, 0.25, 0.3, 1.0)
GL_SAMPLE = (0.0, 0.6, 0.8, 1.0)
GL_PRINTER = (0.8, 0.3, 0.1, 1.0)
GL_HEATER_GLOW = (1.0, 0.5, 0.2, 1.0)
GL_PROBE = (0.0, 0.8, 0.4, 1.0)
GL_PASS = (0.0, 0.8, 0.0, 1.0)
GL_FAIL = (0.8, 0.0, 0.0, 1.0)
GL_STAGE_INDICATOR = (0.9, 0.6, 0.1, 1.0)
GL_RAIL = (0.4, 0.4, 0.45, 1.0)
GL_POST = (0.35, 0.35, 0.4, 1.0)

# ===== CONFIGURATION =====
def find_project_root(start_dir: str) -> str:
    start_dir = os.path.abspath(start_dir)
    markers = ["pythonGateways", "logs", "data", ".git"]
    cur = start_dir
    for _ in range(8):
        if any(os.path.exists(os.path.join(cur, m)) for m in markers):
            return cur
        parent = os.path.dirname(cur)
        if parent == cur:
            break
        cur = parent
    return os.path.abspath(os.path.join(start_dir, ".."))

SCRIPT_DIR = os.path.dirname(__file__)
PROJECT_ROOT = find_project_root(SCRIPT_DIR)
SEARCH_ROOTS = []
# always include project root and current working dir
for r in [PROJECT_ROOT, os.getcwd()]:
    rr = os.path.abspath(r)
    if rr not in SEARCH_ROOTS:
        SEARCH_ROOTS.append(rr)

MAX_EVENTS = 50000
TIMER_FPS = 30
DONE_PULSE_MS = 300
OPENGL_MAJOR_VERSION = 2
OPENGL_MINOR_VERSION = 1
USE_PYOPENGL = True
SNAPSHOT_LINES = 3000
IDLE_TIMEOUT = 5.0  # seconds
LONG_IDLE_TIMEOUT = 15.0  # seconds for "STOPPED?" message
AUTO_SWITCH_ON_IDLE = False  # Whether to auto-switch to replay when idle

# Priority keys for display (shown first)
PRIORITY_EXTRA_KEYS = ['completed', 'total', 'cycle_time_ms', 'pass_count', 'last_result']

# ===== QT IMPORTS =====
try:
    from PySide6.QtWidgets import *
    from PySide6.QtCore import *
    from PySide6.QtGui import QSurfaceFormat, QPainter, QColor, QFont, QPen, QFontMetrics, QBrush, QLinearGradient
    from PySide6.QtOpenGLWidgets import QOpenGLWidget
    QT_AVAILABLE = True
except Exception as e:
    print(f"ERROR importing PySide6: {e}")
    print("Python executable:", sys.executable)
    print("Python path (first 5 entries):")
    for i, path in enumerate(sys.path[:5]):
        print(f"  {i}: {path}")
    print("\nFull traceback:")
    traceback.print_exc()
    print("\nERROR: PySide6 not installed. Install with: pip install PySide6")
    sys.exit(1)

# ===== OPENGL IMPORTS =====
if USE_PYOPENGL:
    try:
        from OpenGL.GL import *
        from OpenGL.GLU import *
        PYOPENGL_AVAILABLE = True
    except ImportError:
        PYOPENGL_AVAILABLE = False
        print("WARNING: PyOpenGL not installed. Using basic rendering.")
        print("For better graphics: pip install PyOpenGL")
else:
    PYOPENGL_AVAILABLE = False

# ===== DATA MODEL =====
@dataclass
class ST4Event:
    t_ns: int
    ready: bool = False
    busy: bool = False
    done: bool = False
    fault: bool = False
    cycle_time_ms: Optional[float] = None
    extra: Dict[str, Any] = field(default_factory=dict)

# ===== CARRY-FORWARD PARSER (ST4 SPECIFIC) =====
class ST4LogParser:
    """Carry-forward parser for ST4 Calibration & Testing logs"""
    
    def __init__(self):
        self.reset()
    
    def reset(self):
        """Reset parser state"""
        self.last_vsi_time_ns = None
        self.synthetic_time_ns = 0
        self.last_emitted_ts = None
    
        # Track SimPy time to advance timestamps by delta
        self.last_simpy_s = None
        self.seen_vsi_time = False  # have we ever seen a real VSI time line?
    
        # Carry-forward state
        self.carried_state = {'ready': None, 'busy': None, 'done': None, 'fault': None}
        self.carried_cycle_time = None
        self.carried_extra = {}
        self.has_seen_any_state = False
        self.in_outputs_section = False
        self.in_inputs_section = False
    
        # ST4-specific patterns
        # VSI time (same as ST3)
        self.vsi_time_pattern = re.compile(r"VSI\s+time\s*:\s*(\d+)\s*ns", re.IGNORECASE)
        
        # SimPy env.now - multiple formats for ST4
        # Format 1: "env.now=24.000s" (from SimState or step lines)
        # Format 2: "SimPy env.now = 24.000s" (old format)
        self.simpy_now_pattern = re.compile(
            r"(?:env\.now\s*=|SimPy\s+env\.now\s*=)\s*([\d.]+)\s*s", 
            re.IGNORECASE
        )
        
        # Time advanced with delta (ST4 specific)
        self.time_advanced_pattern = re.compile(
            r"env\.now\s*=\s*([\d.]+)s,\s*dt_s\s*=\s*[\d.]+s", 
            re.IGNORECASE
        )
        
        # SimState line (ST4 specific)
        self.simstate_pattern = re.compile(
            r"SimState:.*env\.now\s*=\s*([\d.]+)s", 
            re.IGNORECASE
        )
    
        # Boolean state updates (numeric or True/False)
        self.bool_state_inline = {
            "busy": re.compile(r"\bbusy\s*=\s*(True|False|\d+)\b", re.IGNORECASE),
            "ready": re.compile(r"\bready\s*=\s*(True|False|\d+)\b", re.IGNORECASE),
            "done": re.compile(r"\bdone\s*=\s*(True|False|\d+)\b", re.IGNORECASE),
            "fault": re.compile(r"\bfault\s*=\s*(True|False|\d+)\b", re.IGNORECASE),
        }
    
        # ST4 cycle time patterns
        self.cycle_time_patterns = [
            re.compile(r"cycle[_\s]*time[_\s]*[:=]?\s*([\d.]+)\s*ms", re.IGNORECASE),
            re.compile(r"cycle_time_ms[_\s]*[:=]?\s*([\d.]+)", re.IGNORECASE),
        ]
    
        # Key-value pattern for extras (ST4 specific)
        self.key_value_pattern = re.compile(r"(\w+)\s*=\s*([\w.-]+)")
    
        # State patterns (numeric only)
        self.state_patterns = {
            "ready": re.compile(r"\bready\b\s*=\s*(\d+)", re.IGNORECASE),
            "busy": re.compile(r"\bbusy\b\s*=\s*(\d+)", re.IGNORECASE),
            "done": re.compile(r"\bdone\b\s*=\s*(\d+)", re.IGNORECASE),
            "fault": re.compile(r"\bfault\b\s*=\s*(\d+)", re.IGNORECASE),
        }
    
        # ST4 block patterns
        self.block_start_pattern = re.compile(r"^\+=.*ST4_CalibrationTesting.*=\+$", re.IGNORECASE)
        self.block_end_pattern = re.compile(r"^=\+=$")
        self.outputs_section_pattern = re.compile(r"^\s*Outputs:", re.IGNORECASE)
        self.inputs_section_pattern = re.compile(r"^\s*Inputs:", re.IGNORECASE)
    
    def seed_from_event(self, event: ST4Event):
        """Seed the parser with an existing event to establish carried state"""
        self.carried_state = {
            'ready': 1 if event.ready else 0,
            'busy': 1 if event.busy else 0,
            'done': 1 if event.done else 0,
            'fault': 1 if event.fault else 0
        }
        self.carried_cycle_time = event.cycle_time_ms
        self.carried_extra = copy.deepcopy(event.extra)
        self.has_seen_any_state = True
        self.last_vsi_time_ns = event.t_ns
        self.synthetic_time_ns = event.t_ns
        self.last_emitted_ts = event.t_ns
    
    def _is_valid_extra_key(self, key: str) -> bool:
        """Filter extra keys to avoid garbage"""
        # Reject keys that are only digits
        if key.isdigit():
            return False
        
        # Reject keys shorter than 2 characters
        if len(key) < 2:
            return False
        
        # Reject keys that look like garbage (containing strange characters)
        if not re.match(r'^[a-zA-Z_][a-zA-Z0-9_]*$', key):
            return False
        
        # Default: accept if looks reasonable
        return len(key) <= 30  # Max reasonable key length
    
    def parse_line(self, line: str) -> Optional[ST4Event]:
        line = line.strip()
        if not line:
            return None
    
        had_signal = False
    
        # ST4 section tracking
        if self.block_start_pattern.match(line):
            self.in_outputs_section = False
            self.in_inputs_section = False
        elif self.block_end_pattern.match(line):
            self.in_outputs_section = False
            self.in_inputs_section = False
        elif self.outputs_section_pattern.match(line):
            self.in_outputs_section = True
            self.in_inputs_section = False
        elif self.inputs_section_pattern.match(line):
            self.in_inputs_section = True
            self.in_outputs_section = False
    
        # ---- helper: advance timestamp using SimPy time safely ----
        def apply_simpy_time(simpy_s: float):
            nonlocal had_signal
            self.carried_extra['simpy_now_s'] = simpy_s
            had_signal = True
    
            if self.last_simpy_s is None:
                self.last_simpy_s = simpy_s
                if self.last_vsi_time_ns is None:
                    self.last_vsi_time_ns = int(simpy_s * 1e9)
                return
    
            delta_s = simpy_s - self.last_simpy_s
            self.last_simpy_s = simpy_s
    
            if delta_s < 0:
                delta_s = 0.0
    
            delta_ns = int(delta_s * 1e9)
            if delta_ns <= 0:
                delta_ns = 1
    
            if self.last_vsi_time_ns is None:
                self.last_vsi_time_ns = int(simpy_s * 1e9)
            elif self.seen_vsi_time:
                # IMPORTANT: if VSI time was epoch-like, don't compare with simpy_ns. just advance by delta.
                self.last_vsi_time_ns += delta_ns
            else:
                # if we never saw VSI time, we can treat it like simpy_ns
                self.last_vsi_time_ns = max(self.last_vsi_time_ns, int(simpy_s * 1e9))
    
        # ---- VSI time ----
        vsi_match = self.vsi_time_pattern.search(line)
        if vsi_match:
            self.last_vsi_time_ns = int(vsi_match.group(1))
            self.seen_vsi_time = True
            if self.has_seen_any_state:
                had_signal = True
    
        # ---- SimPy env.now (multiple formats) ----
        simpy_match = self.simpy_now_pattern.search(line)
        if simpy_match:
            try:
                apply_simpy_time(float(simpy_match.group(1)))
            except ValueError:
                pass
    
        # ---- Time advanced (ST4 specific format) ----
        time_advanced_match = self.time_advanced_pattern.search(line)
        if time_advanced_match:
            try:
                apply_simpy_time(float(time_advanced_match.group(1)))
            except ValueError:
                pass
        
        # ---- SimState line (ST4 specific) ----
        simstate_match = self.simstate_pattern.search(line)
        if simstate_match:
            try:
                apply_simpy_time(float(simstate_match.group(1)))
            except ValueError:
                pass
    
        # ---- numeric state updates ----
        for state_name, pattern in self.state_patterns.items():
            match = pattern.search(line)
            if match:
                try:
                    value = int(match.group(1))
                    self.carried_state[state_name] = value
                    self.has_seen_any_state = True
                    had_signal = True
                except ValueError:
                    pass
    
        # ---- inline bool/numeric state updates ----
        for state_name, pattern in self.bool_state_inline.items():
            match = pattern.search(line)
            if match:
                val_str = match.group(1).lower()
                if val_str in ['true', 'false']:
                    value = 1 if val_str == 'true' else 0
                else:
                    try:
                        value = int(val_str)
                    except ValueError:
                        continue
                
                self.carried_state[state_name] = value
                self.has_seen_any_state = True
                had_signal = True
    
        # ---- cycle time ----
        for pattern in self.cycle_time_patterns:
            match = pattern.search(line)
            if match:
                try:
                    self.carried_cycle_time = float(match.group(1))
                    had_signal = True
                    break
                except ValueError:
                    pass
    
        # ---- Inputs section: batch_id, recipe_id ----
        if self.in_inputs_section:
            for match in self.key_value_pattern.finditer(line):
                key, value = match.groups()
                k = key.lower()
                
                if k in ['batch_id', 'recipe_id', 'total']:
                    try:
                        v = float(value) if '.' in value else int(value)
                    except ValueError:
                        v = value
                    
                    self.carried_extra[key] = v
                    had_signal = True
    
        # ---- Outputs section: extras including ST4-specific signals ----
        if self.in_outputs_section:
            current_line_extras = {}
            for match in self.key_value_pattern.finditer(line):
                key, value = match.groups()
                k = key.lower()
        
                # convert value first
                try:
                    v = float(value) if '.' in value else int(value)
                except ValueError:
                    v = value
        
                # If the log gives SimPy time as a key-value, advance timestamp from it
                if k in ("simpy_now_s", "simpy_now", "simpy_s"):
                    try:
                        apply_simpy_time(float(v))
                    except Exception:
                        pass
                    current_line_extras[key] = v
                    continue
        
                # Filter out system keys
                if k in ['vsi', 'time', 'cycle', 'ready', 'busy', 'done', 'fault', 'simpy', 'env']:
                    continue
                if 'cycle_time' in k:
                    continue
                if not self._is_valid_extra_key(key):
                    continue
        
                # ST4-specific extras: total, completed
                # These are required signals for ST4
                current_line_extras[key] = v
        
            if current_line_extras:
                self.carried_extra.update(current_line_extras)
                had_signal = True
        
        # ---- choose timestamp ----
        if self.last_vsi_time_ns is not None:
            timestamp = self.last_vsi_time_ns
        else:
            self.synthetic_time_ns += 10_000_000
            timestamp = self.synthetic_time_ns
    
        # ---- emit heartbeat/state event ----
        if not had_signal:
            return None
    
        # enforce strictly increasing timestamps to avoid "flatline" replay
        if self.last_emitted_ts is not None and timestamp <= self.last_emitted_ts:
            timestamp = self.last_emitted_ts + 1
    
        self.last_emitted_ts = timestamp
    
        ready = bool(self.carried_state['ready']) if self.carried_state['ready'] is not None else False
        busy  = bool(self.carried_state['busy'])  if self.carried_state['busy']  is not None else False
        done  = bool(self.carried_state['done'])  if self.carried_state['done']  is not None else False
        fault = bool(self.carried_state['fault']) if self.carried_state['fault'] is not None else False
    
        return ST4Event(
            t_ns=timestamp,
            ready=ready,
            busy=busy,
            done=done,
            fault=fault,
            cycle_time_ms=self.carried_cycle_time,
            extra=copy.deepcopy(self.carried_extra)
        )
    
    def get_current_state(self) -> Optional[ST4Event]:
        """Get current state without parsing a line"""
        if not self.has_seen_any_state and self.carried_cycle_time is None and not self.carried_extra:
            return None
        
        # Determine timestamp
        if self.last_vsi_time_ns is not None:
            timestamp = self.last_vsi_time_ns
        else:
            timestamp = self.synthetic_time_ns
        
        # Convert carried state to booleans
        ready = bool(self.carried_state['ready']) if self.carried_state['ready'] is not None else False
        busy = bool(self.carried_state['busy']) if self.carried_state['busy'] is not None else False
        done = bool(self.carried_state['done']) if self.carried_state['done'] is not None else False
        fault = bool(self.carried_state['fault']) if self.carried_state['fault'] is not None else False
        
        return ST4Event(
            t_ns=timestamp,
            ready=ready,
            busy=busy,
            done=done,
            fault=fault,
            cycle_time_ms=self.carried_cycle_time,
            extra=copy.deepcopy(self.carried_extra)
        )

# ===== LOG DISCOVERY (ST4 SPECIFIC) =====
class LogDiscoverer:
    """Finds ST4 Calibration & Testing logs with priority for check.ST4_CalibrationTesting.log"""
    
    @staticmethod
    def find_st4_log() -> Optional[str]:
        candidates = []

        def consider_file(full_path: str, file: str):
            fl = file.lower()

            # Must be a .log file
            if not fl.endswith(".log"):
                return

            # ST4 station markers
            st4_ok = ("st4" in fl) or ("station4" in fl) or ("station_4" in fl) or ("station 4" in fl)
            
            # ST4 process markers: calibration, testing
            process_ok = ("calibrationtesting" in fl) or ("calibration" in fl) or ("testing" in fl)
            
            if not (st4_ok and process_ok):
                return

            try:
                mtime = os.path.getmtime(full_path)
                size = os.path.getsize(full_path)
            except OSError:
                return

            # Score based on filename relevance for ST4
            score = 0
            # Highest priority: exact match check.ST4_CalibrationTesting.log
            if "check.st4_calibrationtesting.log" == fl:
                score += 100
            # High priority: contains ST4 and CalibrationTesting
            if "st4_calibrationtesting" in fl:
                score += 50
            # Medium priority: check.*.log files (real ST4 logs)
            if fl.startswith("check") and st4_ok:
                score += 30
            # ST4 keyword bonuses
            if "calibration" in fl:
                score += 10
            if "testing" in fl:
                score += 10

            # Check file status
            is_check = fl.startswith("check") or fl.startswith("check_") or fl.startswith("check.")

            candidates.append((is_check, score, size, mtime, full_path))

        # Scan all roots
        for root0 in SEARCH_ROOTS:
            for root, dirs, files in os.walk(root0):
                for file in files:
                    consider_file(os.path.join(root, file), file)

        # DEBUG: print what we found
        print(f"[LogDiscoverer] ST4 candidates total = {len(candidates)}")
        
        # Show top 10 by (score,size,mtime) for visibility
        preview = sorted(candidates, key=lambda x: (-x[1], -x[2], -x[3]))[:10]
        for i, (is_check, score, size, mtime, path) in enumerate(preview, 1):
            tag = "CHECK" if is_check else "OTHER"
            print(f"  {i:02d}) {tag} score={score} size={size} mtime={datetime.fromtimestamp(mtime)} path={path}")

        if not candidates:
            return None

        # Sort by score, then size, then mtime (newest first)
        candidates.sort(key=lambda x: (-x[1], -x[2], -x[3]))
        selected = candidates[0][4]
        print(f"Selected ST4 log: {selected}")
        return selected

# ===== TAIL WORKER (SAME AS ST3) =====
class LogTailWorker(QThread):
    new_event = Signal(ST4Event)  # Emitted for every signal line
    activity_detected = Signal()  # Emitted when any line is read
    file_reopened = Signal()  # Emitted when file is reopened (rotation/truncation)
    
    def __init__(self, log_path: str, seed_event: Optional[ST4Event] = None):
        super().__init__()
        self.log_path = log_path
        self.seed_event = seed_event
        self.running = True
        self.file_handle = None
        self.file_position = 0
        self.file_inode = None
        self.parser = ST4LogParser()
        self.last_activity_time = time.time()
        
    def run(self):
        """Tail the log file and emit new events"""
        self._open_file(seed=True)
        
        while self.running:
            try:
                if not self.file_handle:
                    time.sleep(0.1)
                    continue
                
                # Check if file was rotated/truncated
                try:
                    current_size = os.path.getsize(self.log_path)
                    current_inode = os.stat(self.log_path).st_ino
                    
                    # Check for rotation (inode changed) or truncation
                    if current_inode != self.file_inode or current_size < self.file_position:
                        print("File rotated/truncated, reopening...")
                        self._open_file(seed=True)
                        self.file_reopened.emit()
                        continue
                except (OSError, IOError):
                    # File might have been deleted
                    time.sleep(1)
                    continue
                
                # Read new lines
                try:
                    self.file_handle.seek(self.file_position)
                    new_lines = self.file_handle.readlines()
                    self.file_position = self.file_handle.tell()
                except (OSError, IOError) as e:
                    print(f"Error reading file: {e}")
                    self._open_file(seed=True)
                    self.file_reopened.emit()
                    continue
                
                # Parse lines
                if new_lines:
                    self.last_activity_time = time.time()
                    self.activity_detected.emit()
                    
                    for line in new_lines:
                        event = self.parser.parse_line(line)
                        if event:
                            self.new_event.emit(event)
                
                time.sleep(0.05)  # 50ms sleep
                
            except Exception as e:
                print(f"Error in tail worker: {e}")
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
            
            # Get file inode to detect rotation
            self.file_inode = os.stat(self.log_path).st_ino
            
            # Reset parser when file is reopened
            self.parser = ST4LogParser()
            
            # Seed the parser if we have a seed event
            if seed and self.seed_event:
                self.parser.seed_from_event(self.seed_event)
                
        except Exception as e:
            print(f"Error opening {self.log_path}: {e}")
            self.file_handle = None
    
    def reseed_parser(self, seed_event: ST4Event):
        """Reseed the parser with a new event (e.g., after file rotation)"""
        self.seed_event = seed_event
        self.parser.seed_from_event(seed_event)
    
    def stop(self):
        """Stop the worker thread"""
        self.running = False
        if self.isRunning():
            self.wait()

# ===== OPENGL WIDGET (ST4 SPECIFIC VISUALIZATION) =====
class ST4OpenGLWidget(QOpenGLWidget):
    """OpenGL visualization widget for ST4 Calibration & Testing"""
    
    def __init__(self, parent=None):
        super().__init__(parent)
        self.current_state = {
            'ready': False,
            'busy': False,
            'done': False,
            'fault': False,
            'cycle_time_ms': None,
            'extra': {}
        }
        self.animation_time = 0  # Will be set by MainWindow with visual_time_s
        self.done_pulse_time = 0
        self.shake_offset = 0.0
        self.last_completed_count = 0
        self.mode = "LIVE"  # Will be updated by MainWindow
        
        # ST4 stage animation parameters
        self.base_stage_s = 2.5  # Default seconds per stage
        self.stage_s = self.base_stage_s  # Current stage duration
        self.proc_active = False  # Is processing active?
        self.proc_start = 0.0  # When processing started (in visual_time_s)
        self.proc_end = 0.0  # When processing ends (4 stages)
        self.active_stage_index = -1  # -1 means no stage active
        self.stage_progress = 0.0  # Progress within current stage (0.0 to 1.0)
        
        # ST4-specific stage names
        self.stage_names = ["Move to Position", "Thermal Stabilization", "Calibration", "Test Print + Result"]
        
        # Animation data
        self.path_points = []
        self.heat_particles = []
        self.measurement_dots = []
        self.print_pattern_progress = 0.0
        self.gantry_easing = 0.0
        self.orbit_enabled = False
        self.orbit_angle = 0.0
        
        # View toggles
        self.show_environment = True  # Master toggle for grid + frame
        self.show_grid = True         # Show simplified grid
        self.show_frame = False       # Show minimal frame (off by default)
        
        # Camera
        self.camera_distance = 15.0
        self.camera_angle_x = 25.0
        self.camera_angle_y = 35.0
        self.camera_offset_x = 0.0
        self.camera_offset_y = 0.0
        self.last_mouse_pos = None
        self.mouse_panning = False
        
        self.setMouseTracking(True)
    
    def compute_active_stage(self, visual_time_s=None):
        """Compute which ST4 stage is active and its progress based on visual_time_s"""
        if visual_time_s is None:
            visual_time_s = self.animation_time
            
        if not self.proc_active:
            self.active_stage_index = -1
            self.stage_progress = 0.0
            return -1
        
        # If busy but timer ended, stay in stage 4 (Test Print + Result) with looping animation
        if visual_time_s >= self.proc_end:
            if self.current_state['busy']:
                # Stay in stage 4 with looping
                self.active_stage_index = 3
                # Loop every 2 seconds (using visual_time_s for determinism)
                self.stage_progress = (math.sin(visual_time_s * math.pi) * 0.5 + 0.5) * 0.7  # 0.0 to 0.7 range
                return 3
            else:
                self.proc_active = False
                self.active_stage_index = -1
                self.stage_progress = 0.0
                return -1
        
        elapsed = visual_time_s - self.proc_start
        self.active_stage_index = min(3, int(elapsed / self.stage_s))
        
        # Calculate progress within current stage
        stage_start_time = self.proc_start + self.active_stage_index * self.stage_s
        self.stage_progress = min(1.0, max(0.0, (visual_time_s - stage_start_time) / self.stage_s))
        
        return self.active_stage_index
    
    def initializeGL(self):
        if PYOPENGL_AVAILABLE:
            glEnable(GL_DEPTH_TEST)
            glEnable(GL_BLEND)
            glBlendFunc(GL_SRC_ALPHA, GL_ONE_MINUS_SRC_ALPHA)
            glShadeModel(GL_SMOOTH)
            
            # Simple lighting (optional)
            glEnable(GL_LIGHTING)
            glEnable(GL_LIGHT0)
            glLightfv(GL_LIGHT0, GL_POSITION, (5.0, 10.0, 5.0, 1.0))
            glLightfv(GL_LIGHT0, GL_AMBIENT, (0.2, 0.2, 0.2, 1.0))
            glLightfv(GL_LIGHT0, GL_DIFFUSE, (0.8, 0.8, 0.8, 1.0))
            glLightfv(GL_LIGHT0, GL_SPECULAR, (0.3, 0.3, 0.3, 1.0))
            glLightf(GL_LIGHT0, GL_CONSTANT_ATTENUATION, 1.0)
            glLightf(GL_LIGHT0, GL_LINEAR_ATTENUATION, 0.05)
            glLightf(GL_LIGHT0, GL_QUADRATIC_ATTENUATION, 0.001)
            
            glEnable(GL_COLOR_MATERIAL)
            glColorMaterial(GL_FRONT_AND_BACK, GL_AMBIENT_AND_DIFFUSE)
            glMaterialfv(GL_FRONT_AND_BACK, GL_SPECULAR, (0.3, 0.3, 0.3, 1.0))
            glMaterialf(GL_FRONT_AND_BACK, GL_SHININESS, 20.0)
    
    def resizeGL(self, w, h):
        if PYOPENGL_AVAILABLE:
            glViewport(0, 0, w, h)
            glMatrixMode(GL_PROJECTION)
            glLoadIdentity()
            aspect = w / h if h > 0 else 1.0
            gluPerspective(45, aspect, 0.1, 200)
            glMatrixMode(GL_MODELVIEW)
    
    def paintGL(self):
        if not PYOPENGL_AVAILABLE:
            self.paintBasic()
            return
            
        try:
            # Draw gradient background
            self.draw_background_gradient()
            
            glClear(GL_DEPTH_BUFFER_BIT)
            glLoadIdentity()
            
            # Camera positioning with orbit and pan
            if self.orbit_enabled and not self.mouse_panning:
                self.orbit_angle += 0.5
                if self.orbit_angle > 360:
                    self.orbit_angle -= 360
                    
            angle_y = self.camera_angle_y + (self.orbit_angle if self.orbit_enabled and not self.mouse_panning else 0)
            
            cam_x = self.camera_distance * math.cos(math.radians(angle_y)) * math.cos(math.radians(self.camera_angle_x))
            cam_y = self.camera_distance * math.sin(math.radians(self.camera_angle_x))
            cam_z = self.camera_distance * math.sin(math.radians(angle_y)) * math.cos(math.radians(self.camera_angle_x))
            
            gluLookAt(
                cam_x + self.camera_offset_x, cam_y + self.camera_offset_y, cam_z,
                self.camera_offset_x, self.camera_offset_y, 0,
                0, 1, 0
            )
            
            self.draw_scene()
            
            # Draw overlay using QPainter
            painter = QPainter(self)
            painter.setRenderHint(QPainter.Antialiasing)
            self.draw_overlay(painter)
            self.draw_stage_timeline(painter)
            painter.end()
                
        except Exception as e:
            print(f"OpenGL error: {e}")
            traceback.print_exc()
    
    def paintBasic(self):
        """Basic painting when OpenGL is not available"""
        painter = QPainter(self)
        
        # Draw gradient background
        gradient = QLinearGradient(0, 0, 0, self.height())
        gradient.setColorAt(0, QColor(25, 25, 35))
        gradient.setColorAt(1, QColor(10, 10, 15))
        painter.fillRect(self.rect(), gradient)
        
        # Draw overlay
        self.draw_overlay(painter)
        self.draw_stage_timeline(painter)
        painter.end()
    
    def draw_background_gradient(self):
        """Draw a gradient background quad"""
        glDisable(GL_DEPTH_TEST)
        glDisable(GL_LIGHTING)
        
        glMatrixMode(GL_PROJECTION)
        glPushMatrix()
        glLoadIdentity()
        glOrtho(-1, 1, -1, 1, -1, 1)
        
        glMatrixMode(GL_MODELVIEW)
        glPushMatrix()
        glLoadIdentity()
        
        glBegin(GL_QUADS)
        glColor4f(*GL_BG_TOP)  # Top color
        glVertex2f(-1, 1)
        glVertex2f(1, 1)
        glColor4f(*GL_BG_BOTTOM)  # Bottom color
        glVertex2f(1, -1)
        glVertex2f(-1, -1)
        glEnd()
        
        glPopMatrix()
        glMatrixMode(GL_PROJECTION)
        glPopMatrix()
        glMatrixMode(GL_MODELVIEW)
        
        glEnable(GL_DEPTH_TEST)
        glEnable(GL_LIGHTING)
    
    # ===== 3D DRAWING HELPER FUNCTIONS =====
    def draw_box(self, cx, cy, cz, sx, sy, sz, rgba):
        """Draw a box centered at (cx, cy, cz) with size (sx, sy, sz)"""
        if not PYOPENGL_AVAILABLE:
            return
            
        glColor4f(*rgba)
        glBegin(GL_QUADS)
        
        # Front face
        glVertex3f(cx - sx/2, cy - sy/2, cz + sz/2)
        glVertex3f(cx + sx/2, cy - sy/2, cz + sz/2)
        glVertex3f(cx + sx/2, cy + sy/2, cz + sz/2)
        glVertex3f(cx - sx/2, cy + sy/2, cz + sz/2)
        
        # Back face
        glVertex3f(cx - sx/2, cy - sy/2, cz - sz/2)
        glVertex3f(cx - sx/2, cy + sy/2, cz - sz/2)
        glVertex3f(cx + sx/2, cy + sy/2, cz - sz/2)
        glVertex3f(cx + sx/2, cy - sy/2, cz - sz/2)
        
        # Left face
        glVertex3f(cx - sx/2, cy - sy/2, cz - sz/2)
        glVertex3f(cx - sx/2, cy - sy/2, cz + sz/2)
        glVertex3f(cx - sx/2, cy + sy/2, cz + sz/2)
        glVertex3f(cx - sx/2, cy + sy/2, cz - sz/2)
        
        # Right face
        glVertex3f(cx + sx/2, cy - sy/2, cz - sz/2)
        glVertex3f(cx + sx/2, cy + sy/2, cz - sz/2)
        glVertex3f(cx + sx/2, cy + sy/2, cz + sz/2)
        glVertex3f(cx + sx/2, cy - sy/2, cz + sz/2)
        
        # Top face
        glVertex3f(cx - sx/2, cy + sy/2, cz - sz/2)
        glVertex3f(cx - sx/2, cy + sy/2, cz + sz/2)
        glVertex3f(cx + sx/2, cy + sy/2, cz + sz/2)
        glVertex3f(cx + sx/2, cy + sy/2, cz - sz/2)
        
        # Bottom face
        glVertex3f(cx - sx/2, cy - sy/2, cz - sz/2)
        glVertex3f(cx + sx/2, cy - sy/2, cz - sz/2)
        glVertex3f(cx + sx/2, cy - sy/2, cz + sz/2)
        glVertex3f(cx - sx/2, cy - sy/2, cz + sz/2)
        
        glEnd()
    
    def draw_plate(self, cx, cy, cz, sx, sz, thickness, rgba):
        """Draw a flat plate (thin in Y direction)"""
        self.draw_box(cx, cy, cz, sx, thickness, sz, rgba)
    
    def draw_wire_polyline(self, points, progress_0_1, rgba):
        """Draw a wire polyline with partial length based on progress"""
        if not PYOPENGL_AVAILABLE or len(points) < 2:
            return
            
        glColor4f(*rgba)
        glLineWidth(2.0)
        glBegin(GL_LINE_STRIP)
        
        # Calculate total length of polyline
        total_length = 0.0
        segment_lengths = []
        for i in range(len(points) - 1):
            dx = points[i+1][0] - points[i][0]
            dy = points[i+1][1] - points[i][1]
            dz = points[i+1][2] - points[i][2]
            length = math.sqrt(dx*dx + dy*dy + dz*dz)
            segment_lengths.append(length)
            total_length += length
        
        if total_length == 0:
            return
            
        # Draw up to the progress point
        target_length = total_length * progress_0_1
        current_length = 0.0
        
        # Always draw first point
        glVertex3f(*points[0])
        
        for i in range(len(points) - 1):
            segment_len = segment_lengths[i]
            if current_length + segment_len >= target_length:
                # This is the segment where we stop
                remaining = target_length - current_length
                if remaining > 0 and segment_len > 0:
                    t = remaining / segment_len
                    # Interpolate point
                    x = points[i][0] + t * (points[i+1][0] - points[i][0])
                    y = points[i][1] + t * (points[i+1][1] - points[i][1])
                    z = points[i][2] + t * (points[i+1][2] - points[i][2])
                    glVertex3f(x, y, z)
                break
            else:
                # Draw whole segment
                glVertex3f(*points[i+1])
                current_length += segment_len
        
        glEnd()
    
    def draw_cylinder(self, cx, cy, cz, radius, height, rgba, segments=12):
        """Draw a simple cylinder approximation"""
        if not PYOPENGL_AVAILABLE:
            return
            
        glColor4f(*rgba)
        
        # Draw side faces
        glBegin(GL_QUAD_STRIP)
        for i in range(segments + 1):
            angle = 2.0 * math.pi * i / segments
            x = radius * math.cos(angle)
            z = radius * math.sin(angle)
            
            glVertex3f(cx + x, cy - height/2, cz + z)
            glVertex3f(cx + x, cy + height/2, cz + z)
        glEnd()
        
        # Draw top cap
        glBegin(GL_POLYGON)
        for i in range(segments):
            angle = 2.0 * math.pi * i / segments
            x = radius * math.cos(angle)
            z = radius * math.sin(angle)
            glVertex3f(cx + x, cy + height/2, cz + z)
        glEnd()
        
        # Draw bottom cap
        glBegin(GL_POLYGON)
        for i in range(segments):
            angle = 2.0 * math.pi * i / segments
            x = radius * math.cos(angle)
            z = radius * math.sin(angle)
            glVertex3f(cx + x, cy - height/2, cz + z)
        glEnd()
    
    def draw_grid(self):
        """Draw simplified floor grid that fades with distance"""
        if not PYOPENGL_AVAILABLE:
            return
            
        size = 20.0
        steps = 20  # Reduced from 40 to 20 for fewer lines
        
        glDisable(GL_LIGHTING)
        glLineWidth(1.0)  # Thinner lines
        glBegin(GL_LINES)
        
        for i in range(-steps, steps + 1):
            # Draw only major grid lines (every 2nd line)
            if i % 2 != 0:
                continue
                
            x = i * (size / steps)
            # Stronger fade with distance
            dist_factor = min(1.0, abs(x) / (size/2))
            alpha = 0.3 * (1.0 - dist_factor * 0.9)  # Reduced base alpha
            
            glColor4f(GL_GRID[0], GL_GRID[1], GL_GRID[2], alpha * 0.3)
            glVertex3f(x, 0, -size/2)
            glVertex3f(x, 0, size/2)
            
            glVertex3f(-size/2, 0, x)
            glVertex3f(size/2, 0, x)
        
        glEnd()
        glEnable(GL_LIGHTING)
    
    def draw_station_frame(self):
        """Draw minimal station frame: only 4 corner posts"""
        if not PYOPENGL_AVAILABLE:
            return
        
        # Draw thin corner posts only
        post_height = 3.5  # Reduced height
        post_radius = 0.06  # Thinner posts
        
        corners = [
            (-5, 0, -4), (5, 0, -4), (-5, 0, 4), (5, 0, 4)
        ]
        
        for cx, cy, cz in corners:
            self.draw_cylinder(cx, cy + post_height/2, cz, post_radius, post_height, GL_POST)
        
        # Optional: draw a thin top outline frame (wireframe rectangle)
        # This is less dominant than solid rails
        glDisable(GL_LIGHTING)
        glColor4f(0.4, 0.4, 0.45, 0.6)  # Semi-transparent
        glLineWidth(1.0)
        glBegin(GL_LINE_LOOP)
        glVertex3f(-5, post_height, -4)
        glVertex3f(5, post_height, -4)
        glVertex3f(5, post_height, 4)
        glVertex3f(-5, post_height, 4)
        glEnd()
        glEnable(GL_LIGHTING)
    
    def draw_path_line(self):
        """Draw path line for gantry movement"""
        if not PYOPENGL_AVAILABLE or len(self.path_points) < 2:
            return
            
        glDisable(GL_LIGHTING)
        glLineWidth(2.0)
        glBegin(GL_LINE_STRIP)
        
        # Draw path with fading trail
        for i, (x, y, z) in enumerate(self.path_points):
            alpha = i / len(self.path_points)
            glColor4f(GL_PRINTER[0], GL_PRINTER[1], GL_PRINTER[2], 0.3 + 0.7 * alpha)
            glVertex3f(x, y, z)
        
        glEnd()
        
        # Draw dots at key points
        glPointSize(6.0)
        glBegin(GL_POINTS)
        for i, (x, y, z) in enumerate(self.path_points):
            if i % 5 == 0:  # Every 5th point
                alpha = i / len(self.path_points)
                glColor4f(GL_PRINTER[0], GL_PRINTER[1], GL_PRINTER[2], 0.8)
                glVertex3f(x, y, z)
        glEnd()
        
        glEnable(GL_LIGHTING)
    
    def draw_heat_particles(self):
        """Draw rising heat particles"""
        if not PYOPENGL_AVAILABLE:
            return
            
        glDisable(GL_LIGHTING)
        glPointSize(4.0)
        glBegin(GL_POINTS)
        
        for particle in self.heat_particles:
            x, y, z, life = particle
            if life > 0:
                alpha = life
                intensity = 0.5 + 0.5 * math.sin(self.animation_time * 10 + x * 5)
                glColor4f(
                    GL_HEATER_GLOW[0] * intensity,
                    GL_HEATER_GLOW[1] * intensity,
                    GL_HEATER_GLOW[2] * intensity,
                    alpha
                )
                glVertex3f(x, y, z)
        
        glEnd()
        glEnable(GL_LIGHTING)
    
    def draw_measurement_dots(self):
        """Draw measurement dots for calibration stage"""
        if not PYOPENGL_AVAILABLE:
            return
            
        glDisable(GL_LIGHTING)
        glPointSize(8.0)
        glBegin(GL_POINTS)
        
        for dot in self.measurement_dots:
            x, y, z, active = dot
            if active > 0:
                intensity = 0.7 + 0.3 * math.sin(self.animation_time * 5)
                glColor4f(
                    GL_PROBE[0] * intensity,
                    GL_PROBE[1] * intensity,
                    GL_PROBE[2] * intensity,
                    0.8
                )
                glVertex3f(x, y, z)
        
        glEnd()
        glEnable(GL_LIGHTING)
    
    def draw_print_pattern(self):
        """Draw growing print pattern on sample"""
        if not PYOPENGL_AVAILABLE or self.print_pattern_progress <= 0:
            return
            
        glDisable(GL_LIGHTING)
        glLineWidth(2.0)
        
        # Draw concentric squares
        for i in range(1, 6):
            progress = min(1.0, self.print_pattern_progress * 5 - (i-1))
            if progress <= 0:
                continue
                
            size = 0.8 * (i / 5)
            alpha = 0.3 + 0.7 * (i / 5)
            
            glColor4f(GL_PRINTER[0], GL_PRINTER[1], GL_PRINTER[2], alpha)
            glBegin(GL_LINE_LOOP)
            glVertex3f(-size/2, 1.6, -size/2)
            glVertex3f(size/2, 1.6, -size/2)
            glVertex3f(size/2, 1.6, size/2)
            glVertex3f(-size/2, 1.6, size/2)
            glEnd()
        
        glEnable(GL_LIGHTING)
    
    def draw_overlay(self, painter):
        """Draw overlay text with ST4 system information"""
        # Setup fonts
        title_font = QFont("Segoe UI", 12, QFont.Bold)
        normal_font = QFont("Consolas", 10)
        small_font = QFont("Consolas", 9)
        
        # Draw semi-transparent background for text areas
        painter.fillRect(10, 10, 400, 150, QColor(0, 0, 0, 180))
        
        # Mode and state
        painter.setFont(title_font)
        painter.setPen(QPen(QColor(255, 255, 255), 1))
        painter.drawText(15, 30, f"ST4 Calibration & Testing - {self.mode} Mode")
        
        painter.setFont(normal_font)
        painter.setPen(QPen(QColor(200, 200, 200), 1))
        
        # State indicators
        state_x = 15
        state_y = 55
        
        # Ready state
        ready_color = QColor(UI_GREEN if self.current_state['ready'] else UI_MUTED)
        painter.setPen(QPen(ready_color, 1))
        painter.drawText(state_x, state_y, f"Ready: {self.current_state['ready']}")
        
        # Busy state
        busy_color = QColor(UI_YELLOW if self.current_state['busy'] else UI_MUTED)
        painter.setPen(QPen(busy_color, 1))
        painter.drawText(state_x + 100, state_y, f"Busy: {self.current_state['busy']}")
        
        # Done state
        done_color = QColor(UI_GREEN if self.current_state['done'] else UI_MUTED)
        painter.setPen(QPen(done_color, 1))
        painter.drawText(state_x + 200, state_y, f"Done: {self.current_state['done']}")
        
        # Fault state
        fault_color = QColor(UI_RED if self.current_state['fault'] else UI_MUTED)
        painter.setPen(QPen(fault_color, 1))
        painter.drawText(state_x + 300, state_y, f"Fault: {self.current_state['fault']}")
        
        # Cycle time
        painter.setPen(QPen(QColor(200, 200, 200), 1))
        cycle_text = f"Cycle Time: {self.current_state['cycle_time_ms'] or 'N/A'} ms"
        painter.drawText(15, state_y + 25, cycle_text)
        
        # Get current completed count for display
        completed = self.current_state['extra'].get('completed', 0)
        total = self.current_state['extra'].get('total', 0)
        
        # Time display
        painter.setFont(small_font)
        
        # Show both SimPy and VSI times when available
        simpy_time = self.current_state['extra'].get('simpy_now_s')
        vsi_time = self.current_state['extra'].get('vsi_time_ns')
        
        if simpy_time is not None:
            painter.drawText(15, state_y + 45, f"SimPy Time: {simpy_time:.2f}s")
        
        if vsi_time is not None:
            painter.drawText(15, state_y + 60, f"VSI Time: {vsi_time/1e9:.2f}s")
        
        # Completed/Total
        progress_text = f"Progress: {completed}/{total}" if total != 'N/A' else f"Completed: {completed}"
        painter.drawText(15, state_y + 75, progress_text)
    
    def draw_stage_timeline(self, painter):
        """Draw mini stage timeline overlay"""
        timeline_width = 500
        timeline_height = 60
        timeline_x = self.width() - timeline_width - 20
        timeline_y = 20
        
        # Draw background
        painter.fillRect(
            timeline_x - 10, timeline_y - 10,
            timeline_width + 20, timeline_height + 20,
            QColor(0, 0, 0, 200)
        )
        
        # Draw title
        painter.setFont(QFont("Segoe UI", 10, QFont.Bold))
        painter.setPen(QPen(QColor(255, 255, 255), 1))
        painter.drawText(timeline_x, timeline_y - 5, "Stage Timeline")
        
        # Draw stage boxes
        box_width = (timeline_width - 50) // 4
        box_height = 30
        
        for i in range(4):
            box_x = timeline_x + i * (box_width + 10)
            box_y = timeline_y + 10
            
            # Determine box color
            if self.active_stage_index == i:
                box_color = QColor(UI_ACCENT)
                text_color = QColor(255, 255, 255)
            elif self.active_stage_index > i:
                box_color = QColor(UI_SUCCESS)
                text_color = QColor(255, 255, 255)
            else:
                box_color = QColor(60, 60, 70)
                text_color = QColor(150, 150, 150)
            
            # Draw box
            painter.fillRect(box_x, box_y, box_width, box_height, box_color)
            painter.setPen(QPen(QColor(100, 100, 100), 1))
            painter.drawRect(box_x, box_y, box_width, box_height)
            
            # Draw progress fill for active stage
            if self.active_stage_index == i:
                progress_width = int(box_width * self.stage_progress)
                painter.fillRect(box_x, box_y, progress_width, box_height, 
                               QColor(255, 255, 255, 100))
            
            # Draw stage name (abbreviated)
            painter.setFont(QFont("Segoe UI", 8))
            painter.setPen(QPen(text_color, 1))
            
            stage_names_short = ["Move", "Thermal", "Calibrate", "Test"]
            text_rect = painter.boundingRect(box_x, box_y, box_width, box_height,
                                           Qt.AlignCenter, stage_names_short[i])
            painter.drawText(text_rect, Qt.AlignCenter, stage_names_short[i])
            
            # Draw stage number
            painter.setFont(QFont("Segoe UI", 7))
            painter.drawText(box_x + 5, box_y + 12, f"{i+1}")
    
    def draw_scene(self):
        """Draw the 3D scene for ST4 Calibration & Testing"""
        # Draw environment elements based on toggles
        if self.show_environment:
            if self.show_grid:
                self.draw_grid()
            if self.show_frame:
                self.draw_station_frame()
        
        # Apply shake effect if fault
        if self.current_state['fault']:
            self.shake_offset = math.sin(self.animation_time * 10) * 0.1
            glTranslatef(self.shake_offset, 0, 0)
        
        # ===== ALWAYS DRAW CORE GEOMETRY (what matters) =====
        # 1. Base table
        self.draw_plate(0, -0.25, 0, 10, 8, 0.5, GL_PLATFORM)
        
        # 2. Test platform with subtle shading
        glPushMatrix()
        glTranslatef(0, 0.5, 0)
        glScalef(4, 0.5, 3)
        
        # Different face colors for fake shading
        glBegin(GL_QUADS)
        # Front face (brighter)
        glColor4f(GL_PLATFORM[0]*1.2, GL_PLATFORM[1]*1.2, GL_PLATFORM[2]*1.2, 1.0)
        glVertex3f(-0.5, -0.5, 0.5)
        glVertex3f(0.5, -0.5, 0.5)
        glVertex3f(0.5, 0.5, 0.5)
        glVertex3f(-0.5, 0.5, 0.5)
        
        # Back face (darker)
        glColor4f(GL_PLATFORM[0]*0.8, GL_PLATFORM[1]*0.8, GL_PLATFORM[2]*0.8, 1.0)
        glVertex3f(-0.5, -0.5, -0.5)
        glVertex3f(-0.5, 0.5, -0.5)
        glVertex3f(0.5, 0.5, -0.5)
        glVertex3f(0.5, -0.5, -0.5)
        
        # Sides (medium)
        glColor4f(*GL_PLATFORM)
        # Left
        glVertex3f(-0.5, -0.5, -0.5)
        glVertex3f(-0.5, -0.5, 0.5)
        glVertex3f(-0.5, 0.5, 0.5)
        glVertex3f(-0.5, 0.5, -0.5)
        # Right
        glVertex3f(0.5, -0.5, -0.5)
        glVertex3f(0.5, 0.5, -0.5)
        glVertex3f(0.5, 0.5, 0.5)
        glVertex3f(0.5, -0.5, 0.5)
        # Top
        glColor4f(GL_PLATFORM[0]*1.1, GL_PLATFORM[1]*1.1, GL_PLATFORM[2]*1.1, 1.0)
        glVertex3f(-0.5, 0.5, -0.5)
        glVertex3f(-0.5, 0.5, 0.5)
        glVertex3f(0.5, 0.5, 0.5)
        glVertex3f(0.5, 0.5, -0.5)
        # Bottom
        glColor4f(GL_PLATFORM[0]*0.9, GL_PLATFORM[1]*0.9, GL_PLATFORM[2]*0.9, 1.0)
        glVertex3f(-0.5, -0.5, -0.5)
        glVertex3f(0.5, -0.5, -0.5)
        glVertex3f(0.5, -0.5, 0.5)
        glVertex3f(-0.5, -0.5, 0.5)
        glEnd()
        glPopMatrix()
        
        # 3. Printer head gantry (static)
        self.draw_box(0, 3.0, 0, 6, 0.3, 0.2, GL_PRINTER)
        
        # 4. Test sample (always present)
        self.draw_box(0, 1.2, 0, 1.0, 0.8, 0.8, GL_SAMPLE)
        
        # ===== STAGE-BASED ANIMATIONS =====
        self.compute_active_stage(self.animation_time)
        
        if self.active_stage_index == 0:  # Move to Position
            # Easing function for smooth movement
            self.gantry_easing = self.ease_in_out(self.stage_progress)
            
            # Printer head moves to position with easing
            head_x = -2.0 + self.gantry_easing * 4.0  # Move from left to right
            head_y = 3.0
            
            # Update path points
            if len(self.path_points) < 20:
                self.path_points.append((head_x, head_y, 0))
            else:
                self.path_points.pop(0)
                self.path_points.append((head_x, head_y, 0))
            
            # Draw path line
            self.draw_path_line()
            
            # Draw moving printer head
            head_color = (
                GL_PRINTER[0] * (1.0 + 0.3 * math.sin(self.animation_time * 3)),
                GL_PRINTER[1],
                GL_PRINTER[2],
                GL_PRINTER[3]
            )
            self.draw_box(head_x, head_y, 0, 0.5, 0.5, 0.5, head_color)
            
        elif self.active_stage_index == 1:  # Thermal Stabilization
            # Update heat particles
            if len(self.heat_particles) < 50:
                x = -1.5 + 3.0 * (len(self.heat_particles) / 50)
                self.heat_particles.append((x, 1.0, -1.0, 1.0))
            
            # Update particle positions and lifetimes
            for i, particle in enumerate(self.heat_particles):
                x, y, z, life = particle
                y += 0.02 * (1.0 + 0.5 * math.sin(self.animation_time * 2 + i))
                life -= 0.01
                if life <= 0:
                    # Reset particle
                    self.heat_particles[i] = (-1.5 + 3.0 * (i/50), 1.0, -1.0, 1.0)
                else:
                    self.heat_particles[i] = (x, y, z, life)
            
            # Draw heat particles
            self.draw_heat_particles()
            
            # Heater glows with temperature
            heat_intensity = 0.5 + 0.5 * math.sin(self.animation_time * 2)
            heat_color = (
                GL_HEATER_GLOW[0] * heat_intensity,
                GL_HEATER_GLOW[1] * heat_intensity,
                GL_HEATER_GLOW[2] * heat_intensity,
                1.0
            )
            
            # Draw heater elements
            self.draw_box(-1.5, 1.0, -1.0, 0.3, 0.2, 0.3, heat_color)
            self.draw_box(1.5, 1.0, -1.0, 0.3, 0.2, 0.3, heat_color)
            
            # Temperature display
            temp_height = 0.5 + self.stage_progress * 1.0
            self.draw_box(0, 0.5 + temp_height/2, 2.5, 0.5, temp_height, 0.1, 
                         (heat_intensity, 0.2, 0.1, 1.0))
            
        elif self.active_stage_index == 2:  # Calibration
            # Calibration probe moves and takes measurements
            probe_y = 2.0 + 0.3 * math.sin(self.animation_time * 4)
            probe_z = -1.0 + self.stage_progress * 2.0
            
            # Update measurement dots
            if len(self.measurement_dots) < 5:
                x = -2.0 + (len(self.measurement_dots) * 1.0)
                active = 1.0 if self.stage_progress > (len(self.measurement_dots) * 0.2) else 0.0
                self.measurement_dots.append((x, 1.3, 0, active))
            
            # Draw calibration probe
            self.draw_cylinder(0, probe_y, probe_z, 0.1, 0.8, GL_PROBE)
            
            # Draw measurement dots
            self.draw_measurement_dots()
            
        elif self.active_stage_index == 3:  # Test Print + Result
            # Update print pattern progress
            self.print_pattern_progress = self.stage_progress
            
            # Printer head moves and "prints" test pattern
            head_x = math.sin(self.animation_time * 2) * 2.0
            head_z = math.cos(self.animation_time * 2) * 1.0
            
            # Draw moving printer head
            self.draw_box(head_x, 3.0, head_z, 0.5, 0.5, 0.5, GL_PRINTER)
            
            # Draw print pattern
            self.draw_print_pattern()
            
            # Result panel
            if self.stage_progress > 0.7:
                # Determine panel color
                if self.current_state['fault']:
                    panel_color = GL_FAIL
                    result_text = "FAIL"
                elif self.current_state['done']:
                    panel_color = GL_PASS
                    result_text = "PASS"
                else:
                    panel_color = (0.5, 0.5, 0.5, 1.0)
                    result_text = "RUNNING"
                
                # Panel position with slight hover animation
                panel_y = 2.5 + 0.1 * math.sin(self.animation_time * 2)
                self.draw_plate(0, panel_y, -2.5, 1.5, 1.0, 0.05, panel_color)
        
        # Draw done pulse if active
        if self.animation_time - self.done_pulse_time < DONE_PULSE_MS / 1000.0:
            self.draw_done_pulse()
    
    def ease_in_out(self, t):
        """Easing function for smooth animations"""
        return t * t * (3 - 2 * t)
    
    def draw_done_pulse(self):
        """Draw done pulse effect in 3D"""
        if not PYOPENGL_AVAILABLE:
            return
        
        pulse_progress = (self.animation_time - self.done_pulse_time) / (DONE_PULSE_MS / 1000.0)
        pulse_alpha = 1.0 - pulse_progress
        pulse_scale = 1.0 + pulse_progress * 0.5
        
        # Create pulsed color with alpha
        pulsed_color = (0.0, 1.0, 1.0, pulse_alpha)
        
        # Pulse in center
        glPushMatrix()
        glTranslatef(0, 0.5, 0)
        glScalef(pulse_scale * 1.2, pulse_scale * 0.7, pulse_scale * 1.0)
        self.draw_wireframe_cube()
        glPopMatrix()
    
    def draw_wireframe_cube(self):
        """Draw wireframe cube"""
        vertices = [
            (-1, -1, -1), (1, -1, -1), (1, 1, -1), (-1, 1, -1),
            (-1, -1, 1), (1, -1, 1), (1, 1, 1), (-1, 1, 1)
        ]
        
        edges = [
            (0,1), (1,2), (2,3), (3,0),
            (4,5), (5,6), (6,7), (7,4),
            (0,4), (1,5), (2,6), (3,7)
        ]
        
        glDisable(GL_LIGHTING)
        glColor4f(0.0, 1.0, 1.0, 0.5)
        glLineWidth(2.0)
        glBegin(GL_LINES)
        for edge in edges:
            for vertex in edge:
                glVertex3f(*vertices[vertex])
        glEnd()
        glEnable(GL_LIGHTING)
    
    def mousePressEvent(self, event):
        self.last_mouse_pos = event.position()
        if event.button() == Qt.RightButton:
            self.mouse_panning = True
        elif event.button() == Qt.LeftButton:
            self.mouse_panning = False
    
    def mouseMoveEvent(self, event):
        if self.last_mouse_pos:
            dx = event.position().x() - self.last_mouse_pos.x()
            dy = event.position().y() - self.last_mouse_pos.y()
            
            if event.buttons() & Qt.RightButton:
                # Pan camera
                self.camera_offset_x -= dx * 0.01
                self.camera_offset_y += dy * 0.01
            elif event.buttons() & Qt.LeftButton:
                # Rotate camera
                self.camera_angle_y += dx * 0.5
                self.camera_angle_x = max(-90, min(90, self.camera_angle_x - dy * 0.5))
            
            self.last_mouse_pos = event.position()
            self.update()
    
    def mouseReleaseEvent(self, event):
        self.last_mouse_pos = None
        self.mouse_panning = False
    
    def wheelEvent(self, event):
        delta = event.angleDelta().y()
        self.camera_distance = max(5.0, min(30.0, self.camera_distance - delta * 0.01))
        self.update()
    
    def reset_view(self):
        """Reset camera to default position"""
        self.camera_distance = 15.0
        self.camera_angle_x = 25.0
        self.camera_angle_y = 35.0
        self.camera_offset_x = 0.0
        self.camera_offset_y = 0.0
        self.update()
    
    def update_state(self, event: ST4Event, mode: str = "LIVE", event_time_s: float = None):
        """Update the current state from an ST4 event"""
        old_busy = self.current_state.get('busy', False)
        old_done = self.current_state.get('_last_done', False)
        old_completed = self.current_state.get('extra', {}).get('completed', 0)
        
        self.current_state = {
            'ready': event.ready,
            'busy': event.busy,
            'done': event.done,
            'fault': event.fault,
            'cycle_time_ms': event.cycle_time_ms,
            'extra': event.extra
        }
        
        self.mode = mode
        
        # Use provided event_time_s or fallback to current time for LIVE mode
        if event_time_s is None:
            event_time_s = time.time()
        
        # Check for busy rising edge OR if we're not active but should be (mid-cycle attach)
        current_completed = event.extra.get('completed', 0)
        if event.busy and not old_busy:
            # Normal busy rising edge
            self.proc_active = True
            self.proc_start = event_time_s
            
            # Reset animation state
            self.active_stage_index = -1
            self.stage_progress = 0.0
            self.path_points = []
            self.heat_particles = []
            self.measurement_dots = []
            self.print_pattern_progress = 0.0
            
            # Calculate stage duration from cycle_time_ms if available
            if event.cycle_time_ms:
                total_cycle_s = event.cycle_time_ms / 1000.0
                # Divide by 4 stages, clamp to reasonable range (0.5-6.0 seconds per stage)
                calculated_stage_s = total_cycle_s / 4.0
                self.stage_s = max(0.5, min(6.0, calculated_stage_s))
            else:
                self.stage_s = self.base_stage_s
            
            self.proc_end = event_time_s + 4 * self.stage_s  # 4 stages
        
        # Handle case where visualizer attaches mid-cycle (busy already True but not active)
        elif event.busy and not self.proc_active and self.active_stage_index == -1:
            # We missed the busy rising edge, start animation anyway
            self.proc_active = True
            
            # Use cycle time to determine stage duration
            if event.cycle_time_ms:
                total_cycle_s = event.cycle_time_ms / 1000.0
                calculated_stage_s = total_cycle_s / 4.0
                self.stage_s = max(0.5, min(6.0, calculated_stage_s))
            else:
                self.stage_s = self.base_stage_s
            
            # Estimate we're in stage 3 or 4 (Calibration or Test Print) since we're already busy
            # Set proc_start in the past so animation shows active stage
            self.proc_start = event_time_s - 3 * self.stage_s  # Assume we're near the end
            self.proc_end = event_time_s + 1 * self.stage_s  # Extend a bit into the future
            
            print(f"ST4 attached mid-cycle: starting animation at estimated stage 3/4")
        
        # Stop processing on done rising edge OR completed counter increase
        if (event.done and not old_done) or (current_completed > old_completed):
            if event.done and not old_done:
                self.done_pulse_time = event_time_s
            self.proc_active = False
            self.active_stage_index = -1
            self.stage_progress = 0.0
        
        # On fault: stop processing and show FAIL
        if event.fault:
            self.proc_active = False
            self.active_stage_index = -1
            self.stage_progress = 0.0
        
        # Store last done state
        self.current_state['_last_done'] = event.done
        
        self.update()

# ===== MAIN WINDOW =====
class MainWindow(QMainWindow):
    def __init__(self):
        super().__init__()
        self.setWindowTitle("ST4 Calibration & Testing Visualizer")
        self.setGeometry(100, 100, 1400, 900)
        
        # Apply stylesheet
        self.setStyleSheet(self.get_stylesheet())
        
        # Data
        self.log_path = None
        self.replay_events = []
        self.replay_min_time = 0
        self.replay_max_time = 0
        self.current_time_ns = 0
        self.is_live_mode = True
        self.is_playing = True
        self.playback_speed = 1.0
        self.raw_event_count = 0  # All parsed events
        self.accepted_event_count = 0  # Events that actually changed state
        self.last_state_snapshot = None  # For debouncing
        self.last_event_time_ns = 0  # For debug display
        self.last_event_ignored = False  # Track if last event was ignored
        self.last_activity_time = time.time()
        self.is_idle = False
        self.idle_start_time = 0.0
        self.current_mode = "LIVE"  # "LIVE" or "REPLAY"
        self.current_event = None  # Store current event for time display
        
        # Threads
        self.tail_worker = None
        
        # UI
        self.init_ui()
        
        # Timer for animation and replay
        self.timer = QTimer()
        self.timer.timeout.connect(self.update_animation)
        self.timer.start(1000 // TIMER_FPS)
        
        # Initial log discovery
        self.discover_log()
    
    def get_stylesheet(self):
        """Return application stylesheet"""
        return f"""
        QWidget {{
            background-color: {UI_BG};
            color: {UI_TEXT};
            font-family: 'Segoe UI', Arial;
        }}
        
        QGroupBox {{
            font-weight: bold;
            font-size: 11pt;
            border: 2px solid {UI_ACCENT};
            border-radius: 6px;
            margin-top: 10px;
            padding-top: 10px;
            color: {UI_ACCENT};
        }}
        
        QGroupBox::title {{
            subcontrol-origin: margin;
            left: 10px;
            padding: 0 5px 0 5px;
        }}
        
        QPushButton {{
            background-color: {UI_PANEL_BG};
            border: 1px solid {UI_ACCENT};
            border-radius: 4px;
            padding: 6px 12px;
            font-weight: bold;
        }}
        
        QPushButton:hover {{
            background-color: {UI_ACCENT};
            color: white;
        }}
        
        QPushButton:pressed {{
            background-color: #005a9e;
        }}
        
        QPushButton:disabled {{
            background-color: #3c3c3c;
            color: #666666;
            border-color: #555555;
        }}
        
        QProgressBar {{
            border: 1px solid {UI_ACCENT};
            border-radius: 3px;
            text-align: center;
            background-color: {UI_PANEL_BG};
        }}
        
        QProgressBar::chunk {{
            background-color: {UI_ACCENT};
            border-radius: 2px;
        }}
        
        QCheckBox {{
            spacing: 8px;
        }}
        
        QCheckBox::indicator {{
            width: 16px;
            height: 16px;
        }}
        
        QCheckBox::indicator:checked {{
            background-color: {UI_ACCENT};
            border: 2px solid {UI_ACCENT};
            border-radius: 3px;
        }}
        
        QCheckBox::indicator:unchecked {{
            background-color: {UI_PANEL_BG};
            border: 2px solid #555555;
            border-radius: 3px;
        }}
        
        QLabel {{
            color: {UI_TEXT};
        }}
        
        QComboBox {{
            background-color: {UI_PANEL_BG};
            border: 1px solid #555555;
            border-radius: 4px;
            padding: 3px;
        }}
        
        QComboBox:hover {{
            border-color: {UI_ACCENT};
        }}
        
        QSlider::groove:horizontal {{
            border: 1px solid #555555;
            height: 6px;
            background: {UI_PANEL_BG};
            margin: 2px 0;
            border-radius: 3px;
        }}
        
        QSlider::handle:horizontal {{
            background: {UI_ACCENT};
            border: 1px solid #5c5c5c;
            width: 18px;
            margin: -4px 0;
            border-radius: 9px;
        }}
        
        QScrollArea {{
            border: none;
            background-color: {UI_PANEL_BG};
        }}
        
        QScrollBar:vertical {{
            background: {UI_PANEL_BG};
            width: 12px;
            margin: 0;
        }}
        
        QScrollBar::handle:vertical {{
            background: #505050;
            border-radius: 6px;
            min-height: 20px;
        }}
        
        QScrollBar::handle:vertical:hover {{
            background: #606060;
        }}
        """
    
    def get_visual_time_s(self):
        """Get the current visual time in seconds for deterministic animations"""
        if self.is_live_mode:
            # In LIVE mode, use SimPy time if available, otherwise current time
            if self.current_event:
                # Use SimPy time if available in the current event
                simpy_now = self.current_event.extra.get('simpy_now_s')
                if simpy_now is not None:
                    return simpy_now
            # Fallback to wall time for LIVE mode
            return time.time()
        else:
            # In REPLAY mode, find the current event based on current_time_ns
            if not self.replay_events:
                return (self.current_time_ns - self.replay_min_time) / 1e9
            
            current_event = None
            for event in self.replay_events:
                if event.t_ns <= self.current_time_ns:
                    current_event = event
                else:
                    break
            
            if current_event:
                # Use SimPy time if available in the replay event
                simpy_now = current_event.extra.get('simpy_now_s')
                if simpy_now is not None:
                    return simpy_now
            
            # Fallback to VSI time scaled to seconds
            return (self.current_time_ns - self.replay_min_time) / 1e9
    
    def init_ui(self):
        # Central widget
        central_widget = QWidget()
        self.setCentralWidget(central_widget)
        
        # Main layout
        main_layout = QVBoxLayout(central_widget)
        
        # Top info bar with connection status
        info_layout = QHBoxLayout()
        
        # Connection status indicator
        self.connection_status = QLabel("●")
        self.connection_status.setFixedWidth(20)
        self.connection_status.setAlignment(Qt.AlignCenter)
        self.connection_status.setStyleSheet("font-size: 16pt; font-weight: bold;")
        info_layout.addWidget(self.connection_status)
        
        self.log_info_label = QLabel("Searching for ST4 Calibration & Testing log...")
        self.log_info_label.setStyleSheet("font-weight: bold; padding: 5px; font-size: 11pt;")
        info_layout.addWidget(self.log_info_label)
        
        self.event_count_label = QLabel("Raw: 0 | Accepted: 0")
        self.event_count_label.setStyleSheet("font-family: 'Consolas'; padding: 5px;")
        info_layout.addWidget(self.event_count_label)
        
        self.debug_label = QLabel("Mode: LIVE | Last Event: NONE (no parsable state lines yet)")
        self.debug_label.setStyleSheet("font-family: 'Consolas'; padding: 5px; color: #cccccc;")
        info_layout.addWidget(self.debug_label)
        
        info_layout.addStretch()
        main_layout.addLayout(info_layout)
        
        # Center and right panel
        content_layout = QHBoxLayout()
        
        # OpenGL widget (center)
        self.gl_widget = ST4OpenGLWidget()
        content_layout.addWidget(self.gl_widget, 3)
        
        # Status panel (right) inside scroll area
        status_scroll = QScrollArea()
        status_scroll.setWidgetResizable(True)
        status_scroll.setMaximumWidth(400)
        
        status_widget = QWidget()
        status_panel = QVBoxLayout(status_widget)
        
        # Batch/Recipe info
        info_group = QGroupBox("Batch / Recipe Info")
        info_layout = QVBoxLayout()
        
        self.total_label = QLabel("Total: N/A")
        self.completed_label = QLabel("Completed: N/A")
        self.now_label = QLabel("Now: --:--:--")
        
        for label in [self.total_label, self.completed_label, self.now_label]:
            label.setStyleSheet("font-family: 'Consolas'; padding: 4px; font-size: 10pt;")
            info_layout.addWidget(label)
        
        info_group.setLayout(info_layout)
        status_panel.addWidget(info_group)
        
        # State labels
        state_group = QGroupBox("ST4 State")
        state_layout = QVBoxLayout()
        
        self.ready_label = QLabel("Ready: False")
        self.busy_label = QLabel("Busy: False")
        self.done_label = QLabel("Done: False")
        self.fault_label = QLabel("Fault: False")
        self.cycle_label = QLabel("Cycle Time: N/A")
        
        for label in [self.ready_label, self.busy_label, self.done_label, self.fault_label, self.cycle_label]:
            label.setStyleSheet("font-family: 'Consolas'; padding: 4px; font-size: 10pt;")
            state_layout.addWidget(label)
        
        state_group.setLayout(state_layout)
        status_panel.addWidget(state_group)
        
        # Stage info
        stage_group = QGroupBox("Calibration & Testing Status")
        stage_layout = QVBoxLayout()
        self.stage_status_label = QLabel("Active Stage: Idle")
        self.stage_status_label.setStyleSheet("font-family: 'Consolas'; padding: 4px; font-size: 10pt;")
        stage_layout.addWidget(self.stage_status_label)
        
        # Progress bar
        self.progress_bar = QProgressBar()
        self.progress_bar.setRange(0, 100)
        self.progress_bar.setValue(0)
        self.progress_bar.setTextVisible(True)
        self.progress_bar.setFormat("%p%")
        stage_layout.addWidget(self.progress_bar)
        
        stage_group.setLayout(stage_layout)
        status_panel.addWidget(stage_group)
        
        # Result display
        result_group = QGroupBox("Test Result")
        result_layout = QVBoxLayout()
        
        self.result_label = QLabel("Result: N/A")
        self.pass_count_label = QLabel("Pass Count: N/A")
        
        for label in [self.result_label, self.pass_count_label]:
            label.setStyleSheet("font-family: 'Consolas'; padding: 4px; font-size: 10pt;")
            result_layout.addWidget(label)
        
        result_group.setLayout(result_layout)
        status_panel.addWidget(result_group)
        
        # View Options
        view_group = QGroupBox("View Options")
        view_layout = QVBoxLayout()
        
        # Environment master toggle
        self.env_checkbox = QCheckBox("Show Environment")
        self.env_checkbox.setChecked(True)
        self.env_checkbox.stateChanged.connect(self.on_env_toggled)
        view_layout.addWidget(self.env_checkbox)
        
        # Grid toggle
        self.grid_checkbox = QCheckBox("Show Grid")
        self.grid_checkbox.setChecked(True)
        self.grid_checkbox.stateChanged.connect(self.on_grid_toggled)
        view_layout.addWidget(self.grid_checkbox)
        
        # Frame toggle
        self.frame_checkbox = QCheckBox("Show Frame")
        self.frame_checkbox.setChecked(False)  # Off by default
        self.frame_checkbox.stateChanged.connect(self.on_frame_toggled)
        view_layout.addWidget(self.frame_checkbox)
        
        # Preset dropdown
        preset_layout = QHBoxLayout()
        preset_layout.addWidget(QLabel("Preset:"))
        self.preset_combo = QComboBox()
        self.preset_combo.addItems(["Minimal", "Default", "Detailed"])
        self.preset_combo.setCurrentIndex(0)  # Minimal by default
        self.preset_combo.currentIndexChanged.connect(self.on_preset_changed)
        preset_layout.addWidget(self.preset_combo)
        view_layout.addLayout(preset_layout)
        
        view_group.setLayout(view_layout)
        status_panel.addWidget(view_group)
        
        # Extra KPIs with collapsible list
        self.extra_group = QGroupBox("Extra Signals")
        self.extra_layout = QVBoxLayout()
        self.extra_group.setLayout(self.extra_layout)
        
        # Add "Show all" toggle
        self.show_all_extra = QCheckBox("Show all signals")
        self.show_all_extra.stateChanged.connect(self.update_extra_display)
        self.extra_layout.addWidget(self.show_all_extra)
        
        # Container for extra signals
        self.extra_signals_container = QWidget()
        self.extra_signals_layout = QVBoxLayout(self.extra_signals_container)
        self.extra_layout.addWidget(self.extra_signals_container)
        
        status_panel.addWidget(self.extra_group)
        
        status_panel.addStretch()
        status_scroll.setWidget(status_widget)
        content_layout.addWidget(status_scroll, 1)
        
        main_layout.addLayout(content_layout, 1)
        
        # Bottom controls
        controls_layout = QHBoxLayout()
        
        # Live/Replay toggle
        self.live_toggle = QCheckBox("LIVE Mode")
        self.live_toggle.setChecked(True)
        self.live_toggle.stateChanged.connect(self.on_live_toggled)
        controls_layout.addWidget(self.live_toggle)
        
        # Play/Pause
        self.play_button = QPushButton("⏸")
        self.play_button.clicked.connect(self.toggle_play)
        self.play_button.setEnabled(False)
        controls_layout.addWidget(self.play_button)
        
        # Speed control
        controls_layout.addWidget(QLabel("Speed:"))
        self.speed_combo = QComboBox()
        self.speed_combo.addItems(["0.5x", "1x", "2x", "4x"])
        self.speed_combo.setCurrentIndex(1)
        self.speed_combo.currentIndexChanged.connect(self.on_speed_changed)
        self.speed_combo.setEnabled(False)
        controls_layout.addWidget(self.speed_combo)
        
        # Timeline slider
        controls_layout.addWidget(QLabel("Timeline:"))
        self.timeline_slider = QSlider(Qt.Horizontal)
        self.timeline_slider.setEnabled(False)
        self.timeline_slider.setMinimum(0)
        self.timeline_slider.setMaximum(1000)
        self.timeline_slider.valueChanged.connect(self.on_timeline_changed)
        controls_layout.addWidget(self.timeline_slider, 2)
        
        # Time display
        self.time_label = QLabel("00:00.000")
        self.time_label.setStyleSheet("font-family: 'Consolas'; padding: 4px; font-size: 10pt;")
        controls_layout.addWidget(self.time_label)
        
        # Camera controls
        controls_layout.addWidget(QLabel("Camera:"))
        reset_view_btn = QPushButton("Reset View")
        reset_view_btn.clicked.connect(self.gl_widget.reset_view)
        controls_layout.addWidget(reset_view_btn)
        
        self.orbit_checkbox = QCheckBox("Auto Orbit")
        self.orbit_checkbox.stateChanged.connect(self.on_orbit_toggled)
        controls_layout.addWidget(self.orbit_checkbox)
        
        # Reload button
        reload_button = QPushButton("Reload Log")
        reload_button.clicked.connect(self.discover_log)
        controls_layout.addWidget(reload_button)
        
        main_layout.addLayout(controls_layout)
    
    def on_env_toggled(self, state):
        """Handle environment master toggle"""
        checked = state == Qt.Checked
        self.gl_widget.show_environment = checked
        
        # Enable/disable child toggles
        self.grid_checkbox.setEnabled(checked)
        self.frame_checkbox.setEnabled(checked)
        
        self.gl_widget.update()
    
    def on_grid_toggled(self, state):
        """Handle grid toggle"""
        self.gl_widget.show_grid = state == Qt.Checked
        self.gl_widget.update()
    
    def on_frame_toggled(self, state):
        """Handle frame toggle"""
        self.gl_widget.show_frame = state == Qt.Checked
        self.gl_widget.update()
    
    def on_preset_changed(self, index):
        """Handle preset selection"""
        if index == 0:  # Minimal
            self.env_checkbox.setChecked(True)
            self.grid_checkbox.setChecked(True)
            self.frame_checkbox.setChecked(False)
        elif index == 1:  # Default
            self.env_checkbox.setChecked(True)
            self.grid_checkbox.setChecked(True)
            self.frame_checkbox.setChecked(True)
        elif index == 2:  # Detailed
            self.env_checkbox.setChecked(True)
            self.grid_checkbox.setChecked(True)
            self.frame_checkbox.setChecked(True)
            # Could add more detailed settings here if needed
    
    def _stop_tail_worker(self):
        """Safely stop the tail worker if it exists"""
        if self.tail_worker:
            self.tail_worker.stop()
            self.tail_worker = None
    
    def load_live_snapshot(self) -> Tuple[Optional[ST4Event], int]:
        """Load snapshot of last N lines from log file, return latest event and raw count"""
        if not self.log_path or not os.path.exists(self.log_path):
            return None, 0
        
        try:
            with open(self.log_path, 'r', encoding='utf-8', errors='ignore') as f:
                # Read last N lines efficiently
                lines = collections.deque(f, maxlen=SNAPSHOT_LINES)
            
            parser = ST4LogParser()
            raw_count = 0
            latest_event = None
            
            for line in lines:
                event = parser.parse_line(line)
                if event:
                    raw_count += 1
                    latest_event = event
            
            # If we have a parser state but no event from the last line,
            # get the current state from the parser
            if latest_event is None:
                latest_event = parser.get_current_state()
            
            return latest_event, raw_count
                
        except Exception as e:
            print(f"Error loading snapshot: {e}")
            traceback.print_exc()
            return None, 0
    
    def discover_log(self):
        """Discover and load ST4 log file"""
        # Stop current worker
        self._stop_tail_worker()
        
        # Find log
        self.log_path = LogDiscoverer.find_st4_log()
        
        if self.log_path:
            base_name = os.path.basename(self.log_path)
            self.log_info_label.setText(f"ST4 Log: {base_name}")
            
            # Reset counters
            self.raw_event_count = 0
            self.accepted_event_count = 0
            self.update_event_count_label()
            
            if self.is_live_mode:
                self.switch_to_live()
            else:
                self.switch_to_replay()
        else:
            self.log_info_label.setText("No ST4 log found")
            self.log_path = None
            self.replay_events = []
    
    def switch_to_live(self):
        """Switch to live mode (tail log)"""
        if not self.log_path:
            return
        
        # Stop any existing worker
        self._stop_tail_worker()
        
        # Clear replay data
        self.replay_events = []
        self.current_time_ns = 0
        
        # Update UI for LIVE mode
        self.current_mode = "LIVE"
        self.timeline_slider.setEnabled(False)
        self.speed_combo.setEnabled(False)
        self.play_button.setEnabled(False)
        self.is_playing = False
        self.play_button.setText("▶")
        
        # Load snapshot of existing content
        latest_event, snapshot_raw_count = self.load_live_snapshot()
        self.raw_event_count = snapshot_raw_count
        self.accepted_event_count = 0
        self.update_event_count_label()
        
        if latest_event:
            self.last_state_snapshot = {
                'ready': latest_event.ready,
                'busy': latest_event.busy,
                'done': latest_event.done,
                'fault': latest_event.fault,
                'cycle_time_ms': latest_event.cycle_time_ms,
                'extra': latest_event.extra.copy() if latest_event.extra else {}
            }
            
            # Get event time for update_state
            event_time_s = latest_event.extra.get('simpy_now_s', time.time())
            self.gl_widget.update_state(latest_event, self.current_mode, event_time_s)
            self.update_display(latest_event, from_snapshot=True)
            
            # Update debug label with snapshot info
            simpy_now = latest_event.extra.get('simpy_now_s')
            vsi_time = latest_event.t_ns
            if simpy_now is not None:
                time_str = f"SimPy: {simpy_now:.2f}s, VSI: {vsi_time/1e9:.2f}s"
            else:
                time_str = f"VSI: {vsi_time/1e9:.2f}s"
            self.debug_label.setText(f"Mode: LIVE | Snapshot: {time_str}")
            
            # Start tail worker with seeded parser
            self.tail_worker = LogTailWorker(self.log_path, seed_event=latest_event)
        else:
            self.debug_label.setText("Mode: LIVE | Last Event: NONE (no parsable state lines yet)")
            self.last_state_snapshot = None
            # Start tail worker without seed
            self.tail_worker = LogTailWorker(self.log_path)
        
        # Connect signals
        self.tail_worker.new_event.connect(self.process_new_event)
        self.tail_worker.activity_detected.connect(self.on_activity_detected)
        self.tail_worker.file_reopened.connect(self.on_file_reopened)
        self.tail_worker.start()
        
        self.last_activity_time = time.time()
        self.is_idle = False
        self.idle_start_time = 0.0
        self.update_connection_status()
    
    def switch_to_replay(self):
        """Switch to replay mode (load full file)"""
        # Stop any existing worker
        self._stop_tail_worker()
        
        if not self.log_path:
            return
        
        # Update UI for REPLAY mode
        self.current_mode = "REPLAY"
        self.timeline_slider.setEnabled(True)
        self.speed_combo.setEnabled(True)
        self.play_button.setEnabled(True)
        self.is_playing = True
        self.play_button.setText("⏸")
        self.is_idle = False
        self.idle_start_time = 0.0
        
        # Load all events
        self.load_replay_data()
        
        # Setup timeline slider and timebase
        if self.replay_events:
            self.replay_min_time = self.replay_events[0].t_ns
            self.replay_max_time = self.replay_events[-1].t_ns
            self.current_time_ns = self.replay_min_time
            self.timeline_slider.setValue(0)
            self.update_time_label()
            
            # Get initial visual time
            visual_time_s = self.get_visual_time_s()
            self.gl_widget.animation_time = visual_time_s
            self.gl_widget.compute_active_stage(visual_time_s)
            
            # Force immediate display update with initial state
            self.update_states_from_replay()
            
            # Update debug label for REPLAY mode
            current_event = None
            for event in self.replay_events:
                if event.t_ns <= self.current_time_ns:
                    current_event = event
                else:
                    break
            
            if current_event:
                simpy_now = current_event.extra.get('simpy_now_s')
                vsi_time = current_event.t_ns
                if simpy_now is not None:
                    time_str = f"SimPy: {simpy_now:.2f}s, VSI: {vsi_time/1e9:.2f}s"
                else:
                    time_str = f"VSI: {vsi_time/1e9:.2f}s"
                self.debug_label.setText(f"Mode: REPLAY | Event: {time_str}")
            else:
                self.debug_label.setText("Mode: REPLAY | No events loaded")
        else:
            self.debug_label.setText("Mode: REPLAY | No events loaded")
        
        self.update_connection_status()
    
    def load_replay_data(self):
        """Load all events from log file for replay and compute accepted_event_count"""
        try:
            with open(self.log_path, 'r', encoding='utf-8', errors='ignore') as f:
                lines = f.readlines()
            
            events = []
            parser = ST4LogParser()
            
            for line in lines:
                event = parser.parse_line(line)
                if event:
                    events.append(event)
            
            # Sort by time and limit
            events.sort(key=lambda x: x.t_ns)
            self.replay_events = events[-MAX_EVENTS:]
            self.raw_event_count = len(self.replay_events)
            
            # Compute accepted_event_count using the same logic as in live mode
            self.accepted_event_count = 0
            last_state_snapshot = None
            
            for event in self.replay_events:
                new_state = {
                    'ready': event.ready,
                    'busy': event.busy,
                    'done': event.done,
                    'fault': event.fault,
                    'cycle_time_ms': event.cycle_time_ms,
                    'extra': event.extra.copy() if event.extra else {}
                }
                
                if last_state_snapshot is None or self._state_changed(last_state_snapshot, new_state):
                    last_state_snapshot = new_state
                    self.accepted_event_count += 1
            
            self.update_event_count_label()
            
            print(f"Loaded {len(self.replay_events)} ST4 events for replay")
            print(f"Accepted events (state changes): {self.accepted_event_count}")
            if self.replay_events:
                print(f"Time range: {self.replay_events[0].t_ns/1e9:.3f}s to {self.replay_events[-1].t_ns/1e9:.3f}s")
            
        except Exception as e:
            print(f"Error loading {self.log_path}: {e}")
            traceback.print_exc()
            self.replay_events = []
            self.raw_event_count = 0
            self.accepted_event_count = 0
            self.update_event_count_label()
    
    def get_max_replay_time(self):
        """Get maximum timestamp across replay events"""
        if not self.replay_events:
            return 0
        return self.replay_events[-1].t_ns
    
    def get_min_replay_time(self):
        """Get minimum timestamp across replay events"""
        if not self.replay_events:
            return 0
        return self.replay_events[0].t_ns
    
    def update_states_from_replay(self):
        """Update states based on current replay time"""
        if not self.replay_events:
            return
        
        current_time = self.current_time_ns
        current_event = None
        
        # Find last event <= current time
        for event in self.replay_events:
            if event.t_ns <= current_time:
                current_event = event
            else:
                break
        
        if current_event:
            # Get event time for update_state
            event_time_s = current_event.extra.get('simpy_now_s', (current_time - self.replay_min_time) / 1e9)
            self.gl_widget.update_state(current_event, self.current_mode, event_time_s)
            
            # For replay mode, update display without debouncing
            self.update_display(current_event, from_snapshot=False)
            
            # Update debug label for REPLAY mode
            simpy_now = current_event.extra.get('simpy_now_s')
            vsi_time = current_event.t_ns
            if simpy_now is not None:
                time_str = f"SimPy: {simpy_now:.2f}s, VSI: {vsi_time/1e9:.2f}s"
            else:
                time_str = f"VSI: {vsi_time/1e9:.2f}s"
            self.debug_label.setText(f"Mode: REPLAY | Event: {time_str}")
    
    def update_event_count_label(self):
        """Update the event count label"""
        self.event_count_label.setText(f"Raw: {self.raw_event_count} | Accepted: {self.accepted_event_count}")
    
    def update_connection_status(self):
        """Update the connection status indicator"""
        if self.is_live_mode:
            if self.is_idle:
                idle_time = time.time() - self.idle_start_time
                if idle_time > LONG_IDLE_TIMEOUT:
                    self.connection_status.setText("●")  # Red dot
                    self.connection_status.setStyleSheet("color: red; font-size: 16pt; font-weight: bold;")
                    self.connection_status.setToolTip("STOPPED? - No activity for over 15 seconds")
                else:
                    self.connection_status.setText("●")  # Yellow dot
                    self.connection_status.setStyleSheet("color: yellow; font-size: 16pt; font-weight: bold;")
                    self.connection_status.setToolTip("IDLE - No recent activity")
            else:
                self.connection_status.setText("●")  # Green dot
                self.connection_status.setStyleSheet("color: green; font-size: 16pt; font-weight: bold;")
                self.connection_status.setToolTip("LIVE - Active connection")
        else:
            self.connection_status.setText("●")  # Blue dot
            self.connection_status.setStyleSheet("color: blue; font-size: 16pt; font-weight: bold;")
            self.connection_status.setToolTip("REPLAY - Playing back recorded log")
    
    def update_time_label(self):
        """Update the time display label"""
        if self.is_live_mode:
            if self.is_idle:
                idle_time = time.time() - self.idle_start_time
                if idle_time > LONG_IDLE_TIMEOUT:
                    self.time_label.setText("LIVE (STOPPED?)")
                else:
                    self.time_label.setText("LIVE (IDLE)")
            else:
                # In live mode, show both SimPy and VSI times when available
                if self.current_event:
                    simpy_now = self.current_event.extra.get('simpy_now_s')
                    vsi_time = self.current_event.t_ns
                    
                    if simpy_now is not None:
                        self.time_label.setText(f"LIVE (SimPy: {simpy_now:.1f}s, VSI: {vsi_time/1e9:.1f}s)")
                    else:
                        self.time_label.setText(f"LIVE (VSI: {vsi_time/1e9:.1f}s)")
                else:
                    self.time_label.setText("LIVE")
        else:
            # In replay mode, show both SimPy and VSI times when available
            if self.replay_events:
                # Find current event based on current_time_ns
                current_event = None
                for event in self.replay_events:
                    if event.t_ns <= self.current_time_ns:
                        current_event = event
                    else:
                        break
                
                if current_event:
                    simpy_now = current_event.extra.get('simpy_now_s')
                    if simpy_now is not None:
                        # Show SimPy time with total range
                        total_simpy_start = self.replay_events[0].extra.get('simpy_now_s', 0)
                        total_simpy_end = self.replay_events[-1].extra.get('simpy_now_s', simpy_now + 1)
                        self.time_label.setText(f"SimPy: {simpy_now:07.3f}s / {total_simpy_end:07.3f}s")
                    else:
                        # Fall back to VSI time
                        time_s = (self.current_time_ns - self.replay_min_time) / 1e9
                        total_s = (self.replay_max_time - self.replay_min_time) / 1e9
                        self.time_label.setText(f"VSI: {time_s:07.3f}s / {total_s:07.3f}s")
                else:
                    self.time_label.setText("00:00.000")
            else:
                self.time_label.setText("00:00.000")
    
    def process_new_event(self, event: ST4Event):
        """Process new event from tail worker"""
        # Increment raw count
        self.raw_event_count += 1
        self.update_event_count_label()
        
        # Store current event
        self.current_event = event
        
        # Check if state has actually changed
        new_state = {
            'ready': event.ready,
            'busy': event.busy,
            'done': event.done,
            'fault': event.fault,
            'cycle_time_ms': event.cycle_time_ms,
            'extra': event.extra.copy() if event.extra else {}
        }
        
        # Always update last activity time
        self.last_activity_time = time.time()
        if self.is_idle:
            self.is_idle = False
            self.idle_start_time = 0.0
        
        # Check if state changed
        if self.last_state_snapshot is None or self._state_changed(self.last_state_snapshot, new_state):
            self.last_state_snapshot = new_state
            self.accepted_event_count += 1
            self.update_event_count_label()
            
            # Get event time for update_state
            event_time_s = event.extra.get('simpy_now_s', time.time())
            self.gl_widget.update_state(event, self.current_mode, event_time_s)
            self.update_display(event, from_snapshot=False)
            
            # Use both SimPy and VSI times in debug label if available
            simpy_now = event.extra.get('simpy_now_s')
            vsi_time = event.t_ns
            if simpy_now is not None:
                time_str = f"SimPy: {simpy_now:.2f}s, VSI: {vsi_time/1e9:.2f}s"
            else:
                time_str = f"VSI: {vsi_time/1e9:.2f}s"
                
            self.debug_label.setText(f"Mode: LIVE | Accepted: {time_str}")
            self.last_event_ignored = False
        else:
            # State didn't change
            simpy_now = event.extra.get('simpy_now_s')
            vsi_time = event.t_ns
            if simpy_now is not None:
                time_str = f"SimPy: {simpy_now:.2f}s, VSI: {vsi_time/1e9:.2f}s"
            else:
                time_str = f"VSI: {vsi_time/1e9:.2f}s"
                
            self.debug_label.setText(f"Mode: LIVE | No change: {time_str}")
            self.last_event_ignored = True
        
        self.update_connection_status()
    
    def on_activity_detected(self):
        """Handle activity detection from tail worker"""
        self.last_activity_time = time.time()
        if self.is_idle:
            self.is_idle = False
            self.idle_start_time = 0.0
            self.update_time_label()
            self.update_connection_status()
    
    def on_idle_detected(self):
        """Handle idle detection"""
        if not self.is_idle and self.is_live_mode:
            self.is_idle = True
            self.idle_start_time = time.time()
            self.update_time_label()
            self.update_connection_status()
            
            # Auto-switch to replay if enabled and idle
            if AUTO_SWITCH_ON_IDLE and self.is_live_mode:
                self.live_toggle.setChecked(False)
    
    def on_file_reopened(self):
        """Handle file reopening (rotation/truncation)"""
        if not self.log_path or not self.is_live_mode:
            return
        
        # Reload snapshot to get latest state
        latest_event, _ = self.load_live_snapshot()
        if latest_event and self.tail_worker:
            # Reseed the parser with the latest state
            self.tail_worker.reseed_parser(latest_event)
            # Update UI with the latest state
            event_time_s = latest_event.extra.get('simpy_now_s', time.time())
            self.gl_widget.update_state(latest_event, self.current_mode, event_time_s)
            self.update_display(latest_event, from_snapshot=False)
    
    def _state_changed(self, old_state: dict, new_state: dict) -> bool:
        """Check if state has meaningfully changed"""
        # Check basic states
        for key in ['ready', 'busy', 'done', 'fault']:
            if old_state.get(key) != new_state.get(key):
                return True
        
        # Check cycle time (with tolerance for floating point)
        old_cycle = old_state.get('cycle_time_ms')
        new_cycle = new_state.get('cycle_time_ms')
        if old_cycle is not None and new_cycle is not None:
            if abs(old_cycle - new_cycle) > 0.01:
                return True
        elif old_cycle != new_cycle:  # One is None, other is not
            return True
        
        # Check extra signals
        old_extras = old_state.get('extra', {})
        new_extras = new_state.get('extra', {})
        
        # Check if any tracked extra signal changed
        tracked_keys = set(old_extras.keys()) | set(new_extras.keys())
        for key in tracked_keys:
            if old_extras.get(key) != new_extras.get(key):
                return True
        
        return False
    
    def update_display(self, event: ST4Event, from_snapshot: bool = False):
        """Update all displays from ST4 event"""
        # Note: gl_widget state is already updated in update_state() call
        
        # Update status labels with color coding
        self.ready_label.setText(f"Ready: {event.ready}")
        self.ready_label.setStyleSheet(f"""
            font-family: 'Consolas'; padding: 4px; font-size: 10pt;
            color: {'#4ec9b0' if event.ready else '#858585'};
        """)
        
        self.busy_label.setText(f"Busy: {event.busy}")
        self.busy_label.setStyleSheet(f"""
            font-family: 'Consolas'; padding: 4px; font-size: 10pt;
            color: {'#dcdcaa' if event.busy else '#858585'};
        """)
        
        self.done_label.setText(f"Done: {event.done}")
        self.done_label.setStyleSheet(f"""
            font-family: 'Consolas'; padding: 4px; font-size: 10pt;
            color: {'#4ec9b0' if event.done else '#858585'};
        """)
        
        self.fault_label.setText(f"Fault: {event.fault}")
        self.fault_label.setStyleSheet(f"""
            font-family: 'Consolas'; padding: 4px; font-size: 10pt;
            color: {'#f48771' if event.fault else '#858585'};
        """)
        
        if event.cycle_time_ms:
            self.cycle_label.setText(f"Cycle Time: {event.cycle_time_ms:.1f} ms")
        else:
            self.cycle_label.setText("Cycle Time: N/A")
        
        # Update total and completed
        total = event.extra.get('total', 'N/A')
        completed = event.extra.get('completed', 0)
        
        # Time display
        simpy_now = event.extra.get('simpy_now_s')
        vsi_time = event.t_ns
        
        if simpy_now is not None:
            now_text = f"SimPy: {simpy_now:.2f}s, VSI: {vsi_time/1e9:.2f}s"
        else:
            now_text = f"VSI: {vsi_time/1e9:.2f}s"
        
        self.total_label.setText(f"Total: {total}")
        self.completed_label.setText(f"Completed: {completed}")
        self.now_label.setText(now_text)
        
        # Determine result
        result = "RUNNING"
        result_color = UI_MUTED
        
        if event.fault:
            result = "FAIL"
            result_color = UI_RED
        elif event.done:
            result = "PASS"
            result_color = UI_GREEN
        elif event.busy:
            result = "RUNNING"
            result_color = UI_YELLOW
        
        self.result_label.setText(f"Result: {result}")
        self.result_label.setStyleSheet(f"""
            font-family: 'Consolas'; padding: 4px; font-size: 10pt;
            color: {result_color}; font-weight: bold;
        """)
        
        # Pass count (completed count)
        self.pass_count_label.setText(f"Pass Count: {completed}")
        
        # Update stage status - use gl_widget.stage_progress as single source
        active_index = self.gl_widget.active_stage_index
        if active_index >= 0 and active_index < 4:
            stage_name = self.gl_widget.stage_names[active_index]
            self.stage_status_label.setText(f"Active Stage: {stage_name}")
            self.stage_status_label.setStyleSheet("""
                font-family: 'Consolas'; padding: 4px; font-size: 10pt;
                color: #ffd700; font-weight: bold;
            """)
            
            # Update progress bar - use gl_widget.stage_progress as single source
            progress = int(self.gl_widget.stage_progress * 100)
            self.progress_bar.setValue(progress)
            
            # Update progress bar color based on stage
            if active_index == 3:  # Test stage
                if event.fault:
                    self.progress_bar.setStyleSheet(f"""
                        QProgressBar::chunk {{
                            background-color: {UI_RED};
                        }}
                    """)
                elif event.done:
                    self.progress_bar.setStyleSheet(f"""
                        QProgressBar::chunk {{
                            background-color: {UI_GREEN};
                        }}
                    """)
                else:
                    self.progress_bar.setStyleSheet(f"""
                        QProgressBar::chunk {{
                            background-color: {UI_YELLOW};
                        }}
                    """)
            else:
                self.progress_bar.setStyleSheet(f"""
                    QProgressBar::chunk {{
                        background-color: {UI_ACCENT};
                    }}
                """)
        else:
            self.stage_status_label.setText(f"Active Stage: Idle")
            self.stage_status_label.setStyleSheet("""
                font-family: 'Consolas'; padding: 4px; font-size: 10pt;
                color: #858585;
            """)
            self.progress_bar.setValue(0)
            self.progress_bar.setStyleSheet("")  # Reset to default
        
        # Update extra KPIs
        self.update_extra_display()
    
    def update_extra_display(self):
        """Update extra signals display"""
        # Clear existing widgets
        for i in reversed(range(self.extra_signals_layout.count())):
            widget = self.extra_signals_layout.itemAt(i).widget()
            if widget:
                widget.deleteLater()
        
        if not self.current_event:
            return
        
        # Gather extra items with priority keys first
        priority_items = []
        other_items = []
        
        for key, value in self.current_event.extra.items():
            if key in PRIORITY_EXTRA_KEYS:
                priority_items.append((key, value))
            else:
                other_items.append((key, value))
        
        # Sort priority items by our defined order
        priority_items.sort(key=lambda x: PRIORITY_EXTRA_KEYS.index(x[0]) if x[0] in PRIORITY_EXTRA_KEYS else len(PRIORITY_EXTRA_KEYS))
        
        # Combine items
        all_items = priority_items + other_items
        
        # Limit display if "Show all" is not checked
        if not self.show_all_extra.isChecked():
            all_items = all_items[:10]
        
        for key, value in all_items:
            label = QLabel(f"{key}: {value}")
            label.setStyleSheet("font-family: 'Consolas'; padding: 2px; font-size: 9pt;")
            label.setToolTip(f"{key} = {value}")
            self.extra_signals_layout.addWidget(label)
        
        # Add "..." if there are more items not shown
        if not self.show_all_extra.isChecked() and len(priority_items + other_items) > 10:
            label = QLabel(f"... and {len(priority_items + other_items) - 10} more")
            label.setStyleSheet("font-family: 'Consolas'; padding: 2px; font-size: 9pt; color: #858585;")
            self.extra_signals_layout.addWidget(label)
        
        # Hide extra group if no extra signals
        self.extra_group.setVisible(len(all_items) > 0)
    
    def update_animation(self):
        """Update animation based on timer"""
        # Get current visual time
        visual_time_s = self.get_visual_time_s()
        
        # Update animation time in gl_widget
        self.gl_widget.animation_time = visual_time_s
        
        # Compute active stage using visual time
        self.gl_widget.compute_active_stage(visual_time_s)
        active_index = self.gl_widget.active_stage_index
        
        # Update stage status and progress bar - use gl_widget.stage_progress as single source
        if active_index >= 0 and active_index < 4:
            stage_name = self.gl_widget.stage_names[active_index]
            self.stage_status_label.setText(f"Active Stage: {stage_name}")
            self.stage_status_label.setStyleSheet("""
                font-family: 'Consolas'; padding: 4px; font-size: 10pt;
                color: #ffd700; font-weight: bold;
            """)
            
            # Update progress bar - use gl_widget.stage_progress as single source
            progress = int(self.gl_widget.stage_progress * 100)
            self.progress_bar.setValue(progress)
        else:
            self.stage_status_label.setText("Active Stage: Idle")
            self.stage_status_label.setStyleSheet("""
                font-family: 'Consolas'; padding: 4px; font-size: 10pt;
                color: #858585;
            """)
            self.progress_bar.setValue(0)
        
        if self.is_playing and not self.is_live_mode and self.replay_events:
            # Advance replay time
            time_delta_ns = int(33_333_333 * self.playback_speed)  # ~30 FPS
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
            
            self.update_states_from_replay()
            self.update_time_label()
        
        # Check for idle in LIVE mode
        if self.is_live_mode and not self.is_idle:
            idle_time = time.time() - self.last_activity_time
            if idle_time > IDLE_TIMEOUT:
                self.on_idle_detected()
        elif self.is_live_mode and self.is_idle:
            # Update time label with idle status
            self.update_time_label()
        
        # Trigger OpenGL update
        self.gl_widget.update()
    
    def on_live_toggled(self, state):
        self.is_live_mode = state == Qt.Checked
        
        if self.is_live_mode:
            self.switch_to_live()
        else:
            self.switch_to_replay()
    
    def toggle_play(self):
        if not self.is_live_mode:
            self.is_playing = not self.is_playing
            self.play_button.setText("▶" if not self.is_playing else "⏸")
    
    def on_speed_changed(self, index):
        speeds = [0.5, 1.0, 2.0, 4.0]
        self.playback_speed = speeds[index]
    
    def on_timeline_changed(self, value):
        if not self.replay_events or self.is_live_mode:
            return
        
        # Calculate time from slider
        time_range = self.replay_max_time - self.replay_min_time
        if time_range > 0:
            self.current_time_ns = self.replay_min_time + int(time_range * value / 1000)
            self.update_states_from_replay()
            self.update_time_label()
    
    def on_orbit_toggled(self, state):
        self.gl_widget.orbit_enabled = state == Qt.Checked
    
    def closeEvent(self, event):
        """Cleanup on close"""
        self._stop_tail_worker()
        event.accept()

# ===== MAIN APPLICATION =====
def main():
    # Print debug info at startup
    print("Running ST4 Calibration & Testing visualizer from:", os.path.abspath(__file__))
    print("CWD:", os.path.abspath(os.getcwd()))
    print("PROJECT_ROOT:", PROJECT_ROOT)
    print("SEARCH_ROOTS:", SEARCH_ROOTS)
    
    # Set OpenGL compatibility profile
    fmt = QSurfaceFormat()
    fmt.setVersion(OPENGL_MAJOR_VERSION, OPENGL_MINOR_VERSION)
    fmt.setProfile(QSurfaceFormat.CompatibilityProfile)
    fmt.setDepthBufferSize(24)
    fmt.setSamples(4)  # 4x MSAA
    QSurfaceFormat.setDefaultFormat(fmt)
    
    app = QApplication(sys.argv)
    
    # Check for OpenGL
    if USE_PYOPENGL and not PYOPENGL_AVAILABLE:
        reply = QMessageBox.warning(
            None,
            "OpenGL Warning",
            "PyOpenGL not installed. Visualization will be basic.\n"
            "Install with: pip install PyOpenGL\n\n"
            "Continue anyway?",
            QMessageBox.Yes | QMessageBox.No
        )
        if reply == QMessageBox.No:
            sys.exit(1)
    
    window = MainWindow()
    window.show()
    
    sys.exit(app.exec())

if __name__ == "__main__":
    main()