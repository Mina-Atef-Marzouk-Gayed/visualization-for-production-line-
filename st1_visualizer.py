#!/usr/bin/env python3
"""
ST1 Visualizer - Professional industrial robot visualization for ST1 Component Kitting logs

CHANGES:
1. Fixed cylinder axis bug: Added glRotatef(-90, 1, 0, 0) in draw_cylinder() to align gluCylinder's +Z axis with +Y
2. Reused GLU quadrics: Created single quadric in initializeGL(), reused in draw_cylinder/draw_sphere, removed per-frame creation/deletion
3. Made REPLAY deterministic: Removed time.time() fallback in update_state(), using self.animation_time instead
4. Fixed visual_time_s consistency: MainWindow now passes visual_time_s properly in all call paths
5. Added local blending for Secure/Solder effect with alpha transparency
6. Cleaned up quadric in widget destructor

ENHANCEMENTS (vs ST2):
7. Fixed LIVE mode switching (matching ST2's logic for clean worker restart)
8. Added debug status overlay showing mode, worker state, log path, last event
9. Applied consistent dark theme with improved visual styling
10. Added anti-aliasing and smoother animations
11. Improved UI layout with better spacing and grouping
12. Added visual effects: pulse animations for state changes
13. Added debounced updates to reduce jitter

ROBOT MOTION FIXES:
14. Use deterministic animation time in LIVE mode: time.monotonic() - self.live_t0_wall
15. Removed random idle motion - robot holds stable poses when not in active stage
16. Updated stages to 4: Pick, Kitting, Mounting, Soldering
17. Removed stage vibration and random motions for deterministic movement

NEW FIXES AND FEATURES:
18. Removed unexplained robot wiggle (deterministic motion only)
19. Added component state machine (IN_BIN -> ATTACHED -> ON_TRAY) with smooth transitions
20. Fixed solder effect blending with proper depth masking
21. Added stage visual indicators for each stage
22. Added inventory system with bin cycling and visual feedback
23. Fixed mid-cycle attachment bug - visualizer now starts animation even when attaching during active cycle
24. Fixed UI state sticking bug - coalesce events per read cycle to ensure UI shows final state
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

# ===== CONFIGURATION =====
SEARCH_ROOT = "."
MAX_EVENTS = 50000
TIMER_FPS = 30
DONE_PULSE_MS = 300
FAULT_PULSE_MS = 500
OPENGL_MAJOR_VERSION = 2
OPENGL_MINOR_VERSION = 1
USE_PYOPENGL = True
SNAPSHOT_LINES = 3000
IDLE_TIMEOUT = 5.0  # seconds
LONG_IDLE_TIMEOUT = 15.0  # seconds for "STOPPED?" message
AUTO_SWITCH_ON_IDLE = False  # Whether to auto-switch to replay when idle
DEBOUNCE_THRESHOLD_MS = 50  # Minimum time between accepted state updates

# ===== QT IMPORTS =====
try:
    from PySide6.QtWidgets import *
    from PySide6.QtCore import *
    from PySide6.QtGui import QSurfaceFormat, QPainter, QColor, QFont, QPen, QFontMetrics, QBrush, QPalette
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
class ST1Event:
    t_ns: int
    ready: bool = False
    busy: bool = False
    done: bool = False
    fault: bool = False
    cycle_time_ms: Optional[float] = None
    extra: Dict[str, Any] = field(default_factory=dict)

# ===== CARRY-FORWARD PARSER =====
class ST1LogParser:
    """Carry-forward parser for ST1 Component Kitting logs"""
    
    def __init__(self):
        self.reset()
    
    def reset(self):
        """Reset parser state"""
        self.last_vsi_time_ns = None
        self.synthetic_time_ns = 0
        
        # Carry-forward state
        self.carried_state = {
            'ready': None,  # None means unknown/not seen yet
            'busy': None,
            'done': None,
            'fault': None
        }
        self.carried_cycle_time = None
        self.carried_extra = {}
        
        # Have we ever seen any state value?
        self.has_seen_any_state = False
        
        # Patterns
        self.vsi_time_pattern = re.compile(r"VSI\s+time\s*:\s*(\d+)\s*ns", re.IGNORECASE)
        self.cycle_time_pattern = re.compile(r"cycle[_\s]*time[_\s]*[:=]?\s*([\d.]+)\s*ms", re.IGNORECASE)
        self.key_value_pattern = re.compile(r"(\w+)[_\s]*[:=]\s*([\w.-]+)")
        
        # State patterns with values ONLY - no boolean fallback
        self.state_patterns = {
            "ready": re.compile(r"\bready\b\s*[:=]\s*(\d+)", re.IGNORECASE),
            "busy": re.compile(r"\bbusy\b\s*[:=]\s*(\d+)", re.IGNORECASE),
            "done": re.compile(r"\bdone\b\s*[:=]\s*(\d+)", re.IGNORECASE),
            "fault": re.compile(r"\bfault\b\s*[:=]\s*(\d+)", re.IGNORECASE),
        }
    
    def seed_from_event(self, event: ST1Event):
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
    
    def parse_line(self, line: str) -> Optional[ST1Event]:
        """Parse a line and return an event if state was updated"""
        line = line.strip()
        if not line:
            return None
        
        # Track if this line had any signal at all
        had_signal = False
        
        # Check for VSI time (can be on its own line)
        vsi_match = self.vsi_time_pattern.search(line)
        if vsi_match:
            self.last_vsi_time_ns = int(vsi_match.group(1))
            # VSI time alone doesn't count as a signal
        
        # Determine timestamp to use
        if self.last_vsi_time_ns is not None:
            timestamp = self.last_vsi_time_ns
        else:
            self.synthetic_time_ns += 10_000_000  # 10ms increment
            timestamp = self.synthetic_time_ns
        
        # Check for state updates
        for state_name, pattern in self.state_patterns.items():
            match = pattern.search(line)
            if match:
                try:
                    value = int(match.group(1))
                    # Always update carried state when we see a signal
                    self.carried_state[state_name] = value
                    self.has_seen_any_state = True
                    had_signal = True
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
            key, value = match.groups()
            # Skip already parsed keys
            if key.lower() in ['vsi', 'time', 'cycle', 'ready', 'busy', 'done', 'fault']:
                continue
            # Try to convert to number if possible
            try:
                if '.' in value:
                    value = float(value)
                else:
                    value = int(value)
            except ValueError:
                pass
            current_line_extras[key] = value
        
        # Update carried extras with current line extras
        if current_line_extras:
            for key, value in current_line_extras.items():
                self.carried_extra[key] = value
            had_signal = True
        
        # Emit an event if this line had any signal (even if values didn't change)
        if had_signal:
            # Convert carried state to booleans (None -> False)
            ready = bool(self.carried_state['ready']) if self.carried_state['ready'] is not None else False
            busy = bool(self.carried_state['busy']) if self.carried_state['busy'] is not None else False
            done = bool(self.carried_state['done']) if self.carried_state['done'] is not None else False
            fault = bool(self.carried_state['fault']) if self.carried_state['fault'] is not None else False
            
            event = ST1Event(
                t_ns=timestamp,
                ready=ready,
                busy=busy,
                done=done,
                fault=fault,
                cycle_time_ms=self.carried_cycle_time,
                extra=copy.deepcopy(self.carried_extra)
            )
            return event
        
        return None
    
    def get_current_state(self) -> Optional[ST1Event]:
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
        
        return ST1Event(
            t_ns=timestamp,
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
    def find_st1_log() -> Optional[str]:
        """Find newest ST1 log file matching pattern (more robust)"""
        st1_files = []
        
        # Search recursively from SEARCH_ROOT
        for root, dirs, files in os.walk(SEARCH_ROOT):
            for file in files:
                file_lower = file.lower()
                # Check if file contains "st1" and ends with ".log"
                if "st1" in file_lower and file_lower.endswith('.log'):
                    full_path = os.path.join(root, file)
                    mtime = os.path.getmtime(full_path)
                    
                    # Score: prefer files containing "componentkitting"
                    score = 0
                    if "componentkitting" in file_lower:
                        score = 1
                    
                    st1_files.append((score, mtime, full_path))
        
        if not st1_files:
            return None
        
        # Sort by score (higher first), then by mtime (newest first)
        st1_files.sort(key=lambda x: (-x[0], -x[1]))
        selected_file = st1_files[0][2]
        print(f"Selected ST1 log: {selected_file}")
        return selected_file

# ===== TAIL WORKER =====
class LogTailWorker(QThread):
    new_event = Signal(ST1Event)  # Emitted for every signal line
    activity_detected = Signal()  # Emitted when any line is read
    file_reopened = Signal()  # Emitted when file is reopened (rotation/truncation)
    worker_stopped = Signal()  # Emitted when worker is fully stopped
    
    def __init__(self, log_path: str, seed_event: Optional[ST1Event] = None):
        super().__init__()
        self.log_path = log_path
        self.seed_event = seed_event
        self.running = True
        self.file_handle = None
        self.file_position = 0
        self.file_inode = None
        self.parser = ST1LogParser()
        self.last_activity_time = time.time()
        
    def run(self):
        """Tail the log file and emit new events - FIXED: coalesce events per read cycle"""
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
                
                # Parse lines and coalesce events per read cycle
                if new_lines:
                    self.last_activity_time = time.time()
                    self.activity_detected.emit()
                    
                    last_event_in_chunk = None
                    
                    for line in new_lines:
                        event = self.parser.parse_line(line)
                        if event:
                            last_event_in_chunk = event
                    
                    # After processing all lines, emit ONE final event with the complete state
                    final_event = self.parser.get_current_state() or last_event_in_chunk
                    if final_event:
                        self.new_event.emit(final_event)
                
                time.sleep(0.05)  # 50ms sleep
                
            except Exception as e:
                print(f"Error in tail worker: {e}")
                time.sleep(1)
        
        # Cleanup
        if self.file_handle:
            self.file_handle.close()
        
        self.worker_stopped.emit()
    
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
            self.parser = ST1LogParser()
            
            # Seed the parser if we have a seed event (FIXED: was seed_event)
            if seed and self.seed_event:
                self.parser.seed_from_event(self.seed_event)
                
        except Exception as e:
            print(f"Error opening {self.log_path}: {e}")
            self.file_handle = None
    
    def reseed_parser(self, seed_event: ST1Event):
        """Reseed the parser with a new event (e.g., after file rotation)"""
        self.seed_event = seed_event
        self.parser.seed_from_event(seed_event)
    
    def stop(self):
        """Stop the worker thread"""
        self.running = False
        if self.isRunning():
            self.wait(2000)  # Wait up to 2 seconds

# ===== OPENGL WIDGET =====
class ST1OpenGLWidget(QOpenGLWidget):
    """Professional OpenGL visualization for ST1 with industrial robot cell"""
    
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
        self.animation_time = 0
        self.done_pulse_time = 0
        self.fault_pulse_time = 0
        self.ready_pulse_time = 0
        self.busy_pulse_time = 0
        self.shake_offset = 0.0
        self.last_completed_count = 0
        
        # Stage animation parameters
        self.base_stage_s = 2.5  # Default seconds per stage
        self.stage_s = self.base_stage_s  # Current stage duration
        self.proc_active = False  # Is processing active?
        self.proc_start = 0.0  # When processing started (in visual_time_s)
        self.proc_end = 0.0  # When processing ends (4 stages)
        self.active_stage_index = -1  # -1 means no stage active
        self.stage_progress = 0.0  # Progress within current stage (0.0 to 1.0)
        
        # ST1 stage names - updated to 4 stages: Pick, Kitting, Mounting, Soldering
        self.stage_names = ["Pick Component", "Kitting", "Mounting", "Soldering"]
        
        # Debug flag for mid-cycle attachment
        self.DEBUG = True
        self.has_seen_first_event = False
        
        # Colors - improved dark theme matching ST2
        self.colors = {
            "dark_gray": (0.12, 0.12, 0.14, 1.0),
            "medium_gray": (0.18, 0.18, 0.20, 1.0),
            "light_gray": (0.25, 0.25, 0.27, 1.0),
            "metal_gray": (0.3, 0.32, 0.35, 1.0),
            "dark_blue": (0.08, 0.12, 0.20, 1.0),
            "green_led": (0.0, 0.9, 0.3, 1.0),
            "amber_led": (1.0, 0.7, 0.1, 1.0),
            "red_led": (0.9, 0.1, 0.1, 1.0),
            "cyan_pulse": (0.0, 0.9, 0.9, 1.0),
            "grid": (0.20, 0.20, 0.22, 1.0),
            "conveyor": (0.15, 0.13, 0.11, 1.0),
            "safety_yellow": (0.8, 0.8, 0.1, 0.25),
            "bin_green": (0.1, 0.35, 0.1, 1.0),
            "bin_blue": (0.1, 0.25, 0.35, 1.0),
            "tray_gray": (0.45, 0.45, 0.45, 1.0),
            "component_gold": (0.85, 0.75, 0.25, 1.0),
            "robot_base": (0.25, 0.25, 0.27, 1.0),
            "robot_link": (0.35, 0.37, 0.39, 1.0),
            "robot_joint": (0.45, 0.47, 0.49, 1.0),
            "gripper": (0.55, 0.57, 0.59, 1.0),
            "active_glow": (0.95, 0.75, 0.25, 1.0),
            "ready_pulse": (0.0, 0.8, 0.0, 1.0),
            "busy_pulse": (1.0, 0.6, 0.0, 1.0),
            "solder_effect": (0.9, 0.7, 0.2, 0.8),
        }
        
        # Camera
        self.camera_distance = 18.0
        self.camera_angle_x = 35.0
        self.camera_angle_y = 45.0
        self.last_mouse_pos = None
        
        # Robot joint angles (degrees)
        self.joint_angles = {
            'shoulder_yaw': 0.0,
            'shoulder_pitch': 0.0,
            'elbow_pitch': 0.0,
            'wrist_pitch': 0.0,
            'gripper_open': 0.0  # 0 = closed, 1 = open
        }
        
        # Keyframes for each stage (start and end angles) - updated for 4 stages
        # Stage 0: Pick Component (from bin)
        # Stage 1: Kitting (move to tray)
        # Stage 2: Mounting (position for mounting)
        # Stage 3: Soldering (soldering operation)
        self.keyframes = [
            # Stage 0: Pick Component
            {
                'start': {'shoulder_yaw': -90, 'shoulder_pitch': 20, 'elbow_pitch': 60, 'wrist_pitch': 30, 'gripper_open': 1.0},
                'end': {'shoulder_yaw': -90, 'shoulder_pitch': 45, 'elbow_pitch': 45, 'wrist_pitch': 0, 'gripper_open': 0.0}
            },
            # Stage 1: Kitting (move to tray)
            {
                'start': {'shoulder_yaw': -90, 'shoulder_pitch': 45, 'elbow_pitch': 45, 'wrist_pitch': 0, 'gripper_open': 0.0},
                'end': {'shoulder_yaw': 30, 'shoulder_pitch': 60, 'elbow_pitch': 30, 'wrist_pitch': -10, 'gripper_open': 0.0}
            },
            # Stage 2: Mounting (position over tray)
            {
                'start': {'shoulder_yaw': 30, 'shoulder_pitch': 60, 'elbow_pitch': 30, 'wrist_pitch': -10, 'gripper_open': 0.0},
                'end': {'shoulder_yaw': 30, 'shoulder_pitch': 50, 'elbow_pitch': 40, 'wrist_pitch': 0, 'gripper_open': 1.0}
            },
            # Stage 3: Soldering (soldering operation)
            {
                'start': {'shoulder_yaw': 30, 'shoulder_pitch': 50, 'elbow_pitch': 40, 'wrist_pitch': 0, 'gripper_open': 1.0},
                'end': {'shoulder_yaw': 30, 'shoulder_pitch': 50, 'elbow_pitch': 40, 'wrist_pitch': 0, 'gripper_open': 1.0}
            }
        ]
        
        # Component tracking - NEW STATE MACHINE
        self.component_pos = [0, 0, 0]
        self.component_state = "IN_BIN"  # "IN_BIN", "ATTACHED", "ON_TRAY"
        self.component_visible = False
        self.component_transition_start = 0.0
        self.component_transition_duration = 0.3  # seconds for easing
        self.component_prev_pos = [0, 0, 0]
        self.component_target_pos = [0, 0, 0]
        
        # Inventory system
        self.inventory = {"bin1": 10, "bin2": 10, "bin3": 10}
        self.active_bin = "bin1"
        self.next_bin_index = 0  # For cycling bins
        self.empty_bin_indicator = None  # Track which bin is empty
        
        # Stage visual props
        self.stage_visuals = {
            "bin_highlight": 0.0,  # Pulse intensity for bin highlight
            "tray_highlight": 0.0,  # Pulse intensity for tray
            "clamp_progress": 0.0,  # 0.0 to 1.0 for clamp closing
            "solder_glow": 0.0  # Glow intensity for solder
        }
        
        # Soldering tool position
        self.solder_tool_pos = [0, 0, 0]
        self.solder_tool_active = False
        
        # Interpolation for smoother animations
        self.interp_joint_angles = self.joint_angles.copy()
        self.interp_factor = 0.15  # Faster interpolation for more responsive motion
        
        # GLU quadric for reuse
        self._quadric = None
        
        self.setMouseTracking(True)
    
    def __del__(self):
        """Clean up GLU quadric when widget is destroyed"""
        if hasattr(self, '_quadric') and self._quadric and PYOPENGL_AVAILABLE:
            gluDeleteQuadric(self._quadric)
    
    def smoothstep(self, t):
        """Smoothstep easing function for smooth animations"""
        return t * t * (3 - 2 * t)
    
    def lerp(self, a, b, t):
        """Linear interpolation"""
        return a + (b - a) * t
    
    def compute_active_stage(self):
        """Compute which stage is active and its progress based on animation_time"""
        if not self.proc_active:
            self.active_stage_index = -1
            self.stage_progress = 0.0
            return -1
        
        # If busy but timer ended, stay in stage 3 (Soldering) with stable pose
        if self.animation_time >= self.proc_end:
            if self.current_state['busy']:
                # Stay in stage 3 with stable pose
                self.active_stage_index = 3
                self.stage_progress = 0.9  # Hold at near completion
                return 3
            else:
                self.proc_active = False
                self.active_stage_index = -1
                self.stage_progress = 0.0
                return -1
        
        elapsed = self.animation_time - self.proc_start
        self.active_stage_index = min(3, int(elapsed / self.stage_s))
        
        # Calculate progress within current stage
        stage_start_time = self.proc_start + self.active_stage_index * self.stage_s
        self.stage_progress = min(1.0, max(0.0, (self.animation_time - stage_start_time) / self.stage_s))
        
        return self.active_stage_index
    
    def update_joint_angles(self):
        """Update robot joint angles based on current stage and progress"""
        if self.active_stage_index < 0 or self.active_stage_index > 3:
            # IDLE POSITION: Stable pose, no random motion
            target_angles = {
                'shoulder_yaw': 0.0,
                'shoulder_pitch': 45.0,
                'elbow_pitch': 60.0,
                'wrist_pitch': 0.0,
                'gripper_open': 0.0
            }
        else:
            # Get keyframes for current stage
            keyframe = self.keyframes[self.active_stage_index]
            start = keyframe['start']
            end = keyframe['end']
            
            # Use smoothstep for smooth interpolation
            t = self.smoothstep(self.stage_progress)
            
            # Interpolate between start and end angles
            target_angles = {
                'shoulder_yaw': start['shoulder_yaw'] + (end['shoulder_yaw'] - start['shoulder_yaw']) * t,
                'shoulder_pitch': start['shoulder_pitch'] + (end['shoulder_pitch'] - start['shoulder_pitch']) * t,
                'elbow_pitch': start['elbow_pitch'] + (end['elbow_pitch'] - start['elbow_pitch']) * t,
                'wrist_pitch': start['wrist_pitch'] + (end['wrist_pitch'] - start['wrist_pitch']) * t,
                'gripper_open': start['gripper_open'] + (end['gripper_open'] - start['gripper_open']) * t
            }
            
            # NO vibration or wiggle in any stage - clean deterministic motion only
        
        # Smooth interpolation towards target angles
        for key in self.joint_angles:
            self.joint_angles[key] = self.lerp(
                self.joint_angles[key], 
                target_angles[key], 
                self.interp_factor
            )
    
    def forward_kinematics(self):
        """Calculate end effector position from joint angles"""
        # Simple forward kinematics for visualization
        # Base at (0, 0.5, 0)
        # Link lengths
        L1 = 1.0  # Shoulder to elbow
        L2 = 0.8  # Elbow to wrist
        L3 = 0.3  # Wrist to gripper tip
        
        # Convert angles to radians
        shoulder_yaw = math.radians(self.joint_angles['shoulder_yaw'])
        shoulder_pitch = math.radians(self.joint_angles['shoulder_pitch'])
        elbow_pitch = math.radians(self.joint_angles['elbow_pitch'])
        wrist_pitch = math.radians(self.joint_angles['wrist_pitch'])
        
        # Calculate positions
        x = L1 * math.cos(shoulder_pitch) * math.cos(shoulder_yaw) + L2 * math.cos(shoulder_pitch + elbow_pitch) * math.cos(shoulder_yaw)
        y = 0.5 + L1 * math.sin(shoulder_pitch) + L2 * math.sin(shoulder_pitch + elbow_pitch)
        z = L1 * math.cos(shoulder_pitch) * math.sin(shoulder_yaw) + L2 * math.cos(shoulder_pitch + elbow_pitch) * math.sin(shoulder_yaw)
        
        # Add wrist offset
        x += L3 * math.cos(shoulder_pitch + elbow_pitch + wrist_pitch) * math.cos(shoulder_yaw)
        y += L3 * math.sin(shoulder_pitch + elbow_pitch + wrist_pitch)
        z += L3 * math.cos(shoulder_pitch + elbow_pitch + wrist_pitch) * math.sin(shoulder_yaw)
        
        return [x, y, z]
    
    # ===== OPENGL PRIMITIVES =====
    def draw_box(self, cx, cy, cz, sx, sy, sz, rgba):
        """Draw a solid box centered at (cx, cy, cz) with size (sx, sy, sz)"""
        if not PYOPENGL_AVAILABLE:
            return
            
        glColor4f(*rgba)
        glBegin(GL_QUADS)
        
        # Front face
        glNormal3f(0, 0, 1)
        glVertex3f(cx - sx/2, cy - sy/2, cz + sz/2)
        glVertex3f(cx + sx/2, cy - sy/2, cz + sz/2)
        glVertex3f(cx + sx/2, cy + sy/2, cz + sz/2)
        glVertex3f(cx - sx/2, cy + sy/2, cz + sz/2)
        
        # Back face
        glNormal3f(0, 0, -1)
        glVertex3f(cx - sx/2, cy - sy/2, cz - sz/2)
        glVertex3f(cx - sx/2, cy + sy/2, cz - sz/2)
        glVertex3f(cx + sx/2, cy + sy/2, cz - sz/2)
        glVertex3f(cx + sx/2, cy - sy/2, cz - sz/2)
        
        # Left face
        glNormal3f(-1, 0, 0)
        glVertex3f(cx - sx/2, cy - sy/2, cz - sz/2)
        glVertex3f(cx - sx/2, cy - sy/2, cz + sz/2)
        glVertex3f(cx - sx/2, cy + sy/2, cz + sz/2)
        glVertex3f(cx - sx/2, cy + sy/2, cz - sz/2)
        
        # Right face
        glNormal3f(1, 0, 0)
        glVertex3f(cx + sx/2, cy - sy/2, cz - sz/2)
        glVertex3f(cx + sx/2, cy + sy/2, cz - sz/2)
        glVertex3f(cx + sx/2, cy + sy/2, cz + sz/2)
        glVertex3f(cx + sx/2, cy - sy/2, cz + sz/2)
        
        # Top face
        glNormal3f(0, 1, 0)
        glVertex3f(cx - sx/2, cy + sy/2, cz - sz/2)
        glVertex3f(cx - sx/2, cy + sy/2, cz + sz/2)
        glVertex3f(cx + sx/2, cy + sy/2, cz + sz/2)
        glVertex3f(cx + sx/2, cy + sy/2, cz - sz/2)
        
        # Bottom face
        glNormal3f(0, -1, 0)
        glVertex3f(cx - sx/2, cy - sy/2, cz - sz/2)
        glVertex3f(cx + sx/2, cy - sy/2, cz - sz/2)
        glVertex3f(cx + sx/2, cy - sy/2, cz + sz/2)
        glVertex3f(cx - sx/2, cy - sy/2, cz + sz/2)
        
        glEnd()
    
    def draw_cylinder(self, cx, cy, cz, radius, height, rgba, segments=32):
        """Draw a cylinder aligned with Y axis"""
        if not PYOPENGL_AVAILABLE:
            return
        
        # Ensure quadric exists
        if not self._quadric:
            return
        
        glPushMatrix()
        glTranslatef(cx, cy, cz)
        glRotatef(-90, 1, 0, 0)   # Fix: align Z-axis cylinder to Y-axis
        glColor4f(*rgba)
        gluCylinder(self._quadric, radius, radius, height, segments, 1)
        
        # Draw bottom cap
        gluDisk(self._quadric, 0, radius, segments, 1)
        
        # Draw top cap
        glTranslatef(0, 0, height)
        gluDisk(self._quadric, 0, radius, segments, 1)
        
        glPopMatrix()
    
    def draw_sphere(self, cx, cy, cz, radius, rgba, slices=16, stacks=16):
        """Draw a sphere"""
        if not PYOPENGL_AVAILABLE:
            return
        
        # Ensure quadric exists
        if not self._quadric:
            return
        
        glPushMatrix()
        glTranslatef(cx, cy, cz)
        glColor4f(*rgba)
        gluSphere(self._quadric, radius, slices, stacks)
        glPopMatrix()
    
    def draw_robot(self):
        """Draw the industrial robot arm"""
        if not PYOPENGL_AVAILABLE:
            return
        
        glPushMatrix()
        # Base position
        glTranslatef(0, 0.5, 0)
        
        # Determine robot color based on state
        if self.current_state['fault']:
            base_color = self.colors["red_led"]
            link_color = self.colors["robot_link"]
        elif self.proc_active:
            base_color = self.colors["active_glow"]
            link_color = self.colors["robot_link"]
        else:
            base_color = self.colors["robot_base"]
            link_color = self.colors["robot_link"]
        
        # 1. Base pedestal
        self.draw_cylinder(0, 0, 0, 0.4, 1.0, base_color)
        
        # 2. Shoulder yaw rotation
        glRotatef(self.joint_angles['shoulder_yaw'], 0, 1, 0)
        
        # 3. Shoulder joint (sphere)
        self.draw_sphere(0, 0.5, 0, 0.15, self.colors["robot_joint"])
        
        # 4. Shoulder pitch rotation
        glRotatef(self.joint_angles['shoulder_pitch'], 0, 0, 1)
        
        # 5. Upper arm (from shoulder to elbow)
        glPushMatrix()
        glTranslatef(0, 0.5, 0)
        self.draw_cylinder(0, 0, 0, 0.1, 1.0, link_color)
        
        # 6. Elbow joint (sphere)
        glTranslatef(0, 1.0, 0)
        self.draw_sphere(0, 0, 0, 0.12, self.colors["robot_joint"])
        
        # 7. Elbow pitch rotation
        glRotatef(self.joint_angles['elbow_pitch'], 0, 0, 1)
        
        # 8. Forearm (from elbow to wrist)
        glTranslatef(0, 0, 0)
        self.draw_cylinder(0, 0, 0, 0.08, 0.8, link_color)
        
        # 9. Wrist joint (sphere)
        glTranslatef(0, 0.8, 0)
        self.draw_sphere(0, 0, 0, 0.1, self.colors["robot_joint"])
        
        # 10. Wrist pitch rotation
        glRotatef(self.joint_angles['wrist_pitch'], 0, 0, 1)
        
        # 11. Wrist to gripper
        glTranslatef(0, 0, 0)
        self.draw_cylinder(0, 0, 0, 0.06, 0.3, link_color)
        
        # 12. Gripper
        glTranslatef(0, 0.3, 0)
        gripper_width = 0.15 + 0.1 * self.joint_angles['gripper_open']
        # Left gripper finger
        glPushMatrix()
        glTranslatef(-gripper_width/2, 0, 0)
        self.draw_box(0, 0.1, 0, 0.05, 0.2, 0.03, self.colors["gripper"])
        glPopMatrix()
        
        # Right gripper finger
        glPushMatrix()
        glTranslatef(gripper_width/2, 0, 0)
        self.draw_box(0, 0.1, 0, 0.05, 0.2, 0.03, self.colors["gripper"])
        glPopMatrix()
        
        glPopMatrix()  # Restore to robot base
        
        glPopMatrix()  # Restore to world
    
    def draw_component(self):
        """Draw the component being manipulated with state machine"""
        if not self.component_visible:
            return
        
        # Handle state transitions with easing
        current_time = self.animation_time
        
        # Update position based on state
        if self.component_state == "IN_BIN":
            # Component is in the active bin
            bin_z_positions = {"bin1": -1.5, "bin2": 0, "bin3": 1.5}
            z_pos = bin_z_positions.get(self.active_bin, 0)
            self.component_target_pos = [-2.5, 0.8, z_pos]
            
        elif self.component_state == "ATTACHED":
            # Component is attached to gripper
            gripper_pos = self.forward_kinematics()
            self.component_target_pos = [
                gripper_pos[0],
                gripper_pos[1] - 0.15,  # Slightly below gripper
                gripper_pos[2]
            ]
            
        elif self.component_state == "ON_TRAY":
            # Component is on tray
            self.component_target_pos = [2.5, 0.3, 0]
        
        # Ease position during transitions
        if current_time - self.component_transition_start < self.component_transition_duration:
            t = (current_time - self.component_transition_start) / self.component_transition_duration
            t = self.smoothstep(t)  # Smooth easing
            current_pos = [
                self.component_prev_pos[0] + (self.component_target_pos[0] - self.component_prev_pos[0]) * t,
                self.component_prev_pos[1] + (self.component_target_pos[1] - self.component_prev_pos[1]) * t,
                self.component_prev_pos[2] + (self.component_target_pos[2] - self.component_prev_pos[2]) * t
            ]
        else:
            current_pos = self.component_target_pos
        
        self.component_pos = current_pos
        
        # Draw component as a small gold cube
        self.draw_box(
            self.component_pos[0],
            self.component_pos[1],
            self.component_pos[2],
            0.15, 0.15, 0.15,
            self.colors["component_gold"]
        )
    
    def draw_soldering_effect(self):
        """Draw soldering effect in stage 3 with proper blending"""
        if self.active_stage_index != 3 or self.stage_progress < 0.3:
            return
        
        # Calculate soldering tool position (near component on tray)
        tool_x = 2.5
        tool_y = 0.5
        tool_z = 0
        
        # Save current depth mask state
        glPushAttrib(GL_DEPTH_BUFFER_BIT)
        glDepthMask(GL_FALSE)
        
        # Enable blending for sparks
        glEnable(GL_BLEND)
        glBlendFunc(GL_SRC_ALPHA, GL_ONE_MINUS_SRC_ALPHA)
        
        # Draw soldering tool (opaque)
        glDepthMask(GL_TRUE)
        self.draw_box(
            tool_x, tool_y, tool_z,
            0.08, 0.08, 0.15,
            self.colors["solder_effect"]
        )
        glDepthMask(GL_FALSE)
        
        # Draw soldering spark effect (transparent)
        spark_time = self.animation_time * 5
        spark_alpha = 0.7 + 0.3 * math.sin(spark_time)
        
        # Spark particles
        for i in range(3):
            angle = spark_time + i * 2.0
            spark_x = tool_x + 0.1 * math.cos(angle)
            spark_y = tool_y + 0.05 + 0.1 * math.sin(angle)
            spark_z = tool_z + 0.05 * math.sin(angle * 1.5)
            
            spark_color = (
                1.0,  # R
                0.8 + 0.2 * math.sin(angle * 2),  # G
                0.2,  # B
                spark_alpha * 0.7
            )
            
            self.draw_box(
                spark_x, spark_y, spark_z,
                0.03, 0.03, 0.03,
                spark_color
            )
        
        # Restore state
        glDisable(GL_BLEND)
        glPopAttrib()
    
    def draw_done_pulse(self):
        """Draw done pulse effect"""
        if not PYOPENGL_AVAILABLE:
            return
        
        pulse_progress = (self.animation_time - self.done_pulse_time) / (DONE_PULSE_MS / 1000.0)
        if pulse_progress >= 1.0:
            return
        
        pulse_alpha = 1.0 - pulse_progress
        pulse_radius = 0.5 + pulse_progress * 4.0
        
        # Draw pulsing ring on central table
        glPushMatrix()
        glTranslatef(0, 0.1, 0)
        
        glColor4f(
            self.colors["cyan_pulse"][0],
            self.colors["cyan_pulse"][1],
            self.colors["cyan_pulse"][2],
            pulse_alpha * 0.8
        )
        
        glLineWidth(3.0)
        glBegin(GL_LINE_LOOP)
        segments = 64  # More segments for smoother circle
        for i in range(segments):
            angle = 2.0 * math.pi * i / segments
            x = pulse_radius * math.cos(angle)
            z = pulse_radius * math.sin(angle)
            glVertex3f(x, 0, z)
        glEnd()
        glLineWidth(1.0)
        
        glPopMatrix()
    
    def draw_state_pulses(self):
        """Draw pulse effects for state changes"""
        if not PYOPENGL_AVAILABLE:
            return
        
        # Ready pulse
        ready_progress = (self.animation_time - self.ready_pulse_time) / (DONE_PULSE_MS / 1000.0)
        if ready_progress < 1.0:
            glPushMatrix()
            glTranslatef(-3.0, 2.0, 2.2)  # Ready LED position
            alpha = 1.0 - ready_progress
            scale = 1.0 + ready_progress * 2.0
            glColor4f(
                self.colors["ready_pulse"][0],
                self.colors["ready_pulse"][1],
                self.colors["ready_pulse"][2],
                alpha
            )
            glScalef(scale, scale, scale)
            self.draw_box(0, 0, 0, 0.3, 0.3, 0.1, 
                         (self.colors["ready_pulse"][0],
                          self.colors["ready_pulse"][1],
                          self.colors["ready_pulse"][2],
                          alpha))
            glPopMatrix()
        
        # Busy pulse
        busy_progress = (self.animation_time - self.busy_pulse_time) / (DONE_PULSE_MS / 1000.0)
        if busy_progress < 1.0:
            glPushMatrix()
            glTranslatef(-3.0, 2.0, 1.8)  # Busy LED position
            alpha = 1.0 - busy_progress
            scale = 1.0 + busy_progress * 2.0
            glColor4f(
                self.colors["busy_pulse"][0],
                self.colors["busy_pulse"][1],
                self.colors["busy_pulse"][2],
                alpha
            )
            glScalef(scale, scale, scale)
            self.draw_box(0, 0, 0, 0.3, 0.3, 0.1, 
                         (self.colors["busy_pulse"][0],
                          self.colors["busy_pulse"][1],
                          self.colors["busy_pulse"][2],
                          alpha))
            glPopMatrix()
        
        # Fault pulse
        fault_progress = (self.animation_time - self.fault_pulse_time) / (FAULT_PULSE_MS / 1000.0)
        if fault_progress < 1.0:
            blink = 0.5 + 0.5 * math.sin(self.animation_time * 5)  # Slower, deterministic blink
            fault_color = (
                self.colors["red_led"][0] * blink,
                self.colors["red_led"][1] * blink,
                self.colors["red_led"][2] * blink,
                1.0
            )
            self.draw_box(-3.0, 2.0, 1.4, 0.3, 0.3, 0.1, fault_color)
    
    def draw_stage_visuals(self):
        """Draw visual indicators for each stage"""
        if self.active_stage_index < 0:
            return
        
        # Update stage visual intensities based on progress
        if self.active_stage_index == 0:
            self.stage_visuals["bin_highlight"] = 0.5 + 0.5 * math.sin(self.animation_time * 3)
        elif self.active_stage_index == 1:
            self.stage_visuals["tray_highlight"] = 0.5 + 0.5 * math.sin(self.animation_time * 2)
        elif self.active_stage_index == 2:
            self.stage_visuals["clamp_progress"] = self.stage_progress
        elif self.active_stage_index == 3:
            self.stage_visuals["solder_glow"] = 0.3 + 0.7 * (self.stage_progress ** 0.5)
        
        # Stage 0: Bin highlight
        if self.active_stage_index == 0:
            bin_z_positions = {"bin1": -1.5, "bin2": 0, "bin3": 1.5}
            z_pos = bin_z_positions.get(self.active_bin, 0)
            
            # Draw pulsing ring around active bin
            ring_alpha = self.stage_visuals["bin_highlight"] * 0.5
            ring_color = (0.0, 0.8, 0.8, ring_alpha)
            
            glEnable(GL_BLEND)
            glBlendFunc(GL_SRC_ALPHA, GL_ONE_MINUS_SRC_ALPHA)
            glLineWidth(3.0)
            
            glColor4f(*ring_color)
            glBegin(GL_LINE_LOOP)
            segments = 32
            radius = 0.8
            for i in range(segments):
                angle = 2.0 * math.pi * i / segments
                x = -2.5 + radius * math.cos(angle)
                z = z_pos + radius * math.sin(angle)
                glVertex3f(x, 0.1, z)
            glEnd()
            
            glDisable(GL_BLEND)
            glLineWidth(1.0)
        
        # Stage 1: Tray target highlight
        elif self.active_stage_index == 1:
            # Draw pulsing ring on tray
            ring_alpha = self.stage_visuals["tray_highlight"] * 0.5
            ring_color = (0.0, 0.8, 0.0, ring_alpha)
            
            glEnable(GL_BLEND)
            glBlendFunc(GL_SRC_ALPHA, GL_ONE_MINUS_SRC_ALPHA)
            glLineWidth(3.0)
            
            glColor4f(*ring_color)
            glBegin(GL_LINE_LOOP)
            segments = 32
            radius = 0.6
            for i in range(segments):
                angle = 2.0 * math.pi * i / segments
                x = 2.5 + radius * math.cos(angle)
                z = radius * math.sin(angle)
                glVertex3f(x, 0.15, z)
            glEnd()
            
            glDisable(GL_BLEND)
            glLineWidth(1.0)
        
        # Stage 2: Clamp visualization
        elif self.active_stage_index == 2:
            clamp_progress = self.stage_visuals["clamp_progress"]
            clamp_width = 0.3 * (1.0 - clamp_progress)  # Closes as progress increases
            
            # Draw clamp jaws
            self.draw_box(
                2.5 - clamp_width/2, 0.45, 0,
                0.05, 0.1, 0.2,
                self.colors["robot_joint"]
            )
            self.draw_box(
                2.5 + clamp_width/2, 0.45, 0,
                0.05, 0.1, 0.2,
                self.colors["robot_joint"]
            )
        
        # Stage 3: Solder glow
        elif self.active_stage_index == 3 and self.stage_progress > 0.3:
            glow_intensity = self.stage_visuals["solder_glow"]
            
            # Draw subtle glow on tray under component
            glEnable(GL_BLEND)
            glBlendFunc(GL_SRC_ALPHA, GL_ONE_MINUS_SRC_ALPHA)
            
            glow_color = (0.9, 0.7, 0.2, glow_intensity * 0.3)
            self.draw_box(
                2.5, 0.31, 0,
                0.5, 0.01, 0.5,
                glow_color
            )
            
            glDisable(GL_BLEND)
    
    def draw_inventory_cubes(self):
        """Draw stacked cubes in bins representing inventory"""
        bin_positions = {
            "bin1": (-2.5, 0.6, -1.5),
            "bin2": (-2.5, 0.6, 0),
            "bin3": (-2.5, 0.6, 1.5)
        }
        
        cube_size = 0.12
        cube_spacing = 0.15
        max_display = 8  # Maximum cubes to draw per bin
        
        for bin_name, (x, y_base, z) in bin_positions.items():
            count = self.inventory.get(bin_name, 0)
            display_count = min(count, max_display)
            
            # Draw stacked cubes
            for i in range(display_count):
                row = i // 4
                col = i % 4
                
                cube_x = x - 0.3 + col * cube_spacing
                cube_y = y_base - 0.3 + row * cube_spacing
                cube_z = z - 0.3 + (col % 2) * 0.05  # Stagger slightly
                
                # Different color for empty bins
                if count == 0:
                    cube_color = (0.5, 0.1, 0.1, 1.0)  # Red for empty
                elif bin_name == self.active_bin and self.active_stage_index == 0:
                    cube_color = (0.9, 0.8, 0.2, 1.0)  # Gold for active
                else:
                    cube_color = (0.85, 0.75, 0.25, 1.0)  # Normal gold
                
                self.draw_box(
                    cube_x, cube_y, cube_z,
                    cube_size, cube_size, cube_size,
                    cube_color
                )
            
            # Draw "EMPTY" indicator for empty bins
            if count == 0:
                # Draw red X over bin
                glEnable(GL_BLEND)
                glBlendFunc(GL_SRC_ALPHA, GL_ONE_MINUS_SRC_ALPHA)
                glLineWidth(3.0)
                
                glColor4f(0.9, 0.1, 0.1, 0.8)
                glBegin(GL_LINES)
                # Diagonal lines forming X
                glVertex3f(x - 0.5, y_base, z - 0.5)
                glVertex3f(x + 0.5, y_base, z + 0.5)
                glVertex3f(x + 0.5, y_base, z - 0.5)
                glVertex3f(x - 0.5, y_base, z + 0.5)
                glEnd()
                
                glLineWidth(1.0)
                glDisable(GL_BLEND)
    
    def set_active_bin(self, new_bin):
        """Set active bin and handle empty bin logic"""
        if new_bin in self.inventory:
            old_bin = self.active_bin
            self.active_bin = new_bin
            
            # Mark old bin as empty if needed
            if self.inventory.get(old_bin, 0) <= 0:
                self.empty_bin_indicator = old_bin
            else:
                self.empty_bin_indicator = None
    
    # ===== MAIN OPENGL METHODS =====
    def initializeGL(self):
        if PYOPENGL_AVAILABLE:
            glEnable(GL_DEPTH_TEST)
            glEnable(GL_LIGHTING)
            glEnable(GL_LIGHT0)
            glEnable(GL_LIGHT1)
            glEnable(GL_COLOR_MATERIAL)
            glColorMaterial(GL_FRONT_AND_BACK, GL_AMBIENT_AND_DIFFUSE)
            glEnable(GL_NORMALIZE)
            glEnable(GL_MULTISAMPLE)
            glEnable(GL_LINE_SMOOTH)
            glEnable(GL_POLYGON_SMOOTH)
            glHint(GL_LINE_SMOOTH_HINT, GL_NICEST)
            glHint(GL_POLYGON_SMOOTH_HINT, GL_NICEST)
            
            # Setup lighting for industrial look
            glLightfv(GL_LIGHT0, GL_POSITION, [10.0, 15.0, 10.0, 1.0])
            glLightfv(GL_LIGHT0, GL_AMBIENT, [0.1, 0.1, 0.1, 1.0])
            glLightfv(GL_LIGHT0, GL_DIFFUSE, [0.8, 0.8, 0.8, 1.0])
            glLightfv(GL_LIGHT0, GL_SPECULAR, [0.4, 0.4, 0.4, 1.0])
            
            # Second light for fill lighting
            glLightfv(GL_LIGHT1, GL_POSITION, [-10.0, 15.0, -10.0, 1.0])
            glLightfv(GL_LIGHT1, GL_DIFFUSE, [0.3, 0.3, 0.3, 1.0])
            glLightfv(GL_LIGHT1, GL_SPECULAR, [0.1, 0.1, 0.1, 1.0])
            
            # Material properties for metallic look
            glMaterialfv(GL_FRONT, GL_SPECULAR, [0.6, 0.6, 0.6, 1.0])
            glMaterialf(GL_FRONT, GL_SHININESS, 60.0)
            
            # Enable smooth shading
            glShadeModel(GL_SMOOTH)
            
            # Create reusable quadric
            self._quadric = gluNewQuadric()
            gluQuadricNormals(self._quadric, GLU_SMOOTH)
            gluQuadricTexture(self._quadric, GL_FALSE)
    
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
            glClearColor(0.1, 0.1, 0.12, 1.0)  # Darker background matching ST2
            glClear(GL_COLOR_BUFFER_BIT | GL_DEPTH_BUFFER_BIT)
            glLoadIdentity()
            
            # Camera positioning (orbit around center)
            cam_x = self.camera_distance * math.cos(math.radians(self.camera_angle_y)) * math.cos(math.radians(self.camera_angle_x))
            cam_y = self.camera_distance * math.sin(math.radians(self.camera_angle_x))
            cam_z = self.camera_distance * math.sin(math.radians(self.camera_angle_y)) * math.cos(math.radians(self.camera_angle_x))
            
            gluLookAt(
                cam_x, cam_y, cam_z,
                0, 1, 0,  # Look at center of scene
                0, 1, 0
            )
            
            self.draw_scene()
            
            # Draw overlay using QPainter
            painter = QPainter(self)
            painter.setRenderHint(QPainter.Antialiasing)
            painter.setRenderHint(QPainter.TextAntialiasing)
            self.draw_overlay(painter)
            painter.end()
                
        except Exception as e:
            print(f"OpenGL error: {e}")
            traceback.print_exc()
    
    def paintBasic(self):
        """Basic painting when OpenGL is not available"""
        painter = QPainter(self)
        painter.fillRect(self.rect(), QColor(20, 20, 25))
        
        # Draw overlay
        self.draw_overlay(painter)
        painter.end()
    
    def draw_scene(self):
        """Draw the complete industrial robot cell"""
        # Apply shake effect if fault (subtle)
        if self.current_state['fault']:
            shake_intensity = 0.03
            shake_x = shake_intensity * math.sin(self.animation_time * 5)  # Slower, deterministic
            shake_y = shake_intensity * math.cos(self.animation_time * 4)
            glTranslatef(shake_x, shake_y, 0)
        
        # Draw floor grid
        self.draw_grid()
        
        # ===== FACTORY STATION STRUCTURE =====
        # 1. Main work table
        self.draw_box(0, 0.1, 0, 8, 0.2, 5, self.colors["dark_gray"])
        
        # 2. Conveyor belt at back
        self.draw_box(0, 0.3, 2.8, 7, 0.3, 0.5, self.colors["conveyor"])
        
        # 3. Component bins (left side)
        self.draw_box(-2.5, 0.6, -1.5, 1.2, 0.8, 1.2, self.colors["bin_green"])
        self.draw_box(-2.5, 0.6, 0, 1.2, 0.8, 1.2, self.colors["bin_blue"])
        self.draw_box(-2.5, 0.6, 1.5, 1.2, 0.8, 1.2, self.colors["bin_green"])
        
        # 4. Kit tray area (right side) - where component is placed
        self.draw_box(2.5, 0.3, 0, 1.5, 0.1, 2, self.colors["tray_gray"])
        
        # 5. Safety frame (transparent yellow)
        glEnable(GL_BLEND)
        glBlendFunc(GL_SRC_ALPHA, GL_ONE_MINUS_SRC_ALPHA)
        # Draw safety frame posts
        for x in [-3.5, 3.5]:
            for z in [-2.5, 2.5]:
                self.draw_box(x, 1.5, z, 0.1, 3.0, 0.1, self.colors["safety_yellow"])
        glDisable(GL_BLEND)
        
        # ===== UPDATE ANIMATION STATE =====
        self.compute_active_stage()
        self.update_joint_angles()
        
        # ===== DRAW INVENTORY CUBES =====
        self.draw_inventory_cubes()
        
        # ===== UPDATE COMPONENT STATE MACHINE =====
        if self.proc_active:
            # Handle state transitions based on stage progress
            if self.active_stage_index == 0 and self.stage_progress > 0.55:
                if self.component_state != "ATTACHED":
                    self.component_state = "ATTACHED"
                    self.component_transition_start = self.animation_time
                    self.component_prev_pos = self.component_pos.copy()
                    self.component_visible = True
            
            elif self.active_stage_index == 2 and self.stage_progress > 0.70:
                if self.component_state != "ON_TRAY":
                    self.component_state = "ON_TRAY"
                    self.component_transition_start = self.animation_time
                    self.component_prev_pos = self.component_pos.copy()
        
        # ===== STATUS INDICATORS =====
        # Ready/Busy/Fault LED panel with pulses
        led_y = 2.0
        if self.current_state['ready']:
            self.draw_box(-3.0, led_y, 2.2, 0.3, 0.3, 0.1, self.colors["green_led"])
        if self.current_state['busy']:
            self.draw_box(-3.0, led_y, 1.8, 0.3, 0.3, 0.1, self.colors["amber_led"])
        
        # ===== DRAW ROBOT =====
        self.draw_robot()
        
        # ===== DRAW COMPONENT =====
        self.draw_component()
        
        # ===== DRAW STAGE VISUALS =====
        self.draw_stage_visuals()
        
        # ===== STAGE-SPECIFIC EFFECTS =====
        if self.active_stage_index == 3:  # Soldering
            self.draw_soldering_effect()
        
        # ===== STATE PULSE EFFECTS =====
        self.draw_state_pulses()
        
        # ===== DONE PULSE EFFECT =====
        if self.animation_time - self.done_pulse_time < DONE_PULSE_MS / 1000.0:
            self.draw_done_pulse()
        
    def draw_grid(self):
        """Draw industrial floor grid"""
        if not PYOPENGL_AVAILABLE:
            return
            
        glColor4f(*self.colors["grid"])
        glLineWidth(1.0)
        glBegin(GL_LINES)
        
        size = 20.0
        steps = 40
        
        for i in range(-steps, steps + 1):
            x = i * (size / steps)
            glVertex3f(x, 0, -size/2)
            glVertex3f(x, 0, size/2)
            glVertex3f(-size/2, 0, x)
            glVertex3f(size/2, 0, x)
        
        glEnd()
        
        # Draw thicker center lines
        glLineWidth(2.0)
        glBegin(GL_LINES)
        glVertex3f(-size/2, 0.01, 0)
        glVertex3f(size/2, 0.01, 0)
        glVertex3f(0, 0.01, -size/2)
        glVertex3f(0, 0.01, size/2)
        glEnd()
    
    def draw_overlay(self, painter):
        """Draw overlay text with system information"""
        # Setup font
        font = QFont("Segoe UI", 9)  # Cleaner font than monospace
        painter.setFont(font)
        painter.setPen(QPen(QColor(240, 240, 240), 1))
        
        # Mode and state - use current_mode from MainWindow
        mode_text = f"Mode: {self.mode}"
        
        # Create state "pills" like ST2
        states = []
        if self.current_state['ready']:
            states.append(("Ready", QColor(0, 200, 0)))
        if self.current_state['busy']:
            states.append(("Busy", QColor(255, 165, 0)))
        if self.current_state['done']:
            states.append(("Done", QColor(0, 180, 255)))
        if self.current_state['fault']:
            states.append(("Fault", QColor(255, 50, 50)))
        
        state_text = "State: " + " ".join([s[0] for s in states]) if states else "State: Idle"
        
        # Get current completed count for display
        completed = self.current_state['extra'].get('total_completed', 0)
        total = self.current_state['extra'].get('total', 'N/A')
        
        # Use animation time for display
        now_text = f"Visual Time: {self.animation_time:.1f}s"
            
        info_text = f"Completed: {completed}/{total} | {now_text}"
        
        # Active stage
        active_stage = "Idle"
        stage_color = QColor(200, 200, 200)
        if self.active_stage_index >= 0 and self.active_stage_index < 4:
            active_stage = self.stage_names[self.active_stage_index]
            stage_color = QColor(255, 215, 0)  # Gold for active
            
            # Add progress percentage
            active_stage += f" ({self.stage_progress*100:.0f}%)"
        
        stage_text = f"Active Stage: {active_stage}"
        
        # Cycle time
        cycle_text = f"Cycle: {self.current_state['cycle_time_ms'] or 'N/A'} ms"
        stage_dur_text = f"Stage Dur: {self.stage_s:.1f}s"
        
        # Draw text with background for readability
        y_offset = 20
        line_height = 22
        
        texts = [mode_text, state_text, info_text, stage_text, cycle_text, stage_dur_text]
        
        # Draw state pills
        pill_x = 15
        pill_y = y_offset + line_height - 12
        pill_height = 18
        
        for state_name, color in states:
            metrics = QFontMetrics(font)
            text_width = metrics.horizontalAdvance(state_name) + 20
            
            # Draw pill background
            painter.setBrush(QBrush(color))
            painter.setPen(QPen(color.darker(150), 1))
            painter.drawRoundedRect(pill_x, pill_y, text_width, pill_height, 9, 9)
            
            # Draw pill text
            painter.setPen(QPen(QColor(255, 255, 255), 1))
            painter.drawText(pill_x + 10, pill_y + pill_height - 5, state_name)
            
            pill_x += text_width + 8
        
        # Draw other text
        for i, text in enumerate(texts):
            # Draw background rectangle
            metrics = QFontMetrics(font)
            text_width = metrics.horizontalAdvance(text)
            painter.fillRect(10, y_offset + i * line_height - 15, 
                           text_width + 12, line_height, 
                           QColor(0, 0, 0, 180))
            
            # Draw text
            if i == 3:  # Stage text
                painter.setPen(QPen(stage_color, 1))
            else:
                painter.setPen(QPen(QColor(240, 240, 240), 1))
            painter.drawText(15, y_offset + i * line_height, text)
    
    def mousePressEvent(self, event):
        self.last_mouse_pos = event.position()
    
    def mouseMoveEvent(self, event):
        if self.last_mouse_pos and event.buttons() & Qt.LeftButton:
            dx = event.position().x() - self.last_mouse_pos.x()
            dy = event.position().y() - self.last_mouse_pos.y()
            
            self.camera_angle_y += dx * 0.5
            self.camera_angle_x = max(-90, min(90, self.camera_angle_x - dy * 0.5))
            
            self.last_mouse_pos = event.position()
            self.update()
    
    def wheelEvent(self, event):
        delta = event.angleDelta().y()
        self.camera_distance = max(8.0, min(30.0, self.camera_distance - delta * 0.01))
        self.update()
    
    def update_state(self, event: ST1Event, mode: str = "LIVE", visual_time_s: float = None):
        """Update the current state from an event"""
        old_ready = self.current_state.get('ready', False)
        old_busy = self.current_state.get('busy', False)
        old_done = self.current_state.get('_last_done', False)
        old_fault = self.current_state.get('fault', False)
        old_completed = self.current_state.get('extra', {}).get('total_completed', 0)
        
        self.current_state = {
            'ready': event.ready,
            'busy': event.busy,
            'done': event.done,
            'fault': event.fault,
            'cycle_time_ms': event.cycle_time_ms,
            'extra': event.extra
        }
        
        self.mode = mode
        
        # Use provided visual_time_s or fallback to current animation time (deterministic)
        if visual_time_s is None:
            visual_time_s = self.animation_time
        
        # Debug print for each event
        if self.DEBUG:
            cmd_start = event.extra.get('cmd_start', 0)
            batch_id = event.extra.get('batch_id', 'N/A')
            print(f"ST1 Event: t={event.t_ns/1e9:.3f}s, busy={event.busy}, done={event.done}, ready={event.ready}, cmd_start={cmd_start}, batch_id={batch_id}")
        
        # Track if this is the first event we've seen
        if not self.has_seen_first_event:
            self.has_seen_first_event = True
            if self.DEBUG:
                print(f"ST1: First event received, busy={event.busy}")
        
        # Trigger pulse effects for state changes
        if event.ready and not old_ready:
            self.ready_pulse_time = visual_time_s
        if event.busy and not old_busy:
            self.busy_pulse_time = visual_time_s
            
            # Handle inventory on busy rising edge
            if self.inventory.get(self.active_bin, 0) > 0:
                self.inventory[self.active_bin] -= 1
            else:
                # Mark fault if trying to pick from empty bin
                self.current_state['fault'] = True
            
            # Cycle to next bin
            bin_order = ["bin1", "bin2", "bin3"]
            current_idx = bin_order.index(self.active_bin) if self.active_bin in bin_order else 0
            next_idx = (current_idx + 1) % 3
            self.set_active_bin(bin_order[next_idx])
            
        if event.fault and not old_fault:
            self.fault_pulse_time = visual_time_s
        
        # Check for cycle start conditions
        current_completed = event.extra.get('total_completed', 0)
        cycle_start_reason = None
        
        # Condition 1: busy rising edge (normal start)
        if event.busy and not old_busy:
            cycle_start_reason = "busy_edge"
            
        # Condition 2: cmd_start rising edge (if available in logs)
        elif 'cmd_start' in event.extra:
            cmd_start = event.extra.get('cmd_start', 0)
            old_cmd_start = self.current_state.get('extra', {}).get('cmd_start', 0)
            if cmd_start and not old_cmd_start:
                cycle_start_reason = "cmd_start_edge"
                
        # Condition 3: First event and already busy (attach mid-cycle)
        elif not self.has_seen_first_event and event.busy:
            cycle_start_reason = "attach_mid_cycle"
        
        # If any start condition is met, begin the cycle
        if cycle_start_reason and not self.proc_active:
            if self.DEBUG:
                print(f"ST1: Starting cycle due to: {cycle_start_reason}")
            
            self.proc_active = True
            
            # Calculate stage duration
            if event.cycle_time_ms:
                total_cycle_s = event.cycle_time_ms / 1000.0
                calculated_stage_s = total_cycle_s / 4.0
                self.stage_s = max(0.5, min(6.0, calculated_stage_s))
            else:
                self.stage_s = self.base_stage_s
            
            # Handle different start scenarios
            if cycle_start_reason == "busy_edge" or cycle_start_reason == "cmd_start_edge":
                # Normal start at beginning of cycle
                self.proc_start = visual_time_s
                self.active_stage_index = -1
                self.stage_progress = 0.0
                
                # Initialize component state for new cycle
                self.component_visible = True
                self.component_state = "IN_BIN"
                self.component_transition_start = visual_time_s
                self.component_prev_pos = self.component_pos.copy()
                
            elif cycle_start_reason == "attach_mid_cycle":
                # We attached in the middle of a cycle - estimate progress
                # Assume we're about halfway through the cycle
                estimated_progress = 0.5
                estimated_elapsed = estimated_progress * 4 * self.stage_s
                
                self.proc_start = visual_time_s - estimated_elapsed
                
                # Initialize component state based on estimated progress
                self.component_visible = True
                estimated_stage = min(3, int(estimated_elapsed / self.stage_s))
                
                if estimated_stage >= 2:
                    self.component_state = "ON_TRAY"
                    self.component_pos = [2.5, 0.3, 0]
                elif estimated_stage >= 1:
                    self.component_state = "ATTACHED"
                else:
                    self.component_state = "IN_BIN"
                
                self.component_transition_start = visual_time_s
                self.component_prev_pos = self.component_pos.copy()
                
                if self.DEBUG:
                    print(f"ST1: Attached mid-cycle, estimated stage {estimated_stage}")
            
            self.proc_end = self.proc_start + 4 * self.stage_s
        
        # Stop processing on done rising edge OR completed counter increase
        if (event.done and not old_done) or (current_completed > old_completed):
            if event.done and not old_done:
                self.done_pulse_time = visual_time_s
                if self.DEBUG:
                    print("ST1: Cycle ended (done rising edge)")
            self.proc_active = False
            self.active_stage_index = -1
            self.stage_progress = 0.0
            self.component_visible = False
        
        # On fault: stop processing and show FAIL
        if event.fault:
            if self.DEBUG:
                print("ST1: Cycle ended (fault)")
            self.proc_active = False
            self.active_stage_index = -1
            self.stage_progress = 0.0
            self.component_visible = False
        
        # Store last done state
        self.current_state['_last_done'] = event.done
        
        # Update animation time
        self.animation_time = visual_time_s
        
        self.update()

# ===== MAIN WINDOW =====
class MainWindow(QMainWindow):
    def __init__(self):
        super().__init__()
        self.setWindowTitle("ST1 Component Kitting Visualizer - Industrial Robot Cell")
        self.setGeometry(100, 100, 1400, 900)
        
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
        self.last_update_time = 0  # For debouncing
        self.worker_state = "stopped"  # Track tail worker state
        
        # Deterministic time tracking for LIVE mode
        self.live_t0_wall = 0.0  # Monotonic time when LIVE mode started
        self.live_t0_visual = 0.0  # Visual time when LIVE mode started
        
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
    
    def get_visual_time_s(self):
        """Get the current visual time in seconds for deterministic animations"""
        if self.is_live_mode:
            # In LIVE mode, use monotonic wall time relative to when LIVE mode started
            if self.live_t0_wall == 0:
                self.live_t0_wall = time.monotonic()
                self.live_t0_visual = self.gl_widget.animation_time
            return (time.monotonic() - self.live_t0_wall) + self.live_t0_visual
        else:
            # In REPLAY mode, use scaled VSI time
            if not self.replay_events:
                return (self.current_time_ns - self.replay_min_time) / 1e9
            
            # Find current event
            current_event = None
            for event in self.replay_events:
                if event.t_ns <= self.current_time_ns:
                    current_event = event
                else:
                    break
            
            if current_event:
                # Use VSI time scaled to seconds for replay
                return (current_event.t_ns - self.replay_min_time) / 1e9
            
            return (self.current_time_ns - self.replay_min_time) / 1e9
    
    def init_ui(self):
        # Central widget
        central_widget = QWidget()
        self.setCentralWidget(central_widget)
        
        # Apply dark theme
        self.setStyleSheet("""
            QMainWindow {
                background-color: #1e1e1e;
            }
            QWidget {
                background-color: #2d2d30;
                color: #ffffff;
            }
            QGroupBox {
                font-weight: bold;
                border: 1px solid #555555;
                border-radius: 4px;
                margin-top: 10px;
                padding-top: 10px;
            }
            QGroupBox::title {
                subcontrol-origin: margin;
                left: 10px;
                padding: 0 5px 0 5px;
            }
            QLabel {
                color: #cccccc;
            }
            QPushButton {
                background-color: #3e3e42;
                border: 1px solid #555555;
                border-radius: 3px;
                padding: 5px 15px;
                min-width: 80px;
            }
            QPushButton:hover {
                background-color: #505050;
            }
            QPushButton:pressed {
                background-color: #007acc;
            }
            QPushButton:disabled {
                background-color: #2d2d30;
                color: #666666;
            }
            QComboBox {
                background-color: #3e3e42;
                border: 1px solid #555555;
                border-radius: 3px;
                padding: 3px;
                min-width: 60px;
            }
            QSlider::groove:horizontal {
                background: #404040;
                height: 6px;
                border-radius: 3px;
            }
            QSlider::handle:horizontal {
                background: #007acc;
                width: 16px;
                height: 16px;
                margin: -5px 0;
                border-radius: 8px;
            }
            QProgressBar {
                border: 1px solid #555555;
                border-radius: 3px;
                text-align: center;
                background-color: #3e3e42;
            }
            QProgressBar::chunk {
                background-color: #007acc;
                border-radius: 2px;
            }
        """)
        
        # Main layout
        main_layout = QVBoxLayout(central_widget)
        main_layout.setSpacing(8)
        main_layout.setContentsMargins(10, 10, 10, 10)
        
        # Top info bar
        info_layout = QHBoxLayout()
        info_layout.setSpacing(15)
        
        self.log_info_label = QLabel("Searching for ST1 Component Kitting log...")
        self.log_info_label.setStyleSheet("font-weight: bold; color: #4fc3f7; padding: 5px;")
        info_layout.addWidget(self.log_info_label)
        
        self.event_count_label = QLabel("Raw: 0 | Accepted: 0")
        self.event_count_label.setStyleSheet("font-family: 'Consolas', monospace; padding: 5px;")
        info_layout.addWidget(self.event_count_label)
        
        # Debug/Status label with more info (like ST2)
        self.debug_label = QLabel("Mode: LIVE | Worker: stopped | Log: N/A | Last Event: N/A")
        self.debug_label.setStyleSheet("font-family: 'Consolas', monospace; padding: 5px; color: #cccccc; background-color: #252526; border-radius: 3px;")
        info_layout.addWidget(self.debug_label)
        
        info_layout.addStretch()
        main_layout.addLayout(info_layout)
        
        # Center and right panel
        content_layout = QHBoxLayout()
        content_layout.setSpacing(15)
        
        # OpenGL widget (center) - expanded slightly
        self.gl_widget = ST1OpenGLWidget()
        content_layout.addWidget(self.gl_widget, 4)  # Increased from 3 to 4
        
        # Status panel (right)
        status_panel = QVBoxLayout()
        status_panel.setSpacing(10)
        
        # Component info group
        info_group = QGroupBox("Component / Kit Info")
        info_layout = QVBoxLayout()
        info_layout.setSpacing(5)
        
        self.total_label = QLabel("Total: N/A")
        self.completed_label = QLabel("Completed: N/A")
        self.now_label = QLabel("Now: --:--:--")
        
        for label in [self.total_label, self.completed_label, self.now_label]:
            label.setStyleSheet("font-family: 'Consolas', monospace; padding: 3px;")
            info_layout.addWidget(label)
        
        info_group.setLayout(info_layout)
        status_panel.addWidget(info_group)
        
        # State indicators with pill styling
        state_group = QGroupBox("ST1 State Indicators")
        state_layout = QGridLayout()
        state_layout.setSpacing(8)
        state_layout.setContentsMargins(10, 15, 10, 10)
        
        self.ready_indicator = QLabel("● Ready")
        self.busy_indicator = QLabel("● Busy")
        self.done_indicator = QLabel("● Done")
        self.fault_indicator = QLabel("● Fault")
        
        indicators = [self.ready_indicator, self.busy_indicator, 
                     self.done_indicator, self.fault_indicator]
        
        for i, indicator in enumerate(indicators):
            indicator.setStyleSheet("""
                QLabel {
                    font-weight: bold;
                    font-size: 11px;
                    padding: 6px 12px;
                    border-radius: 10px;
                    background-color: #3e3e42;
                    color: #888888;
                }
            """)
            row = i // 2
            col = i % 2
            state_layout.addWidget(indicator, row, col)
        
        self.cycle_label = QLabel("Cycle: N/A ms")
        self.cycle_label.setStyleSheet("font-family: 'Consolas', monospace; padding: 8px; background-color: #252526; border-radius: 4px;")
        state_layout.addWidget(self.cycle_label, 2, 0, 1, 2)
        
        state_group.setLayout(state_layout)
        status_panel.addWidget(state_group)
        
        # Stage info
        stage_group = QGroupBox("Kitting Status")
        stage_layout = QVBoxLayout()
        stage_layout.setSpacing(8)
        
        self.stage_status_label = QLabel("Active Stage: Idle")
        self.stage_status_label.setStyleSheet("font-weight: bold; font-size: 12px; padding: 5px;")
        stage_layout.addWidget(self.stage_status_label)
        
        # Progress bar with better styling
        self.progress_bar = QProgressBar()
        self.progress_bar.setRange(0, 100)
        self.progress_bar.setValue(0)
        self.progress_bar.setTextVisible(True)
        self.progress_bar.setFormat("%p%")
        stage_layout.addWidget(self.progress_bar)
        
        stage_group.setLayout(stage_layout)
        status_panel.addWidget(stage_group)
        
        # Result display
        result_group = QGroupBox("Kit Result")
        result_layout = QVBoxLayout()
        result_layout.setSpacing(5)
        
        self.result_label = QLabel("Result: N/A")
        self.pass_count_label = QLabel("Pass Count: N/A")
        
        for label in [self.result_label, self.pass_count_label]:
            label.setStyleSheet("font-family: 'Consolas', monospace; padding: 3px;")
            result_layout.addWidget(label)
        
        result_group.setLayout(result_layout)
        status_panel.addWidget(result_group)
        
        # Extra KPIs with scrolling
        self.extra_group = QGroupBox("Extra Signals")
        self.extra_layout = QVBoxLayout()
        self.extra_layout.setSpacing(3)
        self.extra_group.setLayout(self.extra_layout)
        status_panel.addWidget(self.extra_group)
        
        status_panel.addStretch()
        content_layout.addLayout(status_panel, 1)
        
        main_layout.addLayout(content_layout, 1)
        
        # Bottom controls
        controls_layout = QHBoxLayout()
        controls_layout.setSpacing(10)
        
        # Live/Replay toggle with better styling
        toggle_layout = QHBoxLayout()
        toggle_layout.setSpacing(5)
        toggle_layout.addWidget(QLabel("Mode:"))
        self.live_toggle = QCheckBox("LIVE")
        self.live_toggle.setChecked(True)
        self.live_toggle.setStyleSheet("""
            QCheckBox {
                spacing: 8px;
                font-weight: bold;
            }
            QCheckBox::indicator {
                width: 18px;
                height: 18px;
            }
            QCheckBox::indicator:checked {
                background-color: #007acc;
                border: 2px solid #007acc;
                border-radius: 3px;
            }
        """)
        self.live_toggle.stateChanged.connect(self.on_live_toggled)
        toggle_layout.addWidget(self.live_toggle)
        controls_layout.addLayout(toggle_layout)
        
        # Play/Pause
        self.play_button = QPushButton("⏸")
        self.play_button.clicked.connect(self.toggle_play)
        self.play_button.setEnabled(False)
        self.play_button.setFixedWidth(40)
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
        self.time_label.setStyleSheet("font-family: 'Consolas', monospace; padding: 5px 10px; background-color: #252526; border-radius: 3px;")
        self.time_label.setFixedWidth(120)
        controls_layout.addWidget(self.time_label)
        
        # Reload button
        reload_button = QPushButton("Reload Log")
        reload_button.clicked.connect(self.discover_log)
        reload_button.setFixedWidth(100)
        controls_layout.addWidget(reload_button)
        
        main_layout.addLayout(controls_layout)
        
        # Update indicator colors
        self.update_indicator_colors()
    
    def update_indicator_colors(self):
        """Update the state indicator colors based on current state"""
        # This will be called when state changes
        pass
    
    def _stop_tail_worker(self):
        """Safely stop the tail worker if it exists (matching ST2 logic)"""
        if self.tail_worker:
            print("Stopping tail worker...")
            self.tail_worker.stop()
            # Don't wait indefinitely - use a short timeout like ST2
            if self.tail_worker.isRunning():
                self.tail_worker.wait(1000)  # Wait up to 1 second
            self.tail_worker = None
            self.worker_state = "stopped"
            self.update_debug_label()
    
    def load_live_snapshot(self) -> Tuple[Optional[ST1Event], int]:
        """Load snapshot of last N lines from log file, return latest event and raw count"""
        if not self.log_path or not os.path.exists(self.log_path):
            return None, 0
        
        try:
            with open(self.log_path, 'r', encoding='utf-8', errors='ignore') as f:
                # Read last N lines efficiently
                lines = collections.deque(f, maxlen=SNAPSHOT_LINES)
            
            parser = ST1LogParser()
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
        """Discover and load ST1 log file"""
        # Stop current worker
        self._stop_tail_worker()
        
        # Clear replay data
        self.replay_events = []
        
        # Find log
        self.log_path = LogDiscoverer.find_st1_log()
        
        if self.log_path:
            base_name = os.path.basename(self.log_path)
            self.log_info_label.setText(f"ST1 Log: {base_name}")
            
            # Reset counters
            self.raw_event_count = 0
            self.accepted_event_count = 0
            self.update_event_count_label()
            
            if self.is_live_mode:
                self.switch_to_live()
            else:
                self.switch_to_replay()
        else:
            self.log_info_label.setText("No ST1 log found")
            self.log_path = None
            self.replay_events = []
            self.update_debug_label()
    
    def switch_to_live(self):
        """Switch to live mode (tail log) - FIXED to match ST2 logic"""
        print("Switching to LIVE mode...")
        
        # Stop replay if active
        if not self.is_live_mode:
            self.is_playing = False
            self.play_button.setText("▶")
            self.play_button.setEnabled(False)
            self.speed_combo.setEnabled(False)
            self.timeline_slider.setEnabled(False)
        
        # Clear replay data
        self.replay_events = []
        self.current_time_ns = 0
        
        # Update UI for LIVE mode
        self.current_mode = "LIVE"
        self.is_live_mode = True
        self.live_toggle.setChecked(True)
        
        # Reset deterministic time tracking for LIVE mode
        self.live_t0_wall = time.monotonic()
        self.live_t0_visual = 0.0
        
        if not self.log_path:
            self.update_debug_label()
            return
        
        # Stop any existing worker first (like ST2 does)
        self._stop_tail_worker()
        
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
            
            # Get current visual time for animation (deterministic)
            visual_time_s = time.monotonic() - self.live_t0_wall
            self.gl_widget.animation_time = visual_time_s
            
            # Update widget state with visual time
            self.gl_widget.update_state(latest_event, self.current_mode, visual_time_s)
            self.update_display(latest_event, from_snapshot=True)
            
            # Update debug label with snapshot info
            self.last_event_time_ns = latest_event.t_ns
            self.worker_state = "starting"
            self.update_debug_label()
            
            # Start tail worker with seeded parser (like ST2)
            self.tail_worker = LogTailWorker(self.log_path, seed_event=latest_event)
        else:
            self.debug_label.setText("Mode: LIVE | Last Event: NONE (no parsable state lines yet)")
            self.last_state_snapshot = None
            self.worker_state = "starting"
            self.update_debug_label()
            # Start tail worker without seed
            self.tail_worker = LogTailWorker(self.log_path)
        
        # Connect signals (like ST2)
        self.tail_worker.new_event.connect(self.process_new_event)
        self.tail_worker.activity_detected.connect(self.on_activity_detected)
        self.tail_worker.file_reopened.connect(self.on_file_reopened)
        self.tail_worker.worker_stopped.connect(self.on_worker_stopped)
        self.tail_worker.start()
        
        self.worker_state = "running"
        self.update_debug_label()
        
        self.last_activity_time = time.time()
        self.is_idle = False
        self.idle_start_time = 0.0
        self.last_update_time = time.time()
        
        print("LIVE mode started")
    
    def switch_to_replay(self):
        """Switch to replay mode (load full file) - FIXED to match ST2 logic"""
        print("Switching to REPLAY mode...")
        
        # Stop any existing worker (like ST2 does)
        self._stop_tail_worker()
        
        # Update UI for REPLAY mode
        self.current_mode = "REPLAY"
        self.is_live_mode = False
        self.live_toggle.setChecked(False)
        self.timeline_slider.setEnabled(True)
        self.speed_combo.setEnabled(True)
        self.play_button.setEnabled(True)
        self.is_playing = True
        self.play_button.setText("⏸")
        self.is_idle = False
        self.idle_start_time = 0.0
        self.worker_state = "N/A"
        
        # Reset LIVE mode time tracking
        self.live_t0_wall = 0.0
        self.live_t0_visual = 0.0
        
        if not self.log_path:
            self.update_debug_label()
            return
        
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
            self.gl_widget.compute_active_stage()
            
            # Force immediate display update with initial state
            self.update_states_from_replay()
            
            # Update debug label for REPLAY mode
            self.update_debug_label()
        else:
            self.debug_label.setText("Mode: REPLAY | No events loaded")
        
        print(f"REPLAY mode started with {len(self.replay_events)} events")
    
    def load_replay_data(self):
        """Load all events from log file for replay and compute accepted_event_count"""
        try:
            with open(self.log_path, 'r', encoding='utf-8', errors='ignore') as f:
                lines = f.readlines()
            
            events = []
            parser = ST1LogParser()
            
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
            
            print(f"Loaded {len(self.replay_events)} ST1 events for replay")
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
            # Get visual time for animation
            visual_time_s = self.get_visual_time_s()
            
            # Update widget state with visual time
            self.gl_widget.update_state(current_event, self.current_mode, visual_time_s)
            
            # Update display
            self.update_display(current_event, from_snapshot=False)
            
            # Update debug label for REPLAY mode
            self.last_event_time_ns = current_event.t_ns
            self.update_debug_label()
    
    def update_event_count_label(self):
        """Update the event count label"""
        self.event_count_label.setText(f"Raw: {self.raw_event_count} | Accepted: {self.accepted_event_count}")
    
    def update_debug_label(self):
        """Update the debug label with current status"""
        log_file = os.path.basename(self.log_path) if self.log_path else "N/A"
        
        if self.last_event_time_ns:
            last_event_str = f"{self.last_event_time_ns/1e9:.2f}s"
        else:
            last_event_str = "N/A"
        
        debug_text = f"Mode: {self.current_mode} | Worker: {self.worker_state} | Log: {log_file} | Last Event: {last_event_str}"
        self.debug_label.setText(debug_text)
    
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
                self.time_label.setText("LIVE")
        else:
            # Show replay time in seconds
            time_s = (self.current_time_ns - self.replay_min_time) / 1e9
            total_s = (self.replay_max_time - self.replay_min_time) / 1e9
            self.time_label.setText(f"{time_s:07.3f}s / {total_s:07.3f}s")
    
    def process_new_event(self, event: ST1Event):
        """Process new event from tail worker with coalesced state"""
        # Store current event
        self.current_event = event
        self.last_event_time_ns = event.t_ns
        
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
        
        # Always process coalesced events - they already represent the final state
        # Remove debouncing for coalesced events since we're emitting one final event per read cycle
        
        if self.last_state_snapshot is None or self._state_changed(self.last_state_snapshot, new_state):
            self.last_state_snapshot = new_state
            self.accepted_event_count += 1
            self.update_event_count_label()
            self.last_update_time = time.time()
            
            # Get visual time for animation (deterministic)
            visual_time_s = self.get_visual_time_s()
            
            # Update widget state with visual time
            self.gl_widget.update_state(event, self.current_mode, visual_time_s)
            self.update_display(event, from_snapshot=False)
            
            self.update_debug_label()
            self.last_event_ignored = False
        else:
            # State didn't change
            self.last_event_ignored = True
    
    def on_activity_detected(self):
        """Handle activity detection from tail worker"""
        self.last_activity_time = time.time()
        if self.is_idle:
            self.is_idle = False
            self.idle_start_time = 0.0
            self.update_time_label()
    
    def on_worker_stopped(self):
        """Handle worker stopped signal"""
        self.worker_state = "stopped"
        self.update_debug_label()
    
    def on_idle_detected(self):
        """Handle idle detection"""
        if not self.is_idle and self.is_live_mode:
            self.is_idle = True
            self.idle_start_time = time.time()
            self.update_time_label()
            
            # Auto-switch to replay if enabled and idle
            if AUTO_SWITCH_ON_IDLE and self.is_live_mode:
                self.live_toggle.setChecked(False)
    
    def on_file_reopened(self):
        """Handle file reopening (rotation/truncation) - FIXED to match ST2"""
        if not self.log_path or not self.is_live_mode:
            return
        
        # Reload snapshot to get latest state
        latest_event, _ = self.load_live_snapshot()
        if latest_event and self.tail_worker:
            # Reseed the parser with the latest state
            self.tail_worker.reseed_parser(latest_event)
            # Update UI with the latest state
            visual_time_s = self.get_visual_time_s()
            self.gl_widget.update_state(latest_event, self.current_mode, visual_time_s)
            self.update_display(latest_event, from_snapshot=False)
            self.last_event_time_ns = latest_event.t_ns
            self.update_debug_label()
            
            print("File reopened and parser reseeded")
    
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
    
    def update_display(self, event: ST1Event, from_snapshot: bool = False):
        """Update all displays from event - THIS IS THE SINGLE SOURCE OF TRUTH"""
        # Update status indicators with pill styling
        ready_style = """
            QLabel {
                font-weight: bold;
                font-size: 11px;
                padding: 6px 12px;
                border-radius: 10px;
                background-color: #2e7d32;
                color: white;
            }
        """ if event.ready else """
            QLabel {
                font-weight: bold;
                font-size: 11px;
                padding: 6px 12px;
                border-radius: 10px;
                background-color: #3e3e42;
                color: #888888;
            }
        """
        self.ready_indicator.setStyleSheet(ready_style)
        
        busy_style = """
            QLabel {
                font-weight: bold;
                font-size: 11px;
                padding: 6px 12px;
                border-radius: 10px;
                background-color: #f57c00;
                color: white;
            }
        """ if event.busy else """
            QLabel {
                font-weight: bold;
                font-size: 11px;
                padding: 6px 12px;
                border-radius: 10px;
                background-color: #3e3e42;
                color: #888888;
            }
        """
        self.busy_indicator.setStyleSheet(busy_style)
        
        done_style = """
            QLabel {
                font-weight: bold;
                font-size: 11px;
                padding: 6px 12px;
                border-radius: 10px;
                background-color: #0288d1;
                color: white;
            }
        """ if event.done else """
            QLabel {
                font-weight: bold;
                font-size: 11px;
                padding: 6px 12px;
                border-radius: 10px;
                background-color: #3e3e42;
                color: #888888;
            }
        """
        self.done_indicator.setStyleSheet(done_style)
        
        fault_style = """
            QLabel {
                font-weight: bold;
                font-size: 11px;
                padding: 6px 12px;
                border-radius: 10px;
                background-color: #c62828;
                color: white;
            }
        """ if event.fault else """
            QLabel {
                font-weight: bold;
                font-size: 11px;
                padding: 6px 12px;
                border-radius: 10px;
                background-color: #3e3e42;
                color: #888888;
            }
        """
        self.fault_indicator.setStyleSheet(fault_style)
        
        if event.cycle_time_ms:
            self.cycle_label.setText(f"Cycle: {event.cycle_time_ms:.1f} ms")
        else:
            self.cycle_label.setText("Cycle: N/A ms")
        
        # Update total and completed
        total = event.extra.get('total', 'N/A')
        completed = event.extra.get('total_completed', 0)
        
        # Use visual time for display
        now_text = f"Visual Time: {self.gl_widget.animation_time:.1f}s"
        
        # Add inventory info
        inventory_info = f"Bin1: {self.gl_widget.inventory['bin1']} | Bin2: {self.gl_widget.inventory['bin2']} | Bin3: {self.gl_widget.inventory['bin3']}"
        
        self.total_label.setText(f"Total: {total}")
        self.completed_label.setText(f"Completed: {completed}")
        self.now_label.setText(f"{now_text}\n{inventory_info}")
        
        # Determine result
        result = "RUNNING"
        result_color = "#CCCCCC"
        
        if event.fault:
            result = "FAIL"
            result_color = "#FF4444"
        elif event.done:
            result = "PASS"
            result_color = "#44FF44"
        elif event.busy:
            result = "RUNNING"
            result_color = "#FFD700"
        
        self.result_label.setText(f"Result: {result}")
        self.result_label.setStyleSheet(f"font-family: 'Consolas', monospace; padding: 3px; color: {result_color}; font-weight: bold;")
        
        # Pass count (completed count)
        self.pass_count_label.setText(f"Pass Count: {completed}")
        
        # Update stage status - use gl_widget.stage_progress as single source
        active_index = self.gl_widget.active_stage_index
        if active_index >= 0 and active_index < 4:
            stage_name = self.gl_widget.stage_names[active_index]
            self.stage_status_label.setText(f"Active Stage: {stage_name}")
            self.stage_status_label.setStyleSheet("font-weight: bold; font-size: 12px; padding: 5px; color: #FFD700;")
            
            # Update progress bar - use gl_widget.stage_progress as single source
            progress = int(self.gl_widget.stage_progress * 100)
            self.progress_bar.setValue(progress)
        else:
            self.stage_status_label.setText(f"Active Stage: Idle")
            self.stage_status_label.setStyleSheet("font-weight: bold; font-size: 12px; padding: 5px; color: #CCCCCC;")
            self.progress_bar.setValue(0)
        
        # Update extra KPIs
        # Clear existing widgets
        for i in reversed(range(self.extra_layout.count())):
            widget = self.extra_layout.itemAt(i).widget()
            if widget:
                widget.deleteLater()
        
        # Add new KPI labels (max 8 for better visibility)
        extra_items = list(event.extra.items())[:8]
        for key, value in extra_items:
            label = QLabel(f"{key}: {value}")
            label.setStyleSheet("font-family: 'Consolas', monospace; padding: 3px; border-bottom: 1px solid #444444;")
            self.extra_layout.addWidget(label)
        
        # Hide extra group if no extra signals
        self.extra_group.setVisible(len(extra_items) > 0)
    
    def update_animation(self):
        """Update animation based on timer"""
        # Get current visual time (deterministic)
        visual_time_s = self.get_visual_time_s()
        
        # Update animation time in gl_widget
        self.gl_widget.animation_time = visual_time_s
        
        # Compute active stage using animation time
        self.gl_widget.compute_active_stage()
        active_index = self.gl_widget.active_stage_index
        
        # Update stage status and progress bar - use gl_widget.stage_progress as single source
        if active_index >= 0 and active_index < 4:
            stage_name = self.gl_widget.stage_names[active_index]
            self.stage_status_label.setText(f"Active Stage: {stage_name}")
            self.stage_status_label.setStyleSheet("font-weight: bold; font-size: 12px; padding: 5px; color: #FFD700;")
            
            # Update progress bar - use gl_widget.stage_progress as single source
            progress = int(self.gl_widget.stage_progress * 100)
            self.progress_bar.setValue(progress)
        else:
            self.stage_status_label.setText("Active Stage: Idle")
            self.stage_status_label.setStyleSheet("font-weight: bold; font-size: 12px; padding: 5px; color: #CCCCCC;")
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
        """Handle live/replay toggle - FIXED to match ST2 behavior"""
        was_live = self.is_live_mode
        self.is_live_mode = state == Qt.Checked
        
        # Only switch if mode actually changed
        if was_live != self.is_live_mode:
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
    
    def closeEvent(self, event):
        """Cleanup on close"""
        self._stop_tail_worker()
        event.accept()

# ===== MAIN APPLICATION =====
def main():
    # Set OpenGL compatibility profile with anti-aliasing
    fmt = QSurfaceFormat()
    fmt.setVersion(OPENGL_MAJOR_VERSION, OPENGL_MINOR_VERSION)
    fmt.setProfile(QSurfaceFormat.CompatibilityProfile)
    fmt.setDepthBufferSize(24)
    fmt.setSamples(8)  # 8x MSAA for better quality
    fmt.setSwapInterval(1)  # Enable vsync for smoother animation
    QSurfaceFormat.setDefaultFormat(fmt)
    
    app = QApplication(sys.argv)
    
    # Set application-wide dark palette
    app.setStyle("Fusion")
    palette = QPalette()
    palette.setColor(QPalette.Window, QColor(53, 53, 53))
    palette.setColor(QPalette.WindowText, Qt.white)
    palette.setColor(QPalette.Base, QColor(25, 25, 25))
    palette.setColor(QPalette.AlternateBase, QColor(53, 53, 53))
    palette.setColor(QPalette.ToolTipBase, Qt.white)
    palette.setColor(QPalette.ToolTipText, Qt.white)
    palette.setColor(QPalette.Text, Qt.white)
    palette.setColor(QPalette.Button, QColor(53, 53, 53))
    palette.setColor(QPalette.ButtonText, Qt.white)
    palette.setColor(QPalette.BrightText, Qt.red)
    palette.setColor(QPalette.Link, QColor(42, 130, 218))
    palette.setColor(QPalette.Highlight, QColor(42, 130, 218))
    palette.setColor(QPalette.HighlightedText, Qt.black)
    app.setPalette(palette)
    
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