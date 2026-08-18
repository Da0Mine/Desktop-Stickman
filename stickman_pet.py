#!/usr/bin/env python3
"""
桌宠火柴人 — 程序化矢量绘制的白色火柴人

操作说明：
  启动后点击屏幕选择火柴人出现位置
  ←→/AD   左右移动
  ↑/W/空格 跳跃 / 贴墙时墙跳
  ↓/S     快速下落
  双击方向键 → 该方向冲刺（冲刺中穿墙）
  ESC    退出
"""

import sys
import os
import time
import math
import json
import queue
import ctypes
import shutil
import threading
import faulthandler
import numpy as np
import mss
from PyQt5.QtWidgets import (QApplication, QWidget, QVBoxLayout, QGridLayout,
                             QLabel, QSlider, QDoubleSpinBox, QPushButton,
                             QLineEdit, QHBoxLayout, QDialog, QListWidget,
                             QInputDialog, QMessageBox, QSystemTrayIcon,
                             QMenu, QAction)
from PyQt5.QtCore import Qt, QTimer, QPointF, QRectF, QCoreApplication
from PyQt5.QtGui import QPainter, QPixmap, QColor, QFont, QTransform, QPen, QIcon

# ── 修复 Qt 平台插件路径 ──
# 某些环境下 PyQt5 无法自动定位 Qt5/plugins，需要手动设置
import PyQt5 as _pyqt5
_qt_plugin_path = os.path.join(os.path.dirname(_pyqt5.__file__), 'Qt5', 'plugins')
if os.path.isdir(_qt_plugin_path):
    QCoreApplication.addLibraryPath(_qt_plugin_path)
from pynput import keyboard as pkb
from pynput.keyboard import Key

# ═════════════════ 路径 ═════════════════
# 打包成 exe 后 __file__ 指向 PyInstaller 临时解压目录(_MEIPASS)，
# 用户数据(姿势/存档/日志)必须读写 exe 同目录，否则重启即丢失。
SCRIPT_DIR = os.path.dirname(os.path.abspath(
    sys.executable if getattr(sys, 'frozen', False) else __file__))

# 无控制台模式(stdout/stderr 为 None)下 print 会抛异常，统一重定向到日志文件
if getattr(sys, 'frozen', False):
    try:
        _log = open(os.path.join(SCRIPT_DIR, 'crash_log.txt'), 'a', encoding='utf-8')
        sys.stdout = _log
        sys.stderr = _log
    except Exception:
        pass

_fh = open(os.path.join(SCRIPT_DIR, 'crash_log.txt'), 'a', encoding='utf-8')
faulthandler.enable(file=_fh)


def _bootstrap_data_files():
    """打包版首次运行时，把内置的数据文件(用户已编辑好的动作/参数)复制到 exe 同目录。

    PyInstaller onefile 把这些文件打进 _MEIPASS 临时目录，而用户数据读写 exe 同目录。
    首次启动时若 exe 目录缺少对应文件，就从内置默认复制一份；之后用户的编辑
    都保存在 exe 同目录，重启不丢。
    """
    if not getattr(sys, 'frozen', False):
        return
    try:
        src_dir = getattr(sys, '_MEIPASS', SCRIPT_DIR)
        for name in ('poses.json', 'cfg_saved.txt',
                     'pose_profiles.json', 'cfg_profiles.json'):
            dst = os.path.join(SCRIPT_DIR, name)
            if os.path.exists(dst):
                continue
            src = os.path.join(src_dir, name)
            if os.path.exists(src):
                shutil.copy2(src, dst)
    except Exception:
        pass

try:
    ctypes.windll.shcore.SetProcessDpiAwareness(2)
except Exception:
    pass

# ── 全局低级键盘钩子（WH_KEYBOARD_LL）兜底：不依赖窗口焦点/点击即可接收按键 ──
_user32 = ctypes.windll.user32
_VK_MAP = {
    0x25: Key.left, 0x26: Key.up, 0x27: Key.right, 0x28: Key.down,
    0x20: Key.space, 0x1B: Key.esc, 0x71: Key.f2,
    0x57: Key.up, 0x41: Key.left, 0x53: Key.down, 0x44: Key.right,
}


class _KBDLL(ctypes.Structure):
    _fields_ = [("vkCode", ctypes.c_ulong), ("scanCode", ctypes.c_ulong),
                ("flags", ctypes.c_ulong), ("time", ctypes.c_ulong),
                ("dwExtraInfo", ctypes.c_ulong)]


_WinProc = ctypes.WINFUNCTYPE(ctypes.c_long, ctypes.c_int,
                              ctypes.c_ulong, ctypes.c_ulong)
_hk_cb_ref = []          # 持有回调，防止被 GC 回收
_hk_hook_ref = []        # 持有钩子句柄
_hk_win_ref = []         # 持有窗口引用


def _hk_proc(nCode, wParam, lParam):
    try:
        if nCode >= 0 and _hk_win_ref:
            if wParam in (0x0100, 0x0104):
                down = True
            elif wParam in (0x0101, 0x0105):
                down = False
            else:
                down = None
            if down is not None:
                kb = ctypes.cast(lParam, ctypes.POINTER(_KBDLL)).contents
                key = _VK_MAP.get(kb.vkCode)
                if key is not None:
                    win = _hk_win_ref[0]
                    if down:
                        win._on_key_press(key)
                    else:
                        win._on_key_release(key)
    except Exception:
        pass
    hook = _hk_hook_ref[0] if _hk_hook_ref else 0
    return _user32.CallNextHookEx(hook, nCode, wParam, lParam)


def install_global_keyhook(win):
    """安装全局键盘钩子；成功返回 True，失败返回 False（此时调用方应回退 pynput）"""
    try:
        cb = _WinProc(_hk_proc)
        _hk_cb_ref.append(cb)
        _hk_win_ref.append(win)
        hmod = _user32.GetModuleHandleW(None)
        hhook = _user32.SetWindowsHookExW(13, cb, hmod, 0)
        if not hhook:
            return False
        _hk_hook_ref.append(hhook)
        return True
    except Exception:
        return False

# ═════════════════ 路径 ═════════════════
FRAME_DIR = os.path.join(SCRIPT_DIR, 'stickman_frames')

# ═════════════════ 配置参数 ═════════════════
# ── 可实时调节的配置（控制面板可改）──
CFG = {
    'SCAN_RADIUS':      200,   # 截屏半径（旧版手感）
    'COLOR_THRESHOLD':  18,    # 颜色差异阈值（更灵敏）
    'MIN_EDGE_LENGTH':  6,     # 地面检测最小连续边缘（宽松）
    'CEIL_MIN_EDGE':    40,    # 天花板检测最小连续边缘（严格，防文字图标挡跳跃）
    'WALL_RATIO':       0.45,  # 判墙边缘总占比（宽松，先保证检测得到）
    'WALL_TOL':         5,     # 判墙容差px
    'GRAVITY':          1.6,
    'MOVE_SPEED':       5.5,
    'JUMP_FORCE':       18.0,
    'WALL_SLIDE_SPEED': 3.5,
    'DASH_SPEED':       24.0,
    'DASH_DURATION':    0.20,
    'IMG_SCALE':        0.7,
    'RUN_PACE':         90.0,  # 跑步步幅(px/循环)：越大跑步动画越慢
}

class _Cfg:
    """属性访问代理（备用）"""
    def __getattr__(self, name):
        try:
            return CFG[name]
        except KeyError:
            raise AttributeError(name)

CFG_A = _Cfg()


def _load_saved_cfg():
    """启动时读取面板保存过的参数（cfg_saved.txt），格式: KEY = value"""
    p = os.path.join(SCRIPT_DIR, 'cfg_saved.txt')
    if not os.path.exists(p):
        return
    try:
        import io
        for line in io.open(p, encoding='utf-8'):
            line = line.strip()
            if not line or line.startswith('#') or '=' not in line:
                continue
            k, v = [x.strip() for x in line.split('=', 1)]
            if k in CFG:
                try:
                    CFG[k] = float(v)
                except ValueError:
                    pass
    except Exception:
        pass


def load_poses_json():
    """读取姿势编辑器保存的 poses.json；不存在或解析失败返回 None（回退程序化姿势）"""
    path = os.path.join(SCRIPT_DIR, 'poses.json')
    if not os.path.exists(path):
        return None
    try:
        import io
        with io.open(path, encoding='utf-8') as f:
            data = json.load(f)
        return data if isinstance(data, dict) else None
    except Exception:
        return None


FPS = 60
FRAME_MS = int(1000 / FPS)

# 兼容旧代码的常量名（碰撞框尺寸一般不需实时改）
STICKMAN_W = 20
STICKMAN_H = 90
STICKMAN_FOOT_SINK = 6   # 贴图相对碰撞箱下沉(px)：并集包围盒底部比多数帧脚底更低，补偿浮空感
STICKMAN_HITBOX_RIGHT_SHRINK = 3  # 右边界内缩(px)：火柴人右侧是背侧空隙，缩小减少右向误撞
DOUBLE_TAP_WINDOW = 0.25   # 双击判定窗口（秒）
DASH_COOLDOWN = 0.30        # 冲刺冷却（秒）
WALL_JUMP_H = 16.0          # 贴墙跳垂直力度
WALL_JUMP_VX = 8.0          # 贴墙跳水平蹬离速度


# ═════════════════ 帧加载 ═════════════════
def load_frames(prefix, count, skip_4=True):
    """加载指定前缀的帧序列，返回 QPixmap 列表"""
    frames = []
    for i in range(count):
        if skip_4 and i == 4:
            continue
        for ext in ['.PNG', '.png']:
            name = f"{prefix}_{i:02d}{ext}"
            path = os.path.join(FRAME_DIR, name)
            if os.path.exists(path):
                pix = QPixmap(path)
                if not pix.isNull():
                    frames.append(pix)
                break
    return frames


def load_single(name):
    """加载单张图片"""
    for ext in ['.PNG', '.png']:
        path = os.path.join(FRAME_DIR, name + ext)
        if os.path.exists(path):
            pix = QPixmap(path)
            if not pix.isNull():
                return pix
    return None


def compute_sprite_bbox(frame_lists):
    """扫描所有帧的非透明像素，返回归一化包围盒 (u0, v0, u1, v1)
    碰撞箱将严格按精灵图实际轮廓生成：火柴人身体能穿过的地方就能过"""
    u0, v0, u1, v1 = 1.0, 1.0, 0.0, 0.0
    try:
        from PyQt5.QtGui import QImage
        for frames in frame_lists:
            for pix in frames:
                img = pix.toImage().convertToFormat(QImage.Format_RGBA8888)
                w, h = img.width(), img.height()
                if w == 0 or h == 0:
                    continue
                try:
                    buf = img.constBits().asarray(img.sizeInBytes())
                except AttributeError:
                    buf = img.constBits().asarray(img.byteCount())
                arr = np.frombuffer(buf, dtype=np.uint8).reshape(h, img.bytesPerLine())[:, :w * 4].reshape(h, w, 4)
                alpha = arr[:, :, 3] > 25
                if not alpha.any():
                    continue
                rows = np.where(alpha.any(axis=1))[0]
                cols = np.where(alpha.any(axis=0))[0]
                u0 = min(u0, cols[0] / w)
                u1 = max(u1, (cols[-1] + 1) / w)
                v0 = min(v0, rows[0] / h)
                v1 = max(v1, (rows[-1] + 1) / h)
    except Exception:
        pass
    if u1 <= u0 or v1 <= v0:
        return (0.25, 0.05, 0.75, 1.0)  # 兜底值
    return (u0, v0, u1, v1)


# ═════════════════ 工具函数 ═════════════════
def longest_true_run(arr_1d):
    if len(arr_1d) == 0:
        return 0
    padded = np.concatenate([[False], arr_1d, [False]]).astype(np.int8)
    diff = np.diff(padded)
    starts = np.where(diff == 1)[0]
    ends = np.where(diff == -1)[0]
    if len(starts) == 0:
        return 0
    return int(np.max(ends - starts))


# ═════════════════ 屏幕分析器 ═════════════════
class ScreenAnalyzer:
    def __init__(self):
        self.sct = mss.MSS()
        self.dy_bin = None
        self.dx_bin = None
        self.left = 0
        self.top = 0
        self.w = 0
        self.h = 0

    def analyze(self, cx, cy):
        try:
            r = int(round(CFG['SCAN_RADIUS']))
            mon = self.sct.monitors[0]
            left   = max(0, int(cx - r))
            top    = max(0, int(cy - r))
            right  = min(mon['width'],  int(cx + r))
            bottom = min(mon['height'], int(cy + r))
            w = right - left
            h = bottom - top
            if w < 20 or h < 20:
                return
            region = {'left': left, 'top': top, 'width': w, 'height': h}
            shot = self.sct.grab(region)
            img = np.array(shot)[:, :, :3].astype(np.float32)
            gray = img[:, :, 0] * 0.114 + img[:, :, 1] * 0.587 + img[:, :, 2] * 0.299
            if gray.shape[0] < 2 or gray.shape[1] < 2:
                return
            dy = np.abs(np.diff(gray, axis=0))
            dx = np.abs(np.diff(gray, axis=1))
            self.dy_bin = dy > CFG['COLOR_THRESHOLD']
            self.dx_bin = dx > CFG['COLOR_THRESHOLD']
            self.left = left
            self.top = top
            self.w = w
            self.h = h
        except Exception:
            pass

    def check_h(self, abs_y, abs_x1, abs_x2, tol=None):
        tol = int(round(CFG['WALL_TOL'])) + 1
        if self.dy_bin is None:
            return 0
        best = 0
        for t in range(-tol, tol + 1):
            ry = int(abs_y + t - self.top)
            rx1 = max(0, int(abs_x1 - self.left))
            rx2 = min(self.dy_bin.shape[1], int(abs_x2 - self.left))
            if 0 <= ry < self.dy_bin.shape[0] and rx1 < rx2:
                run = longest_true_run(self.dy_bin[ry, rx1:rx2])
                best = max(best, run)
        return best

    def check_v(self, abs_x, abs_y1, abs_y2, tol=None):
        tol = int(round(CFG['WALL_TOL'])) + 1
        if self.dx_bin is None:
            return 0
        best = 0
        for t in range(-tol, tol + 1):
            rx = int(abs_x + t - self.left)
            ry1 = max(0, int(abs_y1 - self.top))
            ry2 = min(self.dx_bin.shape[0], int(abs_y2 - self.top))
            if 0 <= rx < self.dx_bin.shape[1] and ry1 < ry2:
                col = self.dx_bin[ry1:ry2, rx]
                run = longest_true_run(col)
                best = max(best, run)
        return best

    def is_wall(self, abs_x, abs_y1, abs_y2, tol=None, ratio=None):
        tol = int(round(CFG['WALL_TOL']))
        if ratio is None: ratio = CFG['WALL_RATIO']
        """严格确定是否为墙：±tol范围内各列边缘像素总占比≥ratio"""
        if self.dx_bin is None:
            return False
        best_ratio = 0.0
        for t in range(-tol, tol + 1):
            rx = int(abs_x + t - self.left)
            ry1 = max(0, int(abs_y1 - self.top))
            ry2 = min(self.dx_bin.shape[0], int(abs_y2 - self.top))
            if 0 <= rx < self.dx_bin.shape[1] and ry1 < ry2:
                col = self.dx_bin[ry1:ry2, rx]
                r = float(np.sum(col)) / max(len(col), 1)
                best_ratio = max(best_ratio, r)
        return best_ratio >= ratio


# ═════════════════ 火柴人 ═════════════════
class Stickman:
    IDLE, RUN, JUMP, WALL, DASH, CROUCH = range(6)

    def __init__(self, x, y):
        self.x = x
        self.y = y
        self.vx = 0.0
        self.vy = 0.0
        self.on_ground = False
        self.on_wall = 0
        self.last_grounded = 0.0  # 最后一次着地时刻（土狼时间用）
        self.dashing = False
        self.dash_dir = (0, 0)
        self.dash_timer = 0.0
        self.dash_cd = 0.0
        self.facing = -1   # 默认面向左
        self.anim_t = 0.0
        self.anim_phase = 0.0   # 奔跑/冲刺相位（按实际位移推进，保证动作平滑不卡顿）
        self.crouching = False  # 下蹲（按住↓且着地时进入下蹲姿态）
        self.trail = []
        self.wall_hold = 0    # 连续被墙挡住的帧数（贴墙去抖）
        self.wall_side = 0    # 去抖期间的挡墙方向
        self.wall_is_edge = False  # 贴墙来源是否为屏幕边缘（边缘无真墙，绘制不做向墙偏移）
        self._jump_pending = False # 延迟跳跃标志：由键盘事件设置，update 中实际执行
        self._jump_saved_wall = 0  # try_jump 时保存的墙方向，延迟跳跃不再依赖 on_wall 存活

    @property
    def state(self):
        if self.dashing:
            return self.DASH
        if self.on_ground and self.crouching:
            return self.CROUCH
        if self.on_wall != 0:
            return self.WALL
        if not self.on_ground:
            return self.JUMP
        if abs(self.vx) > 0.8:
            return self.RUN
        return self.IDLE

    def try_jump(self):
        import time as _t
        # 土狼时间：离地0.18秒内仍可正常起跳
        if self.on_ground or (_t.time() - self.last_grounded) < 0.18:
            self.vy = -CFG['JUMP_FORCE']
            self.on_ground = False
            self.last_grounded = 0.0
        elif self.on_wall != 0:
            # 贴墙跳延迟到 update() 中处理，此时 keys 已完整包含该帧所有按键状态
            self._jump_pending = True
            self._jump_saved_wall = self.on_wall  # 立即保存墙方向，防止延迟期间 on_wall 被清零

    def start_dash(self, dx, dy):
        if self.dash_cd > 0 or self.dashing:
            return
        self.dashing = True
        self.dash_dir = (dx, dy)
        self.dash_timer = CFG['DASH_DURATION']
        self.dash_cd = CFG['DASH_DURATION'] + DASH_COOLDOWN
        self.trail.clear()

    def update(self, analyzer, keys, dt, screen_w, screen_h):
        self.anim_t += dt
        if self.dash_cd > 0:
            self.dash_cd -= dt

        if self.dashing:
            self._update_dash(dt, screen_w, screen_h, keys, analyzer)
            return

        # ── 延迟贴墙跳跃处理（保证此时 keys 已完整包含该帧所有按键）──
        # 不依赖 on_wall 存活，因为在某些边缘情况下 on_wall 可能在 try_jump 和 update 之间被清零
        jump_processed = False
        if self._jump_pending:
            self._jump_pending = False
            saved_wall = self._jump_saved_wall
            self._jump_saved_wall = 0
            self.on_wall = 0
            self.wall_is_edge = False
            jump_processed = True

            left_pressed  = Key.left  in keys
            right_pressed = Key.right in keys
            if saved_wall == 0:
                # 没有保存到墙方向（理论上不应发生），仍给一个向前的冲量
                up_pressed = Key.up in keys
                if up_pressed:
                    self.vy = -CFG['JUMP_FORCE']
                if right_pressed:
                    self.vx = CFG['MOVE_SPEED']
                    self.facing = 1
                elif left_pressed:
                    self.vx = -CFG['MOVE_SPEED']
                    self.facing = -1
            else:
                away = (saved_wall == -1 and right_pressed) or (saved_wall == 1 and left_pressed)
                if away:
                    self.vy = -CFG['JUMP_FORCE']
                    self.vx = (1 if right_pressed else -1) * CFG['MOVE_SPEED']
                    self.facing = 1 if right_pressed else -1
                    # 离墙跳：推开足够距离确保下一帧不被屏幕边缘检测重新吸附
                    self.x += (1 if right_pressed else -1) * (STICKMAN_W * 1.5)
                else:
                    self.vy = -WALL_JUMP_H
                    self.vx = -saved_wall * WALL_JUMP_VX
                    self.facing = -1 if saved_wall == 1 else 1
                    # 墙跳也推开一些，防止边缘反复吸附
                    self.x += -saved_wall * (STICKMAN_W * 1.0)

        left  = Key.left  in keys
        right = Key.right in keys
        down  = Key.down  in keys

        target_vx = 0.0
        # 蹲下时禁止左右移动（下蹲姿态锁定在当前位置）
        if not (down and self.on_ground):
            if left and not right:
                target_vx = -CFG['MOVE_SPEED']
                self.facing = -1
            elif right and not left:
                target_vx = CFG['MOVE_SPEED']
                self.facing = 1
            elif left and right:
                target_vx = self.facing * CFG['MOVE_SPEED']
        # 屏幕边缘：朝边缘外的移动被边界挡住（消除贴墙时每帧被拉回的位置抖动）
        hw_edge = STICKMAN_W / 2
        if self.x <= hw_edge and target_vx < 0:
            target_vx = 0
        if self.x >= screen_w - hw_edge + STICKMAN_HITBOX_RIGHT_SHRINK and target_vx > 0:
            target_vx = 0
        # 非贴墙跳帧才用 target_vx 覆盖 vx，保留贴墙跳时设定的斜抛速度
        # （贴墙跳已经正确设置了 vx/vy，若再被 target_vx 覆盖会丢失斜抛分量）
        if not jump_processed:
            self.vx = target_vx

        self.vy += CFG['GRAVITY']
        if self.vy > 25:
            self.vy = 25
        if down and not self.on_ground:
            self.vy += 2.5  # 按住下方向键快速下落

        # 下蹲：仅当着地且按住↓时进入下蹲姿态（不改变任何物理/速度参数）
        self.crouching = bool(down and self.on_ground)

        # 奔跑相位按实际位移推进；步幅 RUN_PACE(px/循环) 越大动画越慢（可在调参面板实时改）
        if abs(self.vx) > 0.5:
            pace = max(10.0, CFG['RUN_PACE'])
            self.anim_phase = (self.anim_phase + abs(self.vx) * (dt * 60) / pace) % 1.0

        # 贴墙时自动下滑（无需长按方向键），_move_and_collide 每帧重算 on_wall，离开墙后自动清除
        if self.on_wall != 0 and not self.on_ground and self.vy > CFG['WALL_SLIDE_SPEED']:
            self.vy = CFG['WALL_SLIDE_SPEED']

        self._move_and_collide(analyzer, keys)

        hw = STICKMAN_W / 2
        hh = STICKMAN_H / 2
        # 屏幕左右边缘直接作为墙：空中碰到边缘即贴墙吸附，无需按方向键
        if self.x <= hw:
            self.x = hw
            self.vx = max(0, self.vx)
            if not self.on_ground:
                self.on_wall = -1  # 屏幕左边缘即左墙
                self.wall_is_edge = True
        if self.x >= screen_w - hw + STICKMAN_HITBOX_RIGHT_SHRINK:
            self.x = screen_w - hw + STICKMAN_HITBOX_RIGHT_SHRINK
            self.vx = min(0, self.vx)
            if not self.on_ground:
                self.on_wall = 1   # 屏幕右边缘即右墙
                self.wall_is_edge = True
        if self.y > screen_h - hh:
            self.y = screen_h - hh
            self.vy = 0
            self.on_ground = True
            self.last_grounded = time.time()
        if self.y < hh:
            self.y = hh
            self.vy = max(0, self.vy)

    def _update_dash(self, dt, screen_w, screen_h, keys, analyzer):
        self.dash_timer -= dt
        self.trail.append((self.x, self.y))
        if len(self.trail) > 8:
            self.trail.pop(0)

        hw = STICKMAN_W / 2
        hh = STICKMAN_H / 2
        if self.dash_timer <= 0:
            self.dashing = False
            self.vx = self.dash_dir[0] * CFG['MOVE_SPEED'] * 0.5
            self.vy = self.dash_dir[1] * 2.0
            self.trail.clear()
            return
        # 冲刺方向无视障碍
        self.x += self.dash_dir[0] * CFG['DASH_SPEED']
        self.y += self.dash_dir[1] * CFG['DASH_SPEED']
        # 上下冲刺时允许左右方向键横移调整
        # 横移方向没有冲刺，不能穿墙：撞到墙就停下
        if self.dash_dir[1] != 0:
            body_top    = self.y - hh + 8
            body_bottom = self.y + hh - 8
            left  = Key.left  in keys and Key.right not in keys
            right = Key.right in keys and Key.left not in keys
            if left:
                self.facing = -1
                if not analyzer.is_wall(self.x - CFG['MOVE_SPEED'] - hw, body_top, body_bottom):
                    self.x -= CFG['MOVE_SPEED']
            elif right:
                self.facing = 1
                if not analyzer.is_wall(self.x + CFG['MOVE_SPEED'] + hw - STICKMAN_HITBOX_RIGHT_SHRINK, body_top, body_bottom):
                    self.x += CFG['MOVE_SPEED']
        self.x = max(hw, min(screen_w - hw + STICKMAN_HITBOX_RIGHT_SHRINK, self.x))
        self.y = max(hh, min(screen_h - hh, self.y))

    def _move_and_collide(self, analyzer, keys):
        hw = STICKMAN_W / 2
        hh = STICKMAN_H / 2

        prev_wall = self.on_wall  # 上帧贴墙方向（用于贴墙保持）
        self.on_wall = 0
        blocked = 0  # 本帧水平移动被墙挡住的方向
        steps_x = max(1, int(abs(self.vx)))
        dx_step = self.vx / steps_x
        for _ in range(steps_x):
            new_x = self.x + dx_step
            # 水平碰撞：用几乎整个身体高度检测
            body_top    = self.y - hh + 8
            body_bottom = self.y + hh - 8

            # 地面行走用严格墙判定：屏幕上大量普通明暗边界（壁纸图案、窗口边、
            # 图标列），甚至火柴人自身被截屏截入的手臂线条，在宽松阈值下都会被
            # 误判成"隐形墙"，表现为按住方向键火柴人一动不动（只有无视障碍的
            # 冲刺能穿过）。真墙边缘连续贯穿几乎整个身体高度(占比>0.85)，杂边
            # 和自身散碎线条达不到。空中保持原阈值，不影响贴墙吸附灵敏度。
            wall_ratio = max(float(CFG['WALL_RATIO']), 0.85) if self.on_ground \
                else CFG['WALL_RATIO']
            if self.vx > 0.5:
                if analyzer.is_wall(new_x + hw - STICKMAN_HITBOX_RIGHT_SHRINK,
                                    body_top, body_bottom, ratio=wall_ratio):
                    self.vx = 0
                    blocked = 1
                    break
            elif self.vx < -0.5:
                if analyzer.is_wall(new_x - hw,
                                    body_top, body_bottom, ratio=wall_ratio):
                    self.vx = 0
                    blocked = -1
                    break
            self.x = new_x

        self.on_ground = False
        steps_y = max(1, int(abs(self.vy)))
        dy_step = self.vy / steps_y
        for _ in range(steps_y):
            new_y = self.y + dy_step

            if self.vy > 0.5:
                run = analyzer.check_h(new_y + hh, self.x - hw + 3, self.x + hw - 3)
                if run >= int(round(CFG['MIN_EDGE_LENGTH'])):
                    self.vy = 0
                    self.on_ground = True
                    self.last_grounded = time.time()
                    break
            elif self.vy < -0.5:
                run = analyzer.check_h(new_y - hh, self.x - hw + 3, self.x + hw - 3)
                if run >= int(round(CFG['CEIL_MIN_EDGE'])):
                    self.vy = 0
                    break
            self.y = new_y

        # 贴墙判定：空中且连续多帧被同一方向的墙挡住 → 贴墙
        # 连续帧去抖：跳跃途中背景误判出的"隐形墙"只会挡1~2帧，会被过滤；
        # 真墙会持续挡住，约50ms后进入贴墙（无感知延迟）
        if blocked != 0:
            if self.wall_side == blocked:
                self.wall_hold += 1
            else:
                self.wall_side = blocked
                self.wall_hold = 1
        else:
            self.wall_side = 0
            self.wall_hold = 0
        if not self.on_ground and self.wall_hold >= 3:
            # 脚下墙必须继续延伸才贴墙，避免按方向键滑到墙底后虚空攀附
            below_top    = self.y + hh + 2
            below_bottom = self.y + hh + 8
            if self.wall_side == -1:
                wsx = self.x - hw - 2
            else:
                wsx = self.x + hw - STICKMAN_HITBOX_RIGHT_SHRINK + 2
            if analyzer.check_v(wsx, below_top, below_bottom) >= 5:
                self.on_wall = self.wall_side

        # 贴墙保持：松开方向键后 vx=0 → blocked=0 → wall_hold 清空 → on_wall 丢失。
        # 仅当上帧已贴墙时才保持；采样点取碰撞箱外侧2px（精灵轮廓之外，避免把
        # 火柴人自身轮廓误判为墙）。脚下延伸检测用 check_v（连续长度）而非 is_wall
        # （占比），避免墙底在范围内占比稀释导致误判"墙还在"。
        if self.on_wall == 0 and prev_wall != 0 and not self.on_ground:
            body_top    = self.y - hh + 8
            body_bottom = self.y + hh - 8
            below_top   = self.y + hh + 2    # 脚底下方2px
            below_bottom = self.y + hh + 8   # 脚底下方8px（6px范围）
            if prev_wall == -1:
                sx = self.x - hw - 2
                if analyzer.is_wall(sx, body_top, body_bottom) and \
                   analyzer.check_v(sx, below_top, below_bottom) >= 5:
                    self.on_wall = -1
            elif prev_wall == 1:
                sx = self.x + hw - STICKMAN_HITBOX_RIGHT_SHRINK + 2
                if analyzer.is_wall(sx, body_top, body_bottom) and \
                   analyzer.check_v(sx, below_top, below_bottom) >= 5:
                    self.on_wall = 1


# ═════════════════ 主窗口 ═════════════════
class StickmanWindow(QWidget):

    def __init__(self):
        super().__init__()
        self.setWindowFlags(
            Qt.FramelessWindowHint |
            Qt.WindowStaysOnTopHint |
            Qt.Tool
        )
        self.setAttribute(Qt.WA_TranslucentBackground)

        screen = QApplication.primaryScreen()
        sg = screen.geometry()
        ratio = screen.devicePixelRatio()
        self.screen_w = int(sg.width() * ratio)
        self.screen_h = int(sg.height() * ratio)
        self.ratio = ratio
        self.setGeometry(sg)

        # 启动时应用已保存的用户配置存档（若有；无则用内置默认）
        _p = load_cfg_profiles()
        if _p['active'] in _p['profiles']:
            apply_cfg_profile(_p['profiles'][_p['active']])

        # ── 火柴人外观改用程序化矢量绘制（白色火柴人，不再使用帧图片）──
        # 逻辑尺寸仍随 IMG_SCALE 实时可调（调参面板）
        self.img_size = int(128 * CFG['IMG_SCALE'])

        # 固定精灵包围盒（程序化绘制的白色火柴人占满该区域）→ 据此生成碰撞箱，随 IMG_SCALE 缩放
        self.sprite_bbox = (0.25, 0.03, 0.75, 1.0)
        self._apply_hitbox()
        print(f"白色火柴人尺寸: 逻辑={self.img_size}px → 碰撞箱 "
              f"{STICKMAN_W}x{STICKMAN_H}px")

        # 启动即自动在屏幕中间召唤
        self.phase = 'game'
        self.stickman = Stickman(self.screen_w // 2, self.screen_h // 2)
        self.analyzer = ScreenAnalyzer()

        # 读取姿势编辑器保存的姿势（无则回退程序化绘制）
        self.poses = load_poses_json()

        # 若存在被选中的动作存档，则覆盖当前动作（默认 = 使用 poses.json）
        _pp = load_pose_profiles()
        if _pp['active'] in _pp['profiles']:
            self.poses = dict(_pp['profiles'][_pp['active']])

        self.keys = set()
        self.key_events = queue.Queue()
        self.last_key_time = {}

        # 键盘输入：优先用全局低级钩子（不依赖窗口焦点，最可靠）；
        # 仅当钩子安装失败时才回退到 pynput。两者绝不同时启用，否则
        # 同一物理按键会被双源各投一次 press/release，在自动连发和漏
        # release 情况下产生竞态，表现为"按右键无反应"。
        self.listener = None
        if not install_global_keyhook(self):
            self.listener = pkb.Listener(
                on_press=self._on_key_press,
                on_release=self._on_key_release
            )
            self.listener.start()

        # 免点击：鼠标事件直接穿透到桌面，无需点击窗口；同时把键盘焦点给本窗口
        self.setFocusPolicy(Qt.StrongFocus)
        self.setAttribute(Qt.WA_TransparentForMouseEvents, True)
        self.activateWindow()
        self.setFocus(Qt.OtherFocusReason)

        self.last_time = time.time()
        self.timer = QTimer(self)
        self.timer.timeout.connect(self._tick)
        self.timer.start(FRAME_MS)

        # 启动时不自动弹出设置面板，改为系统托盘图标（点击显示/隐藏）
        self.panel = CfgPanel(self)
        self._setup_tray()

    def _apply_hitbox(self):
        """按精灵轮廓 + 当前缩放，更新全局碰撞箱尺寸（物理像素）"""
        global STICKMAN_W, STICKMAN_H
        u0, v0, u1, v1 = self.sprite_bbox
        phys = self.img_size * self.ratio
        STICKMAN_W = max(4, int(round((u1 - u0) * phys * 0.5)))  # 左右宽度缩一半，手感更轻量
        STICKMAN_H = max(8, int(round((v1 - v0) * phys)))

    # ── 系统托盘 ──
    def _setup_tray(self):
        """右下角托盘图标：左键单击开关设置面板，右键菜单可打开设置/退出"""
        self.tray = QSystemTrayIcon(self)
        self.tray.setIcon(self._make_tray_icon())
        self.tray.setToolTip('火柴人桌宠')
        menu = QMenu()
        act_show = QAction('打开设置面板', menu)
        act_show.triggered.connect(self.toggle_panel)
        act_quit = QAction('退出', menu)
        act_quit.triggered.connect(self.close)
        menu.addAction(act_show)
        menu.addSeparator()
        menu.addAction(act_quit)
        self.tray.setContextMenu(menu)
        self.tray.activated.connect(self._on_tray_activated)
        self.tray.show()

    def _on_tray_activated(self, reason):
        if reason == QSystemTrayIcon.Trigger:   # 左键单击
            self.toggle_panel()

    def _make_tray_icon(self):
        """程序化绘制一个深色圆底 + 白色火柴人的托盘图标"""
        pm = QPixmap(64, 64)
        pm.fill(Qt.transparent)
        p = QPainter(pm)
        p.setRenderHint(QPainter.Antialiasing)
        # 深色圆底
        p.setBrush(QColor(40, 45, 60, 235))
        p.setPen(Qt.NoPen)
        p.drawEllipse(3, 3, 58, 58)
        # 白色火柴人
        pen = QPen(QColor(255, 255, 255))
        pen.setWidthF(5)
        pen.setCapStyle(Qt.RoundCap)
        pen.setJoinStyle(Qt.RoundJoin)
        p.setPen(pen)
        p.setBrush(QColor(255, 255, 255))
        p.drawEllipse(QPointF(32, 15), 7, 7)          # 头
        p.drawLine(QPointF(32, 25), QPointF(32, 46))  # 躯干
        p.drawLine(QPointF(32, 32), QPointF(18, 24))  # 左臂
        p.drawLine(QPointF(32, 32), QPointF(46, 24))  # 右臂
        p.drawLine(QPointF(32, 46), QPointF(22, 60))  # 左腿
        p.drawLine(QPointF(32, 46), QPointF(42, 60))  # 右腿
        p.end()
        return QIcon(pm)

    def mousePressEvent(self, ev):
        if self.phase == 'select':
            from PyQt5.QtGui import QCursor
            gp = QCursor.pos()  # 逻辑全局坐标
            x = int(gp.x() * self.ratio)
            y = int(gp.y() * self.ratio)
            self.stickman = Stickman(x, y)
            self.phase = 'game'
            self.setAttribute(Qt.WA_TransparentForMouseEvents, True)
            self.update()

    def paintEvent(self, ev):
        p = QPainter(self)
        p.setRenderHint(QPainter.Antialiasing)
        p.setRenderHint(QPainter.SmoothPixmapTransform)

        if self.phase == 'select':
            self._draw_select(p)
        elif self.phase == 'game' and self.stickman:
            self._draw_game(p)

    def _draw_select(self, p):
        w = self.width()
        h = self.height()
        p.fillRect(0, 0, w, h, QColor(0, 0, 0, 90))
        p.setPen(QColor(255, 255, 255, 230))
        p.setFont(QFont("Microsoft YaHei", 26, QFont.Bold))
        p.drawText(
            QRectF(0, h * 0.35, w, h * 0.15),
            Qt.AlignCenter,
            "点击屏幕选择火柴人出现位置"
        )
        p.setFont(QFont("Microsoft YaHei", 16))
        p.setPen(QColor(200, 220, 255, 180))
        p.drawText(
            QRectF(0, h * 0.52, w, h * 0.1),
            Qt.AlignCenter,
            "←→/AD 移动  ↑/W/空格 跳跃  双击方向键 冲刺(穿墙)  ESC 退出"
        )

    def _draw_game(self, p):
        s = self.stickman
        cx = s.x / self.ratio
        cy = s.y / self.ratio

        # 冲刺残影
        if s.dashing and s.trail:
            for i, (tx, ty) in enumerate(s.trail):
                alpha = int(80 * (i + 1) / max(len(s.trail), 1))
                self._draw_frame(p, tx / self.ratio, ty / self.ratio,
                                 s.state, s.facing, s.anim_t, alpha, s.dash_dir, s.on_wall)

        # 火柴人本体
        self._draw_frame(p, cx, cy, s.state, s.facing, s.anim_t, 255, s.dash_dir, s.on_wall)

    def _draw_frame(self, p, cx, cy, state, facing, anim_t, alpha, dash_dir, on_wall):
        """程序化矢量绘制白色火柴人

        局部坐标：正 x=朝向方向，负 y=向上；原点在脚底（碰撞箱底部）。
        白色圆头线条两遍渲染（深色轮廓 + 白色填充），保证浅色背景可见。

        若姿势编辑器生成了 poses.json，跑步/贴墙/下蹲/跳跃会优先使用其中姿势，其余回退程序化绘制。
        """
        # ── 姿势编辑器保存的姿势优先（跑步 / 贴墙 / 下蹲 / 跳跃）──
        poses = getattr(self, 'poses', None)
        if poses:
            if state == Stickman.RUN and poses.get('run_frames'):
                self._draw_saved_run(p, cx, cy, facing, alpha)
            elif state == Stickman.WALL and poses.get('wall'):
                self._draw_saved_wall(p, cx, cy, on_wall, alpha)
            elif state == Stickman.CROUCH and poses.get('crouch'):
                self._render_pose(p, cx, cy, poses['crouch'], fl=facing, alpha=alpha)
            elif state == Stickman.JUMP and poses.get('jump'):
                self._render_pose(p, cx, cy, poses['jump'], fl=facing, alpha=alpha)
            elif state == Stickman.IDLE and poses.get('idle'):
                self._draw_saved_idle(p, cx, cy, facing, alpha)
            elif state == Stickman.DASH and (poses.get('dash_r') or
                                             poses.get('dash_up') or
                                             poses.get('dash_down')):
                self._draw_saved_dash(p, cx, cy, facing, alpha)
            else:
                self._draw_procedural(p, cx, cy, state, facing, alpha, dash_dir)
        else:
            self._draw_procedural(p, cx, cy, state, facing, alpha, dash_dir)

        # ── 冲刺特效（配音冲刺用）──
        if state == Stickman.DASH:
            for i in range(3):
                offset = (i + 1) * 8
                line_alpha = int(180 * (1 - (i + 1) / 4))
                p.setPen(QColor(255, 200, 50, line_alpha))
                dx_dir = -dash_dir[0] if dash_dir[0] else -facing
                dy_dir = -dash_dir[1] if dash_dir[1] else 0
                p.drawLine(
                    QPointF(cx + dx_dir * offset, cy + dy_dir * offset - 4),
                    QPointF(cx + dx_dir * offset, cy + dy_dir * offset + 4)
                )

    def _draw_saved_run(self, p, cx, cy, facing, alpha):
        """用姿势编辑器保存的跑步帧绘制（phase 0..1 映射到完整循环）"""
        frames = self.poses['run_frames']
        n = max(1, len(frames))
        s = getattr(self, 'stickman', None)
        ph = s.anim_phase if s else 0.0
        idx = min(n - 1, int(ph * n) % n)
        self._render_pose(p, cx, cy, frames[idx], fl=facing, alpha=alpha)

    def _draw_saved_wall(self, p, cx, cy, on_wall, alpha):
        """用姿势编辑器保存的贴墙姿势绘制；按左右墙选择朝向"""
        pose = self.poses.get('wall')
        if not pose:
            return
        # 编辑器里摆的是「右墙」姿势（伸手/蹬脚朝 +x）。
        # 右墙(on_wall=1)→不镜像；左墙(on_wall=-1)→镜像到 -x。
        fl = on_wall if on_wall != 0 else 1
        self._render_pose(p, cx, cy, pose, fl=fl, alpha=alpha)

    def _draw_saved_idle(self, p, cx, cy, facing, alpha):
        """用姿势编辑器保存的静止姿势绘制，并叠加轻微呼吸起伏使其不生硬"""
        pose = self.poses.get('idle')
        if not pose:
            return
        s = getattr(self, 'stickman', None)
        t = s.anim_t if s else 0.0
        b = math.sin(t * 2.2) * 0.012          # 呼吸：头与肩轻微上下
        p2 = dict(pose)
        p2['head'] = (p2['head'][0], p2['head'][1] + b * 0.5)
        p2['shoulder'] = (p2['shoulder'][0], p2['shoulder'][1] + b)
        self._render_pose(p, cx, cy, p2, fl=facing, alpha=alpha)

    @staticmethod
    def _mirror_joints(pose):
        """沿垂直轴镜像姿势（右冲刺 → 左冲刺）"""
        if not pose:
            return None
        return {k: (-x, y) for k, (x, y) in pose.items()}

    def _draw_saved_dash(self, p, cx, cy, facing, alpha):
        """按冲刺方向选择姿势：右=用户直摆，左=镜像右，上/下=对应姿势并随朝向翻转"""
        poses = self.poses
        s = getattr(self, 'stickman', None)
        dx, dy = (s.dash_dir if s else (0, 0))
        pose = None
        fl = 1
        if dx > 0:
            pose, fl = poses.get('dash_r'), 1
        elif dx < 0:
            pose, fl = self._mirror_joints(poses.get('dash_r')), 1
        elif dy < 0:
            pose, fl = poses.get('dash_up'), facing
        else:
            pose, fl = poses.get('dash_down'), facing
        if pose is not None:
            self._render_pose(p, cx, cy, pose, fl=fl, alpha=alpha)
        else:
            self._draw_procedural(p, cx, cy, Stickman.DASH, facing, alpha, (dx, dy))

    def _render_pose(self, p, cx, cy, pose, fl, alpha):
        """按归一化姿势(身高比例)绘制白色火柴人；fl 为水平朝向(+1/-1)"""
        hh = STICKMAN_H / 2 / self.ratio
        foot_y = cy + hh + STICKMAN_FOOT_SINK / self.ratio   # 脚底
        H = STICKMAN_H / self.ratio
        lw = max(2.0, H * 0.055)
        head_r = H * 0.11

        def pt(fx, fy):
            return QPointF(cx + fl * fx * H, foot_y + fy * H)

        head = pt(*pose['head'])
        shoulder = pt(*pose['shoulder'])
        hip = pt(*pose['hip'])
        strokes = [
            [hip, pt(*pose['knee_b']), pt(*pose['foot_b'])],
            [shoulder, pt(*pose['elbow_b']), pt(*pose['hand_b'])],
            [shoulder, hip],
            [hip, pt(*pose['knee_f']), pt(*pose['foot_f'])],
            [shoulder, pt(*pose['elbow_f']), pt(*pose['hand_f'])],
        ]

        def paint_stroke(cr, cg, cb, a, w):
            pen2 = QPen(QColor(cr, cg, cb, a))
            pen2.setWidthF(w)
            pen2.setCapStyle(Qt.RoundCap)
            pen2.setJoinStyle(Qt.RoundJoin)
            p.setPen(pen2)
            for seg in strokes:
                for i in range(len(seg) - 1):
                    p.drawLine(seg[i], seg[i + 1])

        def paint_head(cr, cg, cb, a, r):
            p.setBrush(QColor(cr, cg, cb, a))
            p.setPen(Qt.NoPen)
            p.drawEllipse(head, r, r)

        p.save()
        if alpha < 255:
            p.setOpacity(alpha / 255.0)
        paint_stroke(20, 20, 30, 70, lw + 4)
        paint_head(20, 20, 30, 70, head_r + 3)
        paint_stroke(255, 255, 255, 255, lw)
        paint_head(255, 255, 255, 255, head_r)
        if alpha < 255:
            p.setOpacity(1.0)
        p.restore()

    def _draw_procedural(self, p, cx, cy, state, facing, alpha, dash_dir):
        """程序化生成姿势并绘制（无 poses.json 时使用，或非跑步/贴墙状态）"""
        hh = STICKMAN_H / 2 / self.ratio
        foot_y = cy + hh + STICKMAN_FOOT_SINK / self.ratio   # 脚底
        H = STICKMAN_H / self.ratio                          # 逻辑身高
        lw = max(2.0, H * 0.055)
        head_r = H * 0.11

        s = getattr(self, 'stickman', None)
        phase = (s.anim_phase if s else 0.0) * 2.0 * math.pi  # 奔跑相位（弧度）
        anim_t = s.anim_t if s else 0.0                       # 呼吸等时间动画

        def P(lx, ly):
            return QPointF(cx + facing * lx, foot_y + ly)

        # ── 默认站立关节点（各状态可覆盖）──
        shoulder = (0.0, -0.80 * H)
        hip      = (0.0, -0.42 * H)
        head     = (0.0, -0.90 * H)
        leg_f = [(0.055 * H, -0.21 * H), (0.055 * H, 0.0)]
        leg_b = [(-0.055 * H, -0.21 * H), (-0.055 * H, 0.0)]
        arm_f = [(0.10 * H, -0.66 * H), (0.13 * H, -0.50 * H)]
        arm_b = [(-0.10 * H, -0.66 * H), (-0.13 * H, -0.50 * H)]

        if state == Stickman.RUN:
            a = phase
            sw = math.sin(a)
            # 身体前倾、略弓身（跑步冲刺姿态）
            shoulder = (0.05 * H, -0.80 * H)
            hip  = (0.02 * H, -0.41 * H)
            head = (0.06 * H, -0.90 * H)
            # ── 双腿正运动学：大腿+小腿，交替蹬地与前抬屈膝（幅度克制更顺滑）──
            TL, SL = 0.20 * H, 0.205 * H
            def _leg(base_a, knee_bend):
                kx = hip[0] + math.sin(base_a) * TL
                ky = hip[1] + math.cos(base_a) * TL
                a2 = base_a - knee_bend
                fx = kx + math.sin(a2) * SL
                fy = ky + math.cos(a2) * SL
                return (kx, ky), (fx, fy)
            a_f = 0.34 + 0.48 * sw          # 前腿角度
            a_b = 0.34 - 0.48 * sw          # 后腿角度（与前腿相反）
            k_f, f_f = _leg(a_f, 0.18 + 0.42 * max(0.0, -sw))
            k_b, f_b = _leg(a_b, 0.18 + 0.42 * max(0.0, sw))
            leg_f = [k_f, f_f]
            leg_b = [k_b, f_b]
            # ── 手臂正运动学：与同侧腿相反摆动，微微弯曲、幅度克制 ──
            UL, FL = 0.16 * H, 0.13 * H
            def _arm(base_a, elbow_bend):
                ex = shoulder[0] + math.sin(base_a) * UL
                ey = shoulder[1] + math.cos(base_a) * UL
                a2 = base_a - elbow_bend
                hx = ex + math.sin(a2) * FL
                hy = ey + math.cos(a2) * FL
                return (ex, ey), (hx, hy)
            e_f, h_f = _arm(0.06 - 0.38 * sw, 0.85)
            e_b, h_b = _arm(0.06 + 0.38 * sw, 0.85)
            arm_f = [e_f, h_f]
            arm_b = [e_b, h_b]
        elif state == Stickman.CROUCH:
            # 单膝下跪：后腿跪地（小腿贴地）、前腿弯曲脚掌着地、躯干前倾、双臂前搭
            shoulder = (0.04 * H, -0.50 * H)
            hip  = (0.02 * H, -0.24 * H)
            head = (0.05 * H, -0.62 * H)
            leg_f = [(0.12 * H, -0.18 * H), (0.15 * H, 0.0)]           # 前腿弯曲脚掌着地
            leg_b = [(-0.02 * H, -0.03 * H), (-0.11 * H, -0.03 * H)]   # 后腿跪地
            arm_f = [(0.10 * H, -0.40 * H), (0.14 * H, -0.26 * H)]     # 前臂搭在前膝附近
            arm_b = [(0.00 * H, -0.40 * H), (0.02 * H, -0.26 * H)]     # 后臂自然前搭
        elif state == Stickman.JUMP:
            shoulder = (0.01 * H, -0.82 * H)
            hip  = (0.0, -0.40 * H)
            head = (0.01 * H, -0.92 * H)
            leg_f = [(0.02 * H, -0.26 * H), (0.04 * H, -0.30 * H)]     # 收腿
            leg_b = [(-0.02 * H, -0.28 * H), (-0.04 * H, -0.31 * H)]
            arm_f = [(-0.16 * H, -0.76 * H), (-0.12 * H, -0.97 * H)]   # 前臂上举
            arm_b = [(0.06 * H, -0.78 * H), (0.04 * H, -0.95 * H)]
        elif state == Stickman.WALL:
            # 自然贴墙：身体贴近墙面、姿态平稳，一手抵墙、一手自然下搭，
            # 一脚弯曲抵墙、一脚舒展抵墙，动作收敛不夸张
            shoulder = (0.02 * H, -0.82 * H)
            hip  = (0.0, -0.42 * H)
            head = (0.03 * H, -0.92 * H)
            arm_b = [(-0.14 * H, -0.72 * H), (-0.18 * H, -0.56 * H)]  # 抵墙手
            arm_f = [(0.04 * H, -0.64 * H), (0.06 * H, -0.46 * H)]    # 下搭手
            leg_b = [(-0.10 * H, -0.30 * H), (-0.15 * H, -0.16 * H)]  # 弯曲抵墙脚
            leg_f = [(-0.05 * H, -0.20 * H), (-0.10 * H, -0.05 * H)]  # 舒展抵墙脚
        elif state == Stickman.DASH:
            sw = math.sin(phase * 1.6)
            lean = 0.07 * H
            shoulder = (lean, -0.82 * H)
            hip  = (lean - 0.03 * H, -0.44 * H)
            head = (lean, -0.92 * H)
            leg_f = [(0.06 * H, -0.24 * H), (0.10 * H, 0.0)]              # 前腿大步
            leg_b = [(-0.13 * H, -0.20 * H), (-0.17 * H + 0.02 * H * sw, 0.0)]
            arm_f = [(0.10 * H, -0.74 * H), (0.16 * H, -0.58 * H)]        # 前臂前伸
            arm_b = [(-0.12 * H, -0.78 * H), (-0.18 * H, -0.66 * H)]      # 后臂后摆
        else:  # IDLE
            b = math.sin(anim_t * 2.2) * 0.012 * H     # 呼吸起伏
            shoulder = (0.0, -0.80 * H + b)
            hip  = (0.0, -0.42 * H)
            head = (0.0, -0.90 * H + b * 0.5)

        # 关节连线（按远近顺序：后腿 → 后臂 → 躯干 → 前腿 → 前臂）
        strokes = [
            [hip, leg_b[0], leg_b[1]],
            [shoulder, arm_b[0], arm_b[1]],
            [shoulder, hip],
            [hip, leg_f[0], leg_f[1]],
            [shoulder, arm_f[0], arm_f[1]],
        ]
        head_c = P(*head)

        def paint_stroke(cr, cg, cb, a, w):
            pen2 = QPen(QColor(cr, cg, cb, a))
            pen2.setWidthF(w)
            pen2.setCapStyle(Qt.RoundCap)
            pen2.setJoinStyle(Qt.RoundJoin)
            p.setPen(pen2)
            for seg in strokes:
                pts = [P(x, y) for x, y in seg]
                for i in range(len(pts) - 1):
                    p.drawLine(pts[i], pts[i + 1])

        def paint_head(cr, cg, cb, a, r):
            p.setBrush(QColor(cr, cg, cb, a))
            p.setPen(Qt.NoPen)
            p.drawEllipse(head_c, r, r)

        p.save()
        if alpha < 255:
            p.setOpacity(alpha / 255.0)

        # 第 1 遍：深色轮廓，保证浅色背景下可见
        paint_stroke(20, 20, 30, 70, lw + 4)
        paint_head(20, 20, 30, 70, head_r + 3)

        # 第 2 遍：白色主体
        paint_stroke(255, 255, 255, 255, lw)
        paint_head(255, 255, 255, 255, head_r)

        if alpha < 255:
            p.setOpacity(1.0)
        p.restore()

    # ── 主循环 ──
    def _tick(self):
        try:
            self._tick_inner()
        except Exception:
            import traceback
            traceback.print_exc()
            with open(os.path.join(SCRIPT_DIR, 'crash_log.txt'), 'a', encoding='utf-8') as f:
                traceback.print_exc(file=f)

    def _tick_inner(self):
        now = time.time()
        dt = min(now - self.last_time, 1 / 30)
        self.last_time = now

        while not self.key_events.empty():
            typ, key = self.key_events.get()
            if typ == 'press':
                self._handle_press(key)
            # release 已在回调中直接处理 keys.discard，这里不需要再处理

        if self.phase == 'game' and self.stickman:
            self.analyzer.analyze(self.stickman.x, self.stickman.y)
            self.stickman.update(
                self.analyzer, self.keys, dt,
                self.screen_w, self.screen_h
            )

        self.update()

    # ── WASD/空格 → 方向键映射 ──
    _KEY_MAP = {
        pkb.KeyCode.from_char('a'): Key.left,  pkb.KeyCode.from_char('A'): Key.left,
        pkb.KeyCode.from_char('d'): Key.right, pkb.KeyCode.from_char('D'): Key.right,
        pkb.KeyCode.from_char('w'): Key.up,    pkb.KeyCode.from_char('W'): Key.up,
        pkb.KeyCode.from_char('s'): Key.down,   pkb.KeyCode.from_char('S'): Key.down,
    }

    # pynput 有时把方向键以 KeyCode(vk=...) 形式投递（而非 Key 枚举），
    # 这里按 vk 码统一归一到 Key 枚举，避免 self.keys 里存的对象和
    # update() 中 `Key.right in keys` 判断不一致。
    _VK_TO_KEY = {
        0x25: Key.left,  0x26: Key.up,  0x27: Key.right, 0x28: Key.down,
        0x20: Key.space, 0x1B: Key.esc, 0x71: Key.f2,
        0x57: Key.up,    0x41: Key.left, 0x53: Key.down, 0x44: Key.right,
    }

    def _map_key(self, key):
        if key == Key.space:
            return Key.up
        mapped = self._KEY_MAP.get(key)
        if mapped is not None:
            return mapped
        # pynput KeyCode 兜底：按 vk 码归一
        vk = getattr(key, 'vk', None)
        if vk is not None:
            mk = self._VK_TO_KEY.get(int(vk))
            if mk is not None:
                return Key.up if mk == Key.space else mk
        return key

    # 引用计数在自动连发(按住不放时 Windows 反复投递 WM_KEYDOWN)和
    # 偶发丢失的 release 面前仍然不可靠：计数会被连发无限抬高，一旦某个
    # 源漏投 release，计数永远归不了零，下一次真正的按下就被当成"已按下"
    # 而跳过，表现为"按右键无反应"。
    # 彻底解决办法：只启用一个键盘源（全局低级钩子优先，失败再回退 pynput），
    # 单源 + set 去重对连发天然幂等（重复 press 命中 set 直接跳过）。
    _key_pressed = set()
    _key_lock = threading.Lock()

    def _on_key_press(self, key):
        key = self._map_key(key)
        with self._key_lock:
            if key not in self._key_pressed:
                self._key_pressed.add(key)
                self.keys.add(key)          # 直接加入，立即生效
                self.key_events.put(('press', key))

    def _on_key_release(self, key):
        key = self._map_key(key)
        with self._key_lock:
            self._key_pressed.discard(key)
            self.keys.discard(key)         # 直接移除，立即生效
        self.key_events.put(('release', key))

    def _handle_press(self, key):
        if key == Key.esc:
            self.close()
            return

        if key == Key.f2:
            self.toggle_panel()
            return

        # keys 已在回调中 add，这里只处理跳跃和冲刺
        now = time.time()

        # 双击检测 → 冲刺
        if key in self.last_key_time:
            gap = now - self.last_key_time[key]
            if gap < DOUBLE_TAP_WINDOW:
                if self.stickman:
                    if key == Key.left:
                        self.stickman.start_dash(-1, 0)
                    elif key == Key.right:
                        self.stickman.start_dash(1, 0)
                    elif key == Key.up:
                        self.stickman.start_dash(0, -1)
                    elif key == Key.down:
                        self.stickman.start_dash(0, 1)
        self.last_key_time[key] = now

        # 跳跃
        if key == Key.up or key == Key.space:
            if self.stickman:
                self.stickman.try_jump()

    def closeEvent(self, ev):
        if getattr(self, 'listener', None):
            self.listener.stop()
        if getattr(self, 'tray', None):
            self.tray.hide()
        super().closeEvent(ev)
        if getattr(self, 'panel', None):
            self.panel.close()

    def toggle_panel(self):
        if getattr(self, 'panel', None) and self.panel.isVisible():
            self.panel.hide()
        else:
            if not getattr(self, 'panel', None):
                self.panel = CfgPanel()
            self.panel.show()
            self.panel.raise_()


# ============ 实时调参面板 ============
# 每个参数一行：名称 + 数值框 + 滑条，改动直接写入 CFG 字典，主循环每帧读取，立即生效
# 快捷键 F2 打开/关闭，ESC 退出程序

# (键, 中文名, 最小, 最大, 步长, 小数位)
_CFG_ITEMS = [
    ('SCAN_RADIUS',      '扫描半径(px)',     50,  600, 10, 0),
    ('COLOR_THRESHOLD',  '颜色差异阈值',      2,  120, 1,  0),
    ('MIN_EDGE_LENGTH',  '地面最小边缘(px)',  2,  80,  1,  0),
    ('CEIL_MIN_EDGE',    '天花板最小边缘(px)', 6, 120, 1, 0),
    ('WALL_RATIO',       '判墙边缘占比',    0.10, 1.0, 0.05, 2),
    ('WALL_TOL',         '判墙容差(px)',      0,  20, 1,  0),
    ('GRAVITY',          '重力加速度',      0.2,  6.0, 0.1, 1),
    ('MOVE_SPEED',       '移动速度',        1.0, 15.0, 0.5, 1),
    ('JUMP_FORCE',       '跳跃力度',        4.0, 40.0, 0.5, 1),
    ('WALL_SLIDE_SPEED', '贴墙下滑速度',    0.5, 12.0, 0.5, 1),
    ('DASH_SPEED',       '冲刺速度',        5.0, 60.0, 1.0, 1),
    ('DASH_DURATION',    '冲刺时长(s)',    0.05,  1.0, 0.05, 2),
    ('RUN_PACE',         '跑步步幅(px/循环)', 30, 240, 1, 0),
    ('IMG_SCALE',        '火柴人大小',      0.3,  2.0, 0.05, 2),
]


# ============ 参数配置存档 & 动作(姿势)存档 ============

CFG_DEFAULTS = dict(CFG)   # 内置默认参数（只读，用户不可直接改动）
CFG_PROFILE_PATH = os.path.join(SCRIPT_DIR, 'cfg_profiles.json')
POSE_PROFILE_PATH = os.path.join(SCRIPT_DIR, 'pose_profiles.json')


def _load_json_dict(path, default):
    try:
        import io
        if not os.path.exists(path):
            return default
        with io.open(path, encoding='utf-8') as f:
            d = json.load(f)
        if not isinstance(d, dict):
            return default
        d.setdefault('profiles', {})
        d.setdefault('active', '')
        return d
    except Exception:
        return default


def _save_json_dict(path, data):
    try:
        import io
        with io.open(path, 'w', encoding='utf-8') as f:
            json.dump(data, f, ensure_ascii=False, indent=1)
    except Exception:
        pass


def load_cfg_profiles():
    return _load_json_dict(CFG_PROFILE_PATH, {'profiles': {}, 'active': ''})


def save_cfg_profiles(data):
    _save_json_dict(CFG_PROFILE_PATH, data)


def load_pose_profiles():
    return _load_json_dict(POSE_PROFILE_PATH, {'profiles': {}, 'active': ''})


def save_pose_profiles(data):
    _save_json_dict(POSE_PROFILE_PATH, data)


def apply_cfg_profile(cfg):
    """把一份参数配置写入 CFG，缺失键回退到内置默认"""
    for key, _n, _l, _h, _s, _d in _CFG_ITEMS:
        if key in cfg:
            try:
                CFG[key] = float(cfg[key])
            except Exception:
                pass
        else:
            CFG[key] = CFG_DEFAULTS.get(key, CFG[key])


def _main_window():
    """找回主窗口实例"""
    for w in QApplication.topLevelWidgets():
        if isinstance(w, StickmanWindow):
            return w
    return None


def default_pose_bundle():
    """内置默认动作包（取自姿势编辑器默认姿势），作为无 poses.json 时的兜底"""
    try:
        import pose_editor as _pe
    except Exception:
        return load_poses_json()
    A = _pe.default_pose()
    return {
        'run_frames': _pe.build_run_frames(A, A),
        'run_start': A, 'run_end': A,
        'wall': _pe.default_wall(),
        'idle': _pe.default_pose(),
        'crouch': _pe.default_crouch(),
        'jump': _pe.default_jump(),
        'dash_r': _pe.default_dash_r(),
        'dash_up': _pe.default_dash_up(),
        'dash_down': _pe.default_dash_down(),
    }


def current_pose_bundle(win):
    """当前生效的整套动作：优先用之保存存档"""
    if win is not None and isinstance(getattr(win, 'poses', None), dict) and win.poses:
        return win.poses
    p = load_poses_json()
    if p:
        return p
    return default_pose_bundle()


class ProfileManagerDialog(QDialog):
    """存档管理对话框：列出存档，支持载入/删除/重命名"""
    def __init__(self, title, get_names, on_load, on_delete, on_rename, parent=None):
        super().__init__(parent, Qt.WindowStaysOnTopHint | Qt.Tool)
        self.setWindowTitle(title)
        self.resize(360, 420)
        self.setFont(QFont('Microsoft YaHei', 11))
        self.get_names = get_names
        self.on_load = on_load
        self.on_delete = on_delete
        self.on_rename = on_rename
        lay = QVBoxLayout(self)
        self.list = QListWidget()
        lay.addWidget(self.list)
        h = QHBoxLayout()
        for text, fn in (('载入', self._load), ('删除', self._delete), ('重命名', self._rename)):
            b = QPushButton(text)
            b.clicked.connect(fn)
            h.addWidget(b)
        bc = QPushButton('关闭')
        bc.clicked.connect(self.accept)
        h.addWidget(bc)
        lay.addLayout(h)
        self._reload()

    def _reload(self):
        self.list.clear()
        for n in self.get_names():
            self.list.addItem(n)
        if self.list.count():
            self.list.setCurrentRow(0)

    def _sel(self):
        it = self.list.currentItem()
        return it.text() if it else None

    def _load(self):
        n = self._sel()
        if n:
            self.on_load(n)

    def _delete(self):
        n = self._sel()
        if not n:
            return
        if QMessageBox.question(self, '删除', '确定删除存档 %r 吗？' % n) == QMessageBox.Yes:
            self.on_delete(n)
            self._reload()

    def _rename(self):
        n = self._sel()
        if not n:
            return
        new, ok = QInputDialog.getText(self, '重命名', '新名称：', text=n)
        new = (new or '').strip()
        if ok and new:
            self.on_rename(n, new)
            self._reload()


class ActionPanel(QWidget):
    """动作（姿势）面板：管理整套动作的存档，可恢复到默认值"""
    def __init__(self, win=None):
        super().__init__(None, Qt.WindowStaysOnTopHint | Qt.Tool)
        self.setWindowTitle('动作面板 - 姿势与动作存档管理')
        self.setFont(QFont('Microsoft YaHei', 13))
        self.resize(600, 380)
        self.win = win or _main_window()
        self.profiles = load_pose_profiles()

        lay = QVBoxLayout(self)
        tip = QLabel('整套动作（静止/跑步/贴墙/下蹲/跳跃/冲刺）。默认动作不会被改动；'
                     '你可以把当前动作保存为新存档、管理或载入存档，也可一键恢复到默认。')
        tip.setWordWrap(True)
        lay.addWidget(tip)
        self.info = QLabel('当前动作存档：' + self._active_name())
        lay.addWidget(self.info)
        for text, fn in (
            ('恢复正常默认值', self._restore_default),
            ('保存当前动作为新存档', self._save_new),
            ('动作存档管理…', self._manage),
            ('打开姿势编辑器(拖拽编辑)…', self._open_editor),
        ):
            b = QPushButton(text)
            b.clicked.connect(fn)
            lay.addWidget(b)
        self.status = QLabel('')
        self.status.setWordWrap(True)
        lay.addWidget(self.status)

    def _active_name(self):
        a = self.profiles.get('active', '')
        return a if a else '(默认)'

    def _refresh_info(self):
        self.info.setText('当前动作存档：' + self._active_name())

    def _restore_default(self):
        self.profiles['active'] = ''
        save_pose_profiles(self.profiles)
        if self.win is not None:
            self.win.poses = load_poses_json()   # 回到默认（使用 poses.json）
        self._refresh_info()
        self.status.setText('已恢复到默认动作（使用 poses.json）；如果想改默认请新建存档。')

    def _save_new(self):
        name, ok = QInputDialog.getText(self, '保存新存档', '存档名称：')
        name = (name or '').strip()
        if not ok or not name:
            return
        bundle = current_pose_bundle(self.win)
        self.profiles['profiles'][name] = bundle
        self.profiles['active'] = name
        save_pose_profiles(self.profiles)
        if self.win is not None:
            self.win.poses = dict(bundle)
        self._refresh_info()
        self.status.setText('已保存并存为当前动作存档：%s' % name)

    def _manage(self):
        dlg = ProfileManagerDialog(
            '动作存档管理',
            get_names=lambda: list(self.profiles['profiles'].keys()),
            on_load=self._load, on_delete=self._delete, on_rename=self._rename)
        dlg.exec_()
        self._refresh_info()

    def _load(self, name):
        if name not in self.profiles['profiles']:
            return
        self.profiles['active'] = name
        save_pose_profiles(self.profiles)
        if self.win is not None:
            self.win.poses = dict(self.profiles['profiles'][name])
        self.status.setText('已载入动作存档：%s' % name)

    def _delete(self, name):
        self.profiles['profiles'].pop(name, None)
        if self.profiles.get('active') == name:
            self.profiles['active'] = ''
        save_pose_profiles(self.profiles)
        if self.win is not None:
            self.win.poses = load_poses_json()

    def _rename(self, old, new):
        if old in self.profiles['profiles'] and new:
            self.profiles['profiles'][new] = self.profiles['profiles'].pop(old)
            if self.profiles.get('active') == old:
                self.profiles['active'] = new
            save_pose_profiles(self.profiles)

    def _open_editor(self):
        # 姿势编辑器直接内嵌到本进程（同为一个 exe），不再启动外部进程
        try:
            import pose_editor as _pe
            ed = getattr(self, '_editor_win', None)
            if ed is None or not ed.isVisible():
                ed = _pe.PoseEditor()
                self._editor_win = ed  # 持有引用，防止被 GC 回收
                ed.show()
            else:
                ed.raise_()
            self.status.setText('已打开姿势编辑器。编辑并保存 poses.json 后，'
                                '再到本面板「保存当前动作为新存档」收录。')
        except Exception as e:
            self.status.setText('打开姿势编辑器失败：%s' % e)


# ============ 设置 / 调参面板（参数与配置存档） ============
# 快捷键 F2 打开/关闭，ESC 退出程序


class CfgPanel(QWidget):
    """设置面板：实时调节参数；可一键恢复默认、另存/更新/管理配置存档"""

    def __init__(self, win=None):
        super().__init__(None, Qt.WindowStaysOnTopHint | Qt.Tool)
        self.setWindowTitle('设置 - 参数与配置存档')
        self.setFont(QFont('Microsoft YaHei', 13))
        self.win = win or _main_window()
        self.resize(660, 720)
        lay = QVBoxLayout(self)
        lay.setSpacing(5)

        tip = QLabel('改动即时生效。可一键恢复默认，或把当前参数保存为用户配置存档进行管理。')
        tip.setWordWrap(True)
        lay.addWidget(tip)

        self.profiles = load_cfg_profiles()
        self.active_label = QLabel('当前配置存档：' + self._active_name())
        lay.addWidget(self.active_label)

        hl = QHBoxLayout()
        self.name_edit = QLineEdit()
        self.name_edit.setPlaceholderText('新存档名称')
        hl.addWidget(self.name_edit, 1)
        b_new = QPushButton('另存为新存档')
        b_new.clicked.connect(self.save_as_new)
        hl.addWidget(b_new)
        b_upd = QPushButton('更新当前存档')
        b_upd.clicked.connect(self.update_current)
        hl.addWidget(b_upd)
        lay.addLayout(hl)

        h2 = QHBoxLayout()
        b_res = QPushButton('恢复正常默认值')
        b_res.clicked.connect(self.restore_default)
        h2.addWidget(b_res)
        b_man = QPushButton('存档管理…')
        b_man.clicked.connect(self.manage_cfg)
        h2.addWidget(b_man)
        b_act = QPushButton('动作面板')
        b_act.clicked.connect(self.open_action_panel)
        h2.addWidget(b_act)
        lay.addLayout(h2)

        self.widgets = {}
        grid = QGridLayout()
        grid.setHorizontalSpacing(8)
        grid.setVerticalSpacing(4)
        for row, (key, name, lo, hi, step, dec) in enumerate(_CFG_ITEMS):
            lab = QLabel(name)
            spin = QDoubleSpinBox()
            spin.setRange(lo, hi)
            spin.setDecimals(dec)
            spin.setSingleStep(step)
            spin.setValue(CFG[key])
            sld = QSlider(Qt.Horizontal)
            scale = 10 ** dec
            sld.setRange(int(lo * scale), int(hi * scale))
            sld.setValue(int(CFG[key] * scale))

            def make_spin(k=key):
                def on_spin(v):
                    CFG[k] = v
                    self._sync(k)
                return on_spin

            def make_sld(k=key, sc=scale):
                def on_sld(v):
                    CFG[k] = v / sc
                    self._sync(k)
                return on_sld

            spin.valueChanged.connect(make_spin())
            sld.valueChanged.connect(make_sld())
            grid.addWidget(lab, row, 0)
            grid.addWidget(spin, row, 1)
            grid.addWidget(sld, row, 2)
            self.widgets[key] = (spin, sld, scale)
        lay.addLayout(grid)

        self.status = QLabel('')
        self.status.setWordWrap(True)
        lay.addWidget(self.status)

    def _active_name(self):
        a = self.profiles.get('active', '')
        return a if a else '(默认)'

    def _refresh_active_label(self):
        self.active_label.setText('当前配置存档：' + self._active_name())

    def _sync(self, changed):
        spin, sld, scale = self.widgets[changed]
        spin.blockSignals(True); sld.blockSignals(True)
        spin.setValue(CFG[changed])
        sld.setValue(int(CFG[changed] * scale))
        spin.blockSignals(False); sld.blockSignals(False)
        if changed == 'IMG_SCALE':
            w = _main_window()
            if w is not None:
                w.img_size = int(128 * CFG['IMG_SCALE'])
                w._apply_hitbox()

    def _cfg_snapshot(self):
        return {key: CFG[key] for key, _n, _l, _h, _s, _d in _CFG_ITEMS}

    def _reload_ui_from_cfg(self):
        for key, _n, _l, _h, _s, dec in _CFG_ITEMS:
            spin, sld, scale = self.widgets[key]
            spin.blockSignals(True); sld.blockSignals(True)
            spin.setValue(CFG[key])
            sld.setValue(int(CFG[key] * scale))
            spin.blockSignals(False); sld.blockSignals(False)
        w = _main_window()
        if w is not None:
            w.img_size = int(128 * CFG['IMG_SCALE'])
            w._apply_hitbox()

    def restore_default(self):
        apply_cfg_profile(CFG_DEFAULTS)
        self.profiles['active'] = ''
        save_cfg_profiles(self.profiles)
        self._reload_ui_from_cfg()
        self._refresh_active_label()
        self.status.setText('已恢复正常默认值。可另存为新的用户存档以保存你的设置。')

    def save_as_new(self):
        name = (self.name_edit.text() or '').strip()
        if not name:
            self.status.setText('请先在输入框填写新存档名称。')
            return
        self.profiles['profiles'][name] = self._cfg_snapshot()
        self.profiles['active'] = name
        save_cfg_profiles(self.profiles)
        self._refresh_active_label()
        self.status.setText('已另存为新配置存档：%s（并设为当前）' % name)

    def update_current(self):
        name = self.profiles.get('active', '')
        if not name or name not in self.profiles['profiles']:
            self.status.setText('当前没有正在使用的用户存档，请先「另存为新存档」。')
            return
        self.profiles['profiles'][name] = self._cfg_snapshot()
        save_cfg_profiles(self.profiles)
        self.status.setText('已更新当前配置存档：%s' % name)

    def manage_cfg(self):
        def on_load(name):
            if name in self.profiles['profiles']:
                apply_cfg_profile(self.profiles['profiles'][name])
                self.profiles['active'] = name
                save_cfg_profiles(self.profiles)
                self._reload_ui_from_cfg()
                self.status.setText('已载入配置存档：%s' % name)

        def on_delete(name):
            self.profiles['profiles'].pop(name, None)
            if self.profiles.get('active') == name:
                self.profiles['active'] = ''
                apply_cfg_profile(CFG_DEFAULTS)
                self._reload_ui_from_cfg()
            save_cfg_profiles(self.profiles)
            self._refresh_active_label()

        def on_rename(old, new):
            if old in self.profiles['profiles'] and new:
                self.profiles['profiles'][new] = self.profiles['profiles'].pop(old)
                if self.profiles.get('active') == old:
                    self.profiles['active'] = new
                save_cfg_profiles(self.profiles)

        dlg = ProfileManagerDialog(
            '配置存档管理',
            get_names=lambda: list(self.profiles['profiles'].keys()),
            on_load=on_load, on_delete=on_delete, on_rename=on_rename)
        dlg.exec_()
        self._refresh_active_label()

    def open_action_panel(self):
        pnl = getattr(self, '_action_panel', None)
        if pnl is None or not pnl.isVisible():
            pnl = ActionPanel(_main_window() or self.win)
            self._action_panel = pnl
            pnl.show()
        else:
            pnl.raise_()


if __name__ == '__main__':
    _bootstrap_data_files()
    _load_saved_cfg()
    app = QApplication(sys.argv)
    win = StickmanWindow()
    win.show()
    sys.exit(app.exec_())
