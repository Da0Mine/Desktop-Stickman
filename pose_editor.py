#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
火柴人姿势编辑器
================
运行：  python pose_editor.py

功能：
  1. 左侧大画布里的白色火柴人，直接用鼠标拖拽各关节点摆姿势。
  2. 用右侧下拉框切换三个槽位：
       跑步起点(A)、跑步终点(B)、右墙(WALL_R)
  3. 勾选「预览跑步」可预览由 A、B 插值补全的整段跑步动画。
  4. 点击「保存 poses.json」：
       - 由 A、B 补全跑步中间姿势（A→B→A 完整循环，默认 12 帧）
       - 由你摆的右墙姿势镜像出左墙姿势
       写入 SCRIPT_DIR/poses.json，供桌宠启动时读取使用。
  5. 「重置当前槽」恢复该槽为默认站姿；「载入 poses.json」读取已保存的姿态。
"""
import sys
import os
import json
import math

from PyQt5.QtWidgets import (
    QApplication, QWidget, QLabel, QComboBox, QCheckBox, QPushButton,
    QHBoxLayout, QVBoxLayout, QFrame, QMessageBox
)
from PyQt5.QtCore import Qt, QTimer, QPointF
from PyQt5.QtGui import QPainter, QPen, QColor, QFont

# 打包成 exe 后 __file__ 指向临时解压目录，数据文件(poses.json 等)必须读写 exe 同目录
SCRIPT_DIR = os.path.dirname(os.path.abspath(
    sys.executable if getattr(sys, 'frozen', False) else __file__))
POSES_PATH = os.path.join(SCRIPT_DIR, 'poses.json')
POSE_PROFILES_PATH = os.path.join(SCRIPT_DIR, 'pose_profiles.json')

# 无控制台模式(stdout/stderr 为 None)下 print 会抛异常；崩溃信息写入日志便于排查
if getattr(sys, 'frozen', False):
    import io as _io
    try:
        _log = _io.open(os.path.join(SCRIPT_DIR, 'crash_log.txt'), 'a', encoding='utf-8')
        sys.stdout = _log
        sys.stderr = _log
        import faulthandler
        faulthandler.enable(file=_log)
    except Exception:
        pass


def _read_pose_profiles():
    """读取游戏的动作存档（pose_profiles.json），结构 {profiles:{名:整套动作}, active:名}"""
    import io as _io
    try:
        if not os.path.exists(POSE_PROFILES_PATH):
            return {'profiles': {}, 'active': ''}
        with _io.open(POSE_PROFILES_PATH, encoding='utf-8') as f:
            d = json.load(f)
        if not isinstance(d, dict):
            return {'profiles': {}, 'active': ''}
        d.setdefault('profiles', {})
        d.setdefault('active', '')
        return d
    except Exception:
        return {'profiles': {}, 'active': ''}


def _save_pose_profiles(data):
    import io as _io
    try:
        with _io.open(POSE_PROFILES_PATH, 'w', encoding='utf-8') as f:
            json.dump(data, f, ensure_ascii=False, indent=1)
    except Exception:
        pass

RUN_FRAME_COUNT = 30  # 生成的跑步循环总帧数（插帧越密越连贯）

# 关节点名称（与桌宠 stickman_pet.py 中使用的命名一致）
JOINT_NAMES = ["head", "shoulder", "hip",
               "knee_f", "foot_f", "knee_b", "foot_b",
               "elbow_f", "hand_f", "elbow_b", "hand_b"]


def default_pose():
    """默认站姿，坐标为身高比例（x=0 中心，y 负为向上，脚底 y=0）"""
    return {
        "head": (0.00, -0.92), "shoulder": (0.00, -0.80), "hip": (0.00, -0.42),
        "knee_f": (0.055, -0.21), "foot_f": (0.055, 0.0),
        "knee_b": (-0.055, -0.21), "foot_b": (-0.055, 0.0),
        "elbow_f": (0.10, -0.66), "hand_f": (0.13, -0.50),
        "elbow_b": (-0.10, -0.66), "hand_b": (-0.13, -0.50),
    }


def default_wall():
    """默认右墙贴墙姿势：墙体在右侧(+x)，一手抵墙、一脚屈抵墙、一脚略直抵墙、一手自然下搭"""
    return {
        "head": (0.03, -0.92), "shoulder": (0.02, -0.82), "hip": (0.0, -0.42),
        "knee_f": (0.06, -0.20), "foot_f": (0.10, -0.06),
        "knee_b": (0.14, -0.30), "foot_b": (0.19, -0.18),
        "elbow_f": (0.14, -0.72), "hand_f": (0.18, -0.56),
        "elbow_b": (-0.04, -0.64), "hand_b": (-0.06, -0.46),
    }


def default_crouch():
    """默认下蹲（单膝下跪）姿势"""
    return {
        "head": (0.05, -0.62), "shoulder": (0.04, -0.50), "hip": (0.02, -0.24),
        "knee_f": (0.12, -0.18), "foot_f": (0.15, 0.0),
        "knee_b": (-0.02, -0.03), "foot_b": (-0.11, -0.03),
        "elbow_f": (0.10, -0.40), "hand_f": (0.14, -0.26),
        "elbow_b": (0.00, -0.40), "hand_b": (0.02, -0.26),
    }


def default_jump():
    """默认跳跃（收腿、双臂上举）姿势"""
    return {
        "head": (0.01, -0.92), "shoulder": (0.01, -0.82), "hip": (0.0, -0.40),
        "knee_f": (0.04, -0.30), "foot_f": (0.05, -0.30),
        "knee_b": (-0.06, -0.31), "foot_b": (-0.05, -0.32),
        "elbow_f": (-0.12, -0.97), "hand_f": (-0.14, -1.00),
        "elbow_b": (0.05, -0.96), "hand_b": (0.04, -1.00),
    }


def default_dash_r():
    """默认向右冲刺姿势（前倾、一臂前伸一臂后摆）"""
    return {
        "head": (0.06, -0.88), "shoulder": (0.05, -0.80), "hip": (0.02, -0.42),
        "knee_f": (0.06, -0.24), "foot_f": (0.10, 0.0),
        "knee_b": (-0.13, -0.20), "foot_b": (-0.17, -0.02),
        "elbow_f": (0.10, -0.70), "hand_f": (0.16, -0.56),
        "elbow_b": (-0.12, -0.74), "hand_b": (-0.18, -0.64),
    }


def default_dash_up():
    """默认向上冲刺姿势（双臂上扬、身体竖直）"""
    return {
        "head": (0.0, -0.94), "shoulder": (0.0, -0.86), "hip": (0.0, -0.48),
        "knee_f": (0.03, -0.28), "foot_f": (0.06, -0.12),
        "knee_b": (-0.03, -0.28), "foot_b": (-0.06, -0.12),
        "elbow_f": (-0.14, -0.92), "hand_f": (-0.16, -1.02),
        "elbow_b": (0.13, -0.94), "hand_b": (0.16, -1.02),
    }


def default_dash_down():
    """默认向下冲刺姿势（身体微蜷、双臂朝下摆）"""
    return {
        "head": (0.02, -0.76), "shoulder": (0.02, -0.68), "hip": (0.0, -0.32),
        "knee_f": (0.06, -0.12), "foot_f": (0.06, 0.04),
        "knee_b": (-0.06, -0.12), "foot_b": (-0.06, 0.04),
        "elbow_f": (-0.12, -0.78), "hand_f": (-0.14, -0.88),
        "elbow_b": (0.12, -0.80), "hand_b": (0.14, -0.90),
    }


def _lerp(a, b, t):
    return (a[0] + (b[0] - a[0]) * t, a[1] + (b[1] - a[1]) * t)


def _smooth(t):
    return t * t * (3 - 2 * t)


def build_run_frames(A, B, n=RUN_FRAME_COUNT):
    """由两个端点姿势补全完整跑步循环：A→B→A。
    用三角波相位 t→0..1..0：起点为 A，中间(中点)精确为 B，末尾回到 A，全帧平滑无回跳。"""
    frames = []
    for i in range(n):
        t = i / n                                     # 0..(n-1)/n
        u = 2.0 * t if t < 0.5 else 2.0 * (1.0 - t)   # 三角波：0→1→0
        s = _smooth(u)
        frame = {k: _lerp(A[k], B[k], s) for k in JOINT_NAMES}
        frames.append(frame)
    return frames


def mirror_pose(pose):
    """沿垂直轴镜像姿势（用于右墙 → 左墙）"""
    return {k: (-p[0], p[1]) for k, p in pose.items()}


class PoseCanvas(QWidget):
    """负责绘制火柴人并响应鼠标拖拽关节点的画布"""

    def __init__(self, editor):
        super().__init__()
        self.editor = editor
        self.dragging = None        # 当前被拖拽的关节点名
        self.anim_t = 0.0
        self.setMinimumSize(640, 600)

    # ---------------- 坐标换算 ----------------
    def _scale(self):
        h = self.height()
        return max(60, int(h * 0.80))   # 身高→像素

    def _cx(self):
        return self.width() // 2

    def _base(self):            # 脚底所在的行
        return self.height() * 9 // 10

    def _pt(self, fx, fy):
        return QPointF(self._cx() + fx * self._scale(),
                       self._base() + fy * self._scale())

    # ---------------- 绘制 ----------------
    def paintEvent(self, ev):
        p = QPainter(self)
        p.setRenderHint(QPainter.Antialiasing)
        p.fillRect(self.rect(), QColor(245, 245, 248))

        # 地面参考线
        pen = QPen(QColor(180, 180, 190))
        pen.setStyle(Qt.DashLine)
        p.setPen(pen)
        gy = self._base()
        p.drawLine(40, gy, self.width() - 40, gy)
        p.setFont(QFont('Microsoft YaHei', 9))
        p.drawText(8, gy - 4, '脚底线')

        pose = self.editor.current_pose()
        color = QColor(30, 30, 40)

        if self.editor.preview_run:
            self._draw_run_preview(p)

        # 当前槽位主模型（可拖拽）
        self._draw_stick(p, pose, self._cx(), self._base(), self._scale(),
                         1, on_screen_joints=True)

        # 右墙槽位：额外淡显左墙镜像 结果 供预览
        if self.editor.slot_key() == 'wall':
            m = mirror_pose(pose)
            ox = self._cx() - self._scale() * 1.1
            if ox < 40:
                ox = 40
            self._draw_stick(p, m, ox, self._base(), int(self._scale() * 0.9), 1,
                             color=QColor(90, 90, 110), on_screen_joints=False)
            of = QFont('Microsoft YaHei', 9)
            p.setFont(of)
            p.setPen(QColor(90, 90, 110))
            p.drawText(int(ox) - 20, self._base() + 22, '左墙(镜像)')

    def _draw_stick(self, p, pose, ox, oy, scale, fl, on_screen_joints=True,
                    color=QColor(30, 30, 40)):
        """按归一化姿势绘制火柴人；fl 为水平镜像标志"""
        def pt(fx, fy):
            return QPointF(ox + fl * fx * scale, oy + fy * scale)

        head = pt(*pose['head'])
        shoulder = pt(*pose['shoulder'])
        hip = pt(*pose['hip'])
        lw = max(2.0, scale * 0.055)
        head_r = scale * 0.11

        strokes = [
            [hip, pt(*pose['knee_b']), pt(*pose['foot_b'])],
            [shoulder, pt(*pose['elbow_b']), pt(*pose['hand_b'])],
            [shoulder, hip],
            [hip, pt(*pose['knee_f']), pt(*pose['foot_f'])],
            [shoulder, pt(*pose['elbow_f']), pt(*pose['hand_f'])],
        ]
        pen = QPen(color)
        pen.setWidthF(lw)
        pen.setCapStyle(Qt.RoundCap)
        pen.setJoinStyle(Qt.RoundJoin)
        p.setPen(pen)
        for seg in strokes:
            for i in range(len(seg) - 1):
                p.drawLine(seg[i], seg[i + 1])
        p.setBrush(color)
        p.setPen(Qt.NoPen)
        p.drawEllipse(head, head_r, head_r)

        if on_screen_joints:
            p.setBrush(QColor(220, 40, 60))
            for name in JOINT_NAMES:
                q = pt(*pose[name])
                p.drawEllipse(q, 5, 5)

    def _draw_run_preview(self, p):
        """左下角小尺寸预览刚才生成的跑步动画"""
        A = self.editor.slots['start']
        B = self.editor.slots['end']
        frames = build_run_frames(A, B)
        idx = int(self.anim_t * 10) % len(frames)
        pose = frames[idx]
        scale = int(self._scale() * 0.42)
        ox = 70
        oy = self.height() - 100
        p.setFont(QFont('Microsoft YaHei', 9))
        p.setPen(QColor(120, 120, 140))
        p.drawText(ox - 40, oy - scale - 10, '跑步预览(A→B→A)')
        self._draw_stick(p, pose, ox, oy, scale, 1,
                         color=QColor(60, 60, 80), on_screen_joints=False)

    # ---------------- 鼠标交互 ----------------
    def _pose_to_screen(self, name):
        pose = self.editor.current_pose()
        if name in pose:
            return self._pt(*pose[name])

    def _screen_to_pose(self, x, y):
        fx = (x - self._cx()) / self._scale()
        fy = (y - self._base()) / self._scale()
        return fx, fy

    def mousePressEvent(self, ev):
        pos = ev.pos()
        best, best_d = None, 1e9
        for name in JOINT_NAMES:
            q = self._pose_to_screen(name)
            if q is None:
                continue
            d = (q.x() - pos.x()) ** 2 + (q.y() - pos.y()) ** 2
            if d < best_d:
                best_d, best = d, name
        if best is not None and best_d < 400:   # 20px 半径
            self.dragging = best
            self.setCursor(Qt.ClosedHandCursor)

    def mouseMoveEvent(self, ev):
        if self.dragging:
            fx, fy = self._screen_to_pose(ev.pos().x(), ev.pos().y())
            self.editor.set_joint(self.dragging, (fx, fy))
            self.editor.refresh()

    def mouseReleaseEvent(self, ev):
        if self.dragging:
            self.dragging = None
            self.unsetCursor()


class PoseEditor(QWidget):
    def __init__(self):
        super().__init__()
        self.setWindowTitle('火柴人姿势编辑器')
        self.resize(1040, 660)
        self.slots = {'idle': default_pose(),
                  'start': default_pose(), 'end': default_pose(),
                  'wall': default_wall(),
                  'crouch': default_crouch(),
                  'jump': default_jump(),
                  'dash_r': default_dash_r(),
                  'dash_up': default_dash_up(),
                  'dash_down': default_dash_down()}
        self.slot_names = {'idle': '静止 (IDLE)',
                           'start': '跑步起点(A)', 'end': '跑步终点(B)',
                           'wall': '右墙(WALL_R)',
                           'crouch': '下蹲(CROUCH)',
                           'jump': '跳跃(JUMP)',
                           'dash_r': '冲刺->右(DASH_R)',
                           'dash_up': '冲刺->上(DASH_UP)',
                           'dash_down': '冲刺->下(DASH_DOWN)'}
        self.slot_key_order = ['idle', 'start', 'end', 'wall', 'crouch', 'jump',
                               'dash_r', 'dash_up', 'dash_down']
        # 当前槽位与下拉框第一项(静止 IDLE)保持一致，避免打开时画布与下拉显示错乱
        self.current = self.slot_key_order[0]
        self.preview_run = False
        self._source_profile = None   # 当前编辑的是哪个动作存档（None=默认/poses.json）

        self.canvas = PoseCanvas(self)

        # ------- 右侧控制面板 -------
        panel = QFrame(self)
        panel.setFixedWidth(290)
        lay = QVBoxLayout(panel)
        lay.setSpacing(8)

        title = QLabel('火柴人姿势编辑器')
        title.setFont(QFont('Microsoft YaHei', 15, QFont.Bold))
        lay.addWidget(title)

        help_ = QLabel('直接用鼠标拖动左侧火柴人的红色关节点来摆姿势。')
        help_.setWordWrap(True)
        lay.addWidget(help_)

        lay.addSpacing(6)
        lay.addWidget(QLabel('当前编辑槽位：'))
        self.slot_box = QComboBox()
        for k in self.slot_key_order:
            self.slot_box.addItem(self.slot_names[k], k)
        self.slot_box.currentIndexChanged.connect(self._on_slot_change)
        lay.addWidget(self.slot_box)

        self.preview_chk = QCheckBox('预览跑步动画 (A→B→A)')
        self.preview_chk.toggled.connect(self._on_preview_toggle)
        lay.addWidget(self.preview_chk)

        lay.addSpacing(10)
        btn_save = QPushButton('生成并保存  poses.json')
        btn_save.clicked.connect(self._save)
        lay.addWidget(btn_save)

        btn_reset = QPushButton('重置当前槽为默认站姿')
        btn_reset.clicked.connect(self._reset_slot)
        lay.addWidget(btn_reset)

        btn_load = QPushButton('载入 poses.json')
        btn_load.clicked.connect(self._load)
        lay.addWidget(btn_load)

        lay.addSpacing(10)
        self.load_state = QLabel('')
        self.load_state.setWordWrap(True)
        self.load_state.setStyleSheet('color:#0a6;')
        lay.addWidget(self.load_state)

        self.info = QLabel('提示：\n'
                           '· 静止 / 下蹲 / 跳跃：各摆一个姿势\n'
                           '· 跑步：摆 起点/终点 两个极限姿势，自动补全中间帧\n'
                           '· 右墙：摆 触墙姿势，左墙自动镜像\n'
                           '· 冲刺(右·上·下)：各摆一个，向左由向右镜像生成')
        self.info.setWordWrap(True)
        self.info.setStyleSheet('color:#666;')
        lay.addWidget(self.info)
        lay.addStretch(1)

        root = QHBoxLayout(self)
        root.setContentsMargins(6, 6, 6, 6)
        root.addWidget(self.canvas, 1)
        root.addWidget(panel)

        # 预览动画计时器
        self.timer = QTimer(self)
        self.timer.timeout.connect(self._tick_anim)
        self.timer.start(40)

        # 启动即自动载入：优先已被选中的动作存档，否则默认 poses.json/内置默认
        QTimer.singleShot(0, self._load_active_source)

    # ---------------- 载入基础（动作存档 / 默认） ----------------
    def _apply_bundle(self, bundle, source_label):
        """把整套动作({字段:姿势})填入各槽位"""
        if not isinstance(bundle, dict):
            return False
        if bundle.get('run_start') and bundle.get('run_end'):
            self.slots['start'] = {k: tuple(v) for k, v in bundle['run_start'].items()}
            self.slots['end'] = {k: tuple(v) for k, v in bundle['run_end'].items()}
        elif bundle.get('run_frames'):
            n = len(bundle['run_frames'])
            if n:
                self.slots['start'] = dict(bundle['run_frames'][0])
                self.slots['end'] = dict(bundle['run_frames'][n // 2])
        for key in ('wall', 'idle', 'crouch', 'jump', 'dash_r', 'dash_up', 'dash_down'):
            if bundle.get(key):
                self.slots[key] = {k: tuple(v) for k, v in bundle[key].items()}
        self.load_state.setText(source_label)
        self.refresh()
        return True

    def _load_active_source(self):
        """启动时：若用户在游戏里选过动作存档则载入该存档，否则载入默认 poses.json"""
        profiles = _read_pose_profiles()
        active = profiles.get('active', '')
        if active and active in profiles.get('profiles', {}):
            if self._apply_bundle(profiles['profiles'][active],
                                  '已载入动作存档：%s' % active):
                self._source_profile = active
                return
        # 无选中存档 → 载入默认
        if os.path.exists(POSES_PATH):
            try:
                import io
                d = json.load(io.open(POSES_PATH, encoding='utf-8'))
            except Exception:
                d = None
            if self._apply_bundle(d, '已载入默认 poses.json'):
                self._source_profile = None
                return
        self._source_profile = None
        self.load_state.setText('当前为内置默认姿势')
        self.refresh()

    # ---------------- 状态 ----------------
    def slot_key(self):
        return self.current

    def current_pose(self):
        return self.slots[self.current]

    def set_joint(self, name, val):
        self.slots[self.current][name] = val

    def refresh(self):
        self.canvas.update()

    def _on_slot_change(self, idx):
        self.current = self.slot_box.itemData(idx)
        self.refresh()

    def _on_preview_toggle(self, on):
        self.preview_run = on
        self.refresh()

    def _reset_slot(self):
        self.slots[self.current] = default_pose()
        self.refresh()

    def _tick_anim(self):
        if self.preview_run:
            self.canvas.anim_t += 0.045
            self.refresh()

    # ---------------- 保存 / 载入 ----------------
    def _save(self):
        A = self.slots['start']
        B = self.slots['end']
        wall_r = self.slots['wall']
        frames = build_run_frames(A, B)
        wall_l = mirror_pose(wall_r)
        data = {
            'run_frames': frames,
            'run_start': A,
            'run_end': B,
            'wall': wall_r,
            'wall_right': wall_r,
            'wall_left': wall_l,
            'idle': self.slots['idle'],
            'crouch': self.slots['crouch'],
            'jump': self.slots['jump'],
            'dash_r': self.slots['dash_r'],
            'dash_up': self.slots['dash_up'],
            'dash_down': self.slots['dash_down'],
        }
        try:
            import io
            with io.open(POSES_PATH, 'w', encoding='utf-8') as f:
                json.dump(data, f, ensure_ascii=False, indent=1)
        except Exception as e:
            QMessageBox.warning(self, '保存失败', str(e))
            return

        # 若当前编辑的是某个动作存档，则同步更新该存档（供游戏直接使用）
        synced = ''
        if self._source_profile:
            try:
                profiles = _read_pose_profiles()
                if self._source_profile in profiles['profiles']:
                    profiles['profiles'][self._source_profile] = data
                    profiles['active'] = self._source_profile
                    _save_pose_profiles(profiles)
                    synced = self._source_profile
            except Exception:
                pass

        msg = (f'已写入 {os.path.basename(POSES_PATH)}\n'
               f'跑步插值补全：{len(frames)} 帧\n'
               f'左墙姿势：已由右墙镜像生成')
        if synced:
            msg += f'\n\n已同步更新动作存档：{synced}（游戏无需重启即可生效）'
        else:
            msg += '\n\n重启桌宠后生效。'
        QMessageBox.information(self, '已保存', msg)

    def _load(self):
        if not os.path.exists(POSES_PATH):
            QMessageBox.information(self, '载入', '尚未找到 poses.json')
            return
        try:
            import io
            d = json.load(io.open(POSES_PATH, encoding='utf-8'))
        except Exception as e:
            QMessageBox.warning(self, '载入失败', str(e))
            return
        if d.get('run_start') and d.get('run_end'):
            self.slots['start'] = {k: tuple(v) for k, v in d['run_start'].items()}
            self.slots['end'] = {k: tuple(v) for k, v in d['run_end'].items()}
        elif d.get('run_frames'):
            n = len(d['run_frames'])
            self.slots['start'] = dict(d['run_frames'][0])
            self.slots['end'] = dict(d['run_frames'][n // 2])
        wr = d.get('wall_right') or d.get('wall')
        if wr:
            self.slots['wall'] = {k: tuple(v) for k, v in wr.items()}
        for key in ('idle', 'crouch', 'jump', 'dash_r', 'dash_up', 'dash_down'):
            if d.get(key):
                self.slots[key] = {k: tuple(v) for k, v in d[key].items()}
        self.refresh()
        QMessageBox.information(self, '载入', '已读取 poses.json 到各槽位')


def main():
    import ctypes
    try:
        ctypes.windll.shcore.SetProcessDpiAwareness(2)
    except Exception:
        pass
    app = QApplication(sys.argv)
    ed = PoseEditor()
    ed.show()
    sys.exit(app.exec_())


if __name__ == '__main__':
    main()