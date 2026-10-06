# SPDX-License-Identifier: GPL-2.0-or-later
"""BB Set Viewer - game-style navigation and camera control for Beta Builder sets.

Built for team members who are not Blender users. Two jobs:

  1. Walk  - a Minecraft-spectator flythrough. Mouse looks, WASD or the arrows move,
             Space/Ctrl rise and fall, Shift sprints. Movement is *state*
             based: you move while a key is held and stop the instant it is
             released. Blender's native fly mode is impulse based, which is
             why releasing W there does not stop you.

  2. Cameras - pick any camera in the set from a list, look through it, and
             adjust it from the panel (nudge, tilt, focal length, depth of
             field) without touching Blender's native transform tools.

  3. Artist Mode - a per-file kiosk. The viewport goes full screen, every
             other sidebar tab and header disappears, the set is locked
             against selection, and Blender's own shortcuts and mouse/trackpad
             navigation are switched off so nothing can be pressed by
             accident. Walk becomes the only way to move, so nothing drifts.
             Nothing is written to Blender's preferences: the blocking lives
             in add-on keymaps that only act while Artist Mode is on.

Cameras kept for reference (e.g. the art department's own) can be left out of
the viewer: give their collection the custom property bb_sv_hidden = True.
They stay in the file but never appear in the camera list and cannot be driven.

v2.4 (21 Sep 2026): hidden camera collections (bb_sv_hidden).
v2.5 (22 Sep 2026): Easy Mode; F starts walking again in Artist Mode (Blender reverses
     add-on keymap order, so the blockers now pass our own shortcuts through);
     mouse-look reads relative motion under a cursor grab, so it cannot spin by
     itself on scaled or external displays; Preview always uses the set's lights
     and world; focus points are parented to their cameras.
v2.5.1: Preview had NO lights in Artist/Easy Mode - the stripped view hid the
     'Light' object type, and in Preview a hidden light gives no light. Lights
     stay visible now; Easy Mode hides overlay extras instead (light and camera
     outlines) so the shot stays clean.
v2.5.2: one file carries both modes - switch between Easy and Artist Mode in one click
     (Easy: More > Switch to Artist Mode; Artist: Panel Setup > Switch to Easy Mode).
v2.6: Easy Mode gets the Fast / Preview look buttons.
v2.7: Wire look in both modes - a readable wireframe (a colour per object on a dark
     background, no X-ray), toggled off again back to the look it came from.
v2.8: Set Lights toggle in both modes - the set's own lights and world, or Blender's
     studio light. Saved with the file, and a mode switch no longer forces it back on.
v2.9 (30 Sep 2026): shortcuts in both modes - the arrow keys walk like WASD, C captures,
     and 1 to 6 are the focal lengths (18, 24, 35, 50, 85, 135 mm), including mid-walk.
v2.10 (2 Oct 2026): Capture Passes - one press of Capture (or C) saves the look, a blockout,
     an uncoloured pass, greyscale, wireframe and a real depth map, whichever are ticked.
     The depth map renders in EEVEE with the Z pass mapped to the set's own near and far
     (so the sky cannot flatten it) through a colour ramp, saved with the view transform
     forced to Standard - a film curve turns white into 0.77 and is why depth maps come out
     grey and flat. Clear All Cameras. Render-based captures force EEVEE: no Cycles.
v2.11 (2 Oct 2026): the depth map uses Normalize, so it fits whatever the camera is looking at
     with nothing to set (the one catch: in an open shot the sky takes the far end). The
     'uncoloured' pass became a proper LINE ART pass - white paper, cavity and object outlines
     turned up, drawn at 2x resolution, then stretched to black ink on white paper. Straight
     out of the viewport it is grey on grey: paper 0.73, darkest lines 0.46, nothing above
     0.73. After the stretch: paper 0.96, lines 0.06.
v2.12 (2 Oct 2026): the wireframe pass is gone - line art is what it was wanted for, and two
     similar-sounding passes only cause confusion.
v2.13 (2 Oct 2026, not published - a working build): the panels were rebuilt. Two mode buttons
     at the top, one Shot panel (walk + speed, the three looks, capture and its passes),
     Cameras on its own, Lens/Focus/Tilt merged into Camera Settings, and everything you set
     once moved into a closed Settings panel. The looks are now Fast (solid), Preview (material)
     and Render (EEVEE with ray tracing, always using the set's own lights); the wire button is
     gone. Line art went back to the settings that actually produced a drawing - flat single
     colour and nothing else, with the contrast fixed on the saved image afterwards, never in
     Blender.
v2.14 (3 Oct 2026, working build): six looks instead of three, from the viewport settings Aman
     settled on by hand - Fast, Clay, Line Art, Flat Colour, Preview, Render - with one table
     driving both the view buttons and the capture passes so they cannot drift. Easy Mode shows
     the same looks and captures only what is on screen, with its own Depth Map button. Camera
     Settings keeps roll and Reset Horizon only; depth of field is greyed out rather than
     hidden. A mini map of the set draws in the corner of the viewport in Artist Mode, with the
     cameras on it and where you are standing.
v2.15 (3 Oct 2026): Easy Mode gets two depth buttons under the looks - Generate Separate Depth
     Map, and Multiply with Depth Map, which captures the view and multiplies it by its own
     depth so a drawing gains the distance it cannot show on its own. Both are offered only for
     Clay, Line Art and Flat Colour.
v2.16 (3 Oct 2026): both modes open in Fast, not Preview. Material Preview compiles a shader
     per material before it draws anything, which on a heavy set is a long freeze that looks
     like a crash - and on a 26 million triangle set can be one.
v2.17 (3 Oct 2026): a Play button in both modes, for mocap takes and anything else keyframed.
     Both modes hide Blender's timeline, so there was no way to start playback from inside
     them. It appears only when the scene has something animated.

  4. Easy Mode - one panel, one camera. The viewport IS the camera: Walk moves
             it, sliders set focal length, focus distance, depth of field and
             f-stop, and Capture saves the picture plus the camera settings
             (a JSON file beside the image) so the shot can be rebuilt later.

Drop this file in your addons folder and enable "BB Set Viewer".
Panel lives in the 3D view sidebar (press N) under the "BB Set" tab.
"""

import json
import math
import os
import re
import subprocess
import sys
import time

import blf
import bpy
from bpy.app.handlers import persistent
from bpy.props import (
    BoolProperty,
    EnumProperty,
    FloatProperty,
    IntProperty,
    PointerProperty,
    StringProperty,
)
from bpy.types import Operator, Panel, PropertyGroup
from mathutils import Euler, Matrix, Vector

bl_info = {
    "name": "BB Set Viewer",
    "author": "Beta Builder",
    "version": (2, 21, 0),
    "blender": (4, 2, 0),
    "location": "View3D > Sidebar (N) > BB Set",
    "description": "Game-style WASD navigation and panel-driven camera control",
    "category": "3D View",
}

# Pitch is measured so that 90 degrees is the horizon, 0 is straight down and
# 180 is straight up. Stop just short of both poles or the view rolls over.
PITCH_MIN = math.radians(0.5)
PITCH_MAX = math.radians(179.5)

MOVE_KEYS = {
    "W": Vector((0.0, 0.0, -1.0)),   # forward, along the level heading
    "S": Vector((0.0, 0.0, 1.0)),
    "A": Vector((-1.0, 0.0, 0.0)),
    "D": Vector((1.0, 0.0, 0.0)),
    # the arrow keys do exactly what WASD does, for anyone who reaches for them
    "UP_ARROW": Vector((0.0, 0.0, -1.0)),
    "DOWN_ARROW": Vector((0.0, 0.0, 1.0)),
    "LEFT_ARROW": Vector((-1.0, 0.0, 0.0)),
    "RIGHT_ARROW": Vector((1.0, 0.0, 0.0)),
}
# W A S D stay on the floor plane; height changes only with Space (up) and
# Ctrl (down), so looking down and pressing W never sinks you into the floor.
UP_KEYS = {"SPACE"}


def _rot_from_angles(pitch, yaw):
    return Euler((pitch, 0.0, yaw), "XYZ").to_quaternion()


def _angles_from_rot(quat):
    e = quat.to_euler("XYZ")
    return e.x, e.z


def _focus_get(self):
    """Distance from the active camera to its focus point, along the camera's view line."""
    cam = self.id_data.camera
    if cam is None or cam.type != "CAMERA":
        return 0.0
    focus = cam.data.dof.focus_object
    if focus is None:
        return cam.data.dof.focus_distance
    if focus.parent is cam:
        # the point lives in the camera's own space: straight ahead is -Z.
        # Read location, not matrix_world, which lags a slider drag by one update.
        return max(0.0, -(focus.matrix_parent_inverse @ focus.location).z)
    forward = cam.matrix_world.to_quaternion() @ Vector((0.0, 0.0, -1.0))
    return max(0.0, (focus.matrix_world.translation - cam.matrix_world.translation).dot(forward))


def _focus_set(self, value):
    cam = self.id_data.camera
    if cam is None or cam.type != "CAMERA" or _is_locked(cam):
        return
    focus = cam.data.dof.focus_object
    if focus is None:
        cam.data.dof.focus_distance = value
        return
    _parent_focus(cam)
    local = focus.matrix_parent_inverse @ focus.location
    local.z = -max(0.1, value)
    focus.location = focus.matrix_parent_inverse.inverted_safe() @ local


def _parent_focus(cam):
    """Make the camera's focus point its child, keeping it where it is, so it travels with
    the camera. Files made before v2.5 have loose focus points; they are fixed on load."""
    focus = cam.data.dof.focus_object
    if focus is None or focus.parent is cam:
        return
    world = focus.matrix_world.copy()
    focus.parent = cam
    focus.matrix_parent_inverse.identity()
    focus.matrix_world = world


def _cam_data(self):
    cam = self.id_data.camera
    return cam.data if cam is not None and cam.type == "CAMERA" else None


def _lens_get(self):
    d = _cam_data(self)
    return d.lens if d else 35.0


def _lens_set(self, v):
    d = _cam_data(self)
    if d:
        d.lens = v


def _dof_get(self):
    d = _cam_data(self)
    return bool(d and d.dof.use_dof)


def _dof_set(self, v):
    d = _cam_data(self)
    if d:
        d.dof.use_dof = v


def _fstop_get(self):
    d = _cam_data(self)
    return d.dof.aperture_fstop if d else 2.8


def _fstop_set(self, v):
    d = _cam_data(self)
    if d:
        d.dof.aperture_fstop = v


def _lights_update(self, context):
    """Push the toggle out to every 3D view showing this scene, so the viewport agrees with
    the button whichever mode we are in."""
    for window in context.window_manager.windows:
        if window.scene is not self.id_data:
            continue
        for area in window.screen.areas:
            if area.type == "VIEW_3D":
                _scene_lighting(area.spaces.active.shading, self.scene_lights)


class BBSV_Props(PropertyGroup):
    speed: FloatProperty(
        name="Speed",
        description="Walking speed in metres per second",
        default=4.0, min=0.1, max=100.0, soft_max=30.0, unit="VELOCITY",
    )
    sprint: FloatProperty(
        name="Sprint",
        description="Speed multiplier while Shift is held",
        default=3.0, min=1.0, max=20.0,
    )
    sensitivity: FloatProperty(
        name="Mouse",
        description="Mouse look sensitivity",
        default=1.0, min=0.05, max=5.0,
    )
    invert_y: BoolProperty(
        name="Invert Y", description="Invert vertical mouse look", default=False,
    )
    eye_height: FloatProperty(
        name="Eye Height",
        description="Height above the floor used by Stand On Floor",
        default=1.65, min=0.1, max=5.0, subtype="DISTANCE",
    )
    fly_target: EnumProperty(
        name="Move",
        description="What the flythrough moves",
        items=[
            ("AUTO", "Auto", "Move the camera when looking through one, otherwise the free view"),
            ("VIEW", "Free View", "Fly the viewport, leaving all cameras untouched"),
            ("CAMERA", "Camera", "Fly the active camera itself"),
        ],
        default="AUTO",
    )
    artist_mode: BoolProperty(
        name="Artist Mode",
        description="Saved with the file: when on, the file opens straight into Artist Mode",
        default=False,
    )
    easy_mode: BoolProperty(
        name="Easy Mode",
        description="Saved with the file: when on, the file opens in Easy Mode - one panel, the view is the camera",
        default=False,
    )
    # The checklist: which sections an artist sees
    show_capture: BoolProperty(name="Capture", default=True)
    show_walk: BoolProperty(name="Walk", default=True)
    show_cameras: BoolProperty(name="Cameras", default=True)
    show_adjust: BoolProperty(name="Move Camera", default=True)
    show_lens: BoolProperty(name="Lens", default=True)
    show_dof: BoolProperty(name="Focus & Depth of Field", default=True)
    show_frame: BoolProperty(name="Framing", default=True)
    show_parts: BoolProperty(name="Show / Hide Set Parts", default=True)
    show_look: BoolProperty(name="Look", default=True)
    scene_lights: BoolProperty(
        name="Set Lights",
        description="Light Preview with the set's own lights and world. Turn it off for "
                    "Blender's studio light, which lights everything evenly and ignores the set",
        default=True, update=_lights_update,
    )
    active_cam: StringProperty(name="Camera", default="")
    focus_on_add: BoolProperty(
        name="With Focus Point",
        description="New cameras get a focus point where they look, used as the depth-of-field target",
        default=True,
    )
    nudge: FloatProperty(
        name="Step", description="Distance each nudge button moves the camera",
        default=0.25, min=0.001, max=10.0, subtype="DISTANCE",
    )
    tilt: FloatProperty(
        name="Tilt Step", description="Angle each tilt button rotates the camera",
        default=5.0, min=0.1, max=45.0,
    )
    focus_pull: FloatProperty(
        name="Focus Distance",
        description="Slide the focus point nearer or further along the camera's view line",
        get=_focus_get, set=_focus_set,
        min=0.1, soft_min=0.1, soft_max=30.0, subtype="DISTANCE", precision=2,
    )
    # Easy Mode sliders: bounded ranges so a slider drag stays in useful territory
    lens_slider: FloatProperty(
        name="Focal Length", description="Wide (small numbers) to tele (big numbers)",
        get=_lens_get, set=_lens_set, min=10.0, max=200.0, soft_min=12.0, soft_max=135.0,
        precision=0, unit="CAMERA",
    )
    dof_toggle: BoolProperty(
        name="Depth of Field", description="Blur what is nearer or further than the focus distance",
        get=_dof_get, set=_dof_set,
    )
    # Capture passes: one press of Capture (or C) saves every pass that is ticked.
    look_now: StringProperty(default="FAST", options={"HIDDEN"})
    capture_size: EnumProperty(
        name="Capture Size",
        description="How big the saved pictures are. The frame shape is set separately",
        items=[("1K", "1K", "1920 px on the long edge"),
               ("2K", "2K", "2560 px on the long edge - the default"),
               ("4K", "4K", "3840 px on the long edge - slower, and four times the file size")],
        default="2K",
        update=lambda self, ctx: _apply_capture_size(ctx.scene),
    )
    show_minimap: BoolProperty(
        name="Mini Map", default=False,
        description="A plan of the set in the corner of the viewport, with the cameras on it "
                    "and where you are standing",
        update=lambda self, ctx: _map_enable(self.show_minimap),
    )
    pass_look: BoolProperty(name="Current View", default=True,
                            description="Whatever is on screen right now")
    pass_FAST: BoolProperty(name="Fast", default=False, description="Solid view with the studio light")
    pass_CLAY: BoolProperty(name="Clay", default=False, description="One clay colour, soft studio light")
    pass_LINE: BoolProperty(name="Line Art", default=False,
                            description="A line drawing, saved at a higher resolution")
    pass_COLOUR: BoolProperty(name="Flat Colour", default=False,
                              description="Flat material colours with black outlines")
    pass_PREVIEW: BoolProperty(name="Preview", default=False, description="Material preview")
    pass_grey: BoolProperty(name="Greyscale", default=False,
                            description="The current view with the colour taken out")
    pass_depth: BoolProperty(name="Depth Map", default=False,
                             description="A real depth map. This renders the frame in EEVEE, "
                                         "so it takes a few seconds")
    depth_near_white: BoolProperty(
        name="Near is White", default=True,
        description="White nearest the camera, black furthest away. Off flips it",
    )
    fstop_slider: FloatProperty(
        name="F-Stop", description="Smaller = more blur outside the focus distance",
        get=_fstop_get, set=_fstop_set, min=0.7, max=32.0, soft_min=0.95, soft_max=16.0, precision=1,
    )


_WALK = {"on": False, "camera": False}


def _is_locked(cam):
    return bool(cam and cam.get("bb_locked"))


HIDDEN_KEY = "bb_sv_hidden"      # collection property: its cameras stay out of the viewer


def _is_hidden(cam):
    return any(c.get(HIDDEN_KEY) for c in cam.users_collection)


def _viewer_cams(scene):
    """The cameras the viewer shows and drives, in name order."""
    return sorted((o for o in scene.objects if o.type == "CAMERA" and not _is_hidden(o)),
                  key=lambda o: o.name)


def _set_locked(cam, state):
    """Lock a camera down: our controls refuse to move it and Blender's own
    transform locks are set too, so it cannot be dragged either."""
    cam["bb_locked"] = bool(state)
    cam.lock_location = (state,) * 3
    cam.lock_rotation = (state,) * 3
    focus = cam.data.dof.focus_object
    if focus is not None:
        focus.lock_location = (state,) * 3


def _refuse_if_locked(op, cam):
    if _is_locked(cam):
        op.report({"WARNING"}, "%s is locked - click its padlock to unlock it" % cam.name)
        return True
    return False


class BBSV_OT_flythrough(Operator):
    """Walk through the set. Mouse looks, WASD moves, Space/Ctrl up and down, Shift sprints, Esc exits"""

    bl_idname = "bb_sv.flythrough"
    bl_label = "Walk Through Set"
    # GRAB_CURSOR: Blender holds and wraps the pointer itself and reports smooth relative
    # motion. Warping the pointer back to the centre by hand drifted on scaled displays:
    # the warp landed a few pixels off, every event read as movement and the view spun.
    bl_options = {"REGISTER", "UNDO", "GRAB_CURSOR", "BLOCKING"}

    @classmethod
    def poll(cls, context):
        return context.area is not None and context.area.type == "VIEW_3D"

    # -- target abstraction: the same modal flies the viewport or a camera ----
    def _read_target(self, context):
        if self.target == "CAMERA" and self.cam:
            m = self.cam.matrix_world
            quat = m.to_quaternion()
            return m.translation.copy(), quat
        rv3d = self.rv3d
        quat = rv3d.view_rotation.copy()
        eye = rv3d.view_location + quat @ Vector((0.0, 0.0, rv3d.view_distance))
        return eye, quat

    def _write_target(self, eye, quat):
        if self.target == "CAMERA" and self.cam:
            self.cam.rotation_mode = "XYZ"
            self.cam.location = eye
            self.cam.rotation_euler = quat.to_euler("XYZ")
            return
        rv3d = self.rv3d
        rv3d.view_rotation = quat
        # Keep the eye where we put it: view_location is the orbit pivot, which
        # sits view_distance *behind* the eye along the view axis.
        rv3d.view_location = eye - quat @ Vector((0.0, 0.0, rv3d.view_distance))

    def invoke(self, context, event):
        props = context.scene.bb_sv
        self.props = props
        self.target = props.fly_target
        if self.target == "AUTO":
            looking_through = context.area.spaces.active.region_3d.view_perspective == "CAMERA"
            self.target = "CAMERA" if looking_through and _active_cam(context) else "VIEW"
        self.cam = _active_cam(context) if self.target == "CAMERA" else None
        if self.target == "CAMERA" and self.cam is None:
            self.report({"WARNING"}, "No active camera to fly - set one in the Cameras panel")
            return {"CANCELLED"}

        self.area = context.area
        self.region = next(r for r in self.area.regions if r.type == "WINDOW")
        self.rv3d = self.area.spaces.active.region_3d   # works from the sidebar button too

        # A locked camera stays put: walk the free view, starting where it stands.
        if self.target == "CAMERA" and _is_locked(self.cam):
            m = self.cam.matrix_world
            quat = m.to_quaternion()
            self.rv3d.view_perspective = "PERSP"
            self.rv3d.view_rotation = quat
            self.rv3d.view_location = m.translation - quat @ Vector((0.0, 0.0, self.rv3d.view_distance))
            self.report({"INFO"}, "%s is locked - walking freely. Unlock it to move it." % self.cam.name)
            self.target, self.cam = "VIEW", None

        # A camera-locked viewport cannot be flown; drop to perspective first.
        self.restore_persp = None
        if self.target == "VIEW" and self.rv3d.view_perspective == "CAMERA":
            self.restore_persp = "CAMERA"
            self.rv3d.view_perspective = "PERSP"

        eye, quat = self._read_target(context)
        self.pitch, self.yaw = _angles_from_rot(quat)
        self.pitch = max(PITCH_MIN, min(PITCH_MAX, self.pitch))
        self.eye = eye
        self.start_eye, self.start_quat = eye.copy(), quat.copy()

        self.held = set()
        self.last_t = time.perf_counter()
        self.easy = _ARTIST.get("easy", False)

        # Without Blender's continuous grab (a preference), park the pointer mid-view
        # and re-centre it near the edges, ignoring the jump each re-centre causes.
        self.wrap = not context.preferences.inputs.use_mouse_continuous
        self.cx = self.region.x + self.region.width // 2
        self.cy = self.region.y + self.region.height // 2
        self.skip = 0
        self.mx, self.my = event.mouse_x, event.mouse_y      # last pointer position seen
        if self.wrap:
            context.window.cursor_warp(self.cx, self.cy)
            self.skip = 2
        context.window.cursor_modal_set("NONE")

        self._timer = context.window_manager.event_timer_add(1 / 60, window=context.window)
        context.window_manager.modal_handler_add(self)
        self._set_header()
        _WALK["on"] = True
        _WALK["camera"] = self.target == "CAMERA"
        return {"RUNNING_MODAL"}

    def _set_header(self):
        cam = _active_cam(bpy.context)
        lens = "   %d mm (1-6)" % round(cam.data.lens) if cam is not None else ""
        self.area.header_text_set(
            "Walk:  WASD or arrows move   Space up   Ctrl down   Shift sprint%s   "
            "Wheel speed %.1f m/s   F or Esc finish   Enter finish + lock   Right-click undo"
            % (lens, self.props.speed)
        )

    def _finish(self, context, cancel=False, lock=False):
        _WALK["on"] = False
        if lock and self.target == "CAMERA" and self.cam:
            _set_locked(self.cam, True)
            self.report({"INFO"}, "%s locked" % self.cam.name)
        context.window_manager.event_timer_remove(self._timer)
        context.window.cursor_modal_restore()
        self.area.header_text_set(None)
        if cancel:
            self._write_target(self.start_eye, self.start_quat)
            # Cancelling should leave the viewport exactly as it was found,
            # including a camera lock we dropped on the way in.
            if self.restore_persp == "CAMERA":
                self.rv3d.view_perspective = "CAMERA"
        context.area.tag_redraw()
        return {"CANCELLED"} if cancel else {"FINISHED"}

    def modal(self, context, event):
        # Enter: the shot is set - finish and lock the camera it was driving.
        if event.type in {"RET", "NUMPAD_ENTER"} and event.value == "PRESS":
            return self._finish(context, lock=not self.easy)
        # F toggles walking off again; Esc stays as the familiar backup.
        if event.value == "PRESS" and (event.type == "ESC" or (event.type == "F" and not event.is_repeat)):
            return self._finish(context)
        if event.type == "RIGHTMOUSE" and event.value == "PRESS":
            return self._finish(context, cancel=True)

        # 1-6 change the lens without leaving the walk, so the shot can be framed
        # while moving. The modal sees keys before any keymap does.
        if event.value == "PRESS" and event.type in LENS_BY_KEY:
            cam = _active_cam(context)
            if cam is not None and not _is_locked(cam):
                cam.data.lens = LENS_BY_KEY[event.type]
                self._set_header()
            return {"RUNNING_MODAL"}

        # Speed on the wheel, so the same controls suit a desk and a stadium.
        if event.type == "WHEELUPMOUSE":
            self.props.speed = min(100.0, self.props.speed * 1.25)
            self._set_header()
            return {"RUNNING_MODAL"}
        if event.type == "WHEELDOWNMOUSE":
            self.props.speed = max(0.1, self.props.speed / 1.25)
            self._set_header()
            return {"RUNNING_MODAL"}

        # A key released while Blender is not the front window never sends a
        # release event; forget everything held rather than keep moving.
        if event.type == "WINDOW_DEACTIVATE":
            self.held.clear()
            return {"RUNNING_MODAL"}
        # macOS sends no key release while Cmd is down, so a key let go during a
        # Cmd shortcut would stay 'held' and keep walking. Cmd resets the keys.
        if event.type in {"OSKEY", "LEFT_CMD", "RIGHT_CMD"} or event.oskey:
            self.held.clear()

        # --- the fix for native fly mode: track press and release as state ---
        if event.value == "PRESS":
            self.held.add(event.type)
        elif event.value == "RELEASE":
            self.held.discard(event.type)

        if event.type in {"MOUSEMOVE", "INBETWEEN_MOUSEMOVE"}:
            dx, dy = event.mouse_x - self.mx, event.mouse_y - self.my
            self.mx, self.my = event.mouse_x, event.mouse_y
            if self.skip:
                self.skip -= 1
                dx = dy = 0
            if dx or dy:
                s = self.props.sensitivity * 0.0025
                self.yaw -= dx * s
                self.pitch += (dy * s) * (-1.0 if self.props.invert_y else 1.0)
                self.pitch = max(PITCH_MIN, min(PITCH_MAX, self.pitch))
                # Rotate about the eye, not the orbit pivot, or looking around
                # swings you through the room.
                self._write_target(self.eye, _rot_from_angles(self.pitch, self.yaw))
            if self.wrap:
                r = self.region
                if not (r.x + r.width * 0.2 < event.mouse_x < r.x + r.width * 0.8
                        and r.y + r.height * 0.2 < event.mouse_y < r.y + r.height * 0.8):
                    context.window.cursor_warp(self.cx, self.cy)
                    self.mx, self.my = self.cx, self.cy
                    self.skip = 1
            return {"RUNNING_MODAL"}

        if event.type == "TIMER":
            now = time.perf_counter()
            dt = min(now - self.last_t, 0.1)   # clamp so a stall cannot teleport you
            self.last_t = now

            quat = _rot_from_angles(self.pitch, self.yaw)
            level = _rot_from_angles(math.radians(90.0), self.yaw)   # same heading, no pitch
            move = Vector((0.0, 0.0, 0.0))
            for key, axis in MOVE_KEYS.items():
                if key in self.held:
                    move += level @ axis

            # Up and down stay world-relative, so Space rises even when you are
            # looking at the floor. Ctrl comes from the live modifier state,
            # which is steadier than tracking left and right Ctrl separately.
            up = 0.0
            if self.held & UP_KEYS:
                up += 1.0
            if event.ctrl:
                up -= 1.0
            move.z += up

            if move.length_squared:
                speed = self.props.speed * (self.props.sprint if event.shift else 1.0)
                self.eye = self.eye + move.normalized() * speed * dt
                self._write_target(self.eye, quat)
                context.area.tag_redraw()
            return {"RUNNING_MODAL"}

        return {"RUNNING_MODAL"}


class BBSV_OT_look_through(Operator):
    """Make this the active camera and look through it"""

    bl_idname = "bb_sv.look_through"
    bl_label = "Look Through"
    bl_options = {"REGISTER", "UNDO"}

    name: StringProperty()

    def execute(self, context):
        cam = context.scene.objects.get(self.name)
        if cam is None or cam.type != "CAMERA" or _is_hidden(cam):
            self.report({"WARNING"}, "Camera not found: %s" % self.name)
            return {"CANCELLED"}
        context.scene.camera = cam
        context.scene.bb_sv.active_cam = cam.name
        for area in context.screen.areas:
            if area.type == "VIEW_3D":
                area.spaces.active.region_3d.view_perspective = "CAMERA"
        return {"FINISHED"}


class BBSV_OT_nudge(Operator):
    """Move or tilt the active camera by one step"""

    bl_idname = "bb_sv.nudge"
    bl_label = "Nudge Camera"
    bl_options = {"REGISTER", "UNDO"}

    axis: StringProperty()
    amount: FloatProperty(default=1.0)
    kind: StringProperty(default="MOVE")

    def execute(self, context):
        cam = _active_cam(context)
        if cam is None:
            self.report({"WARNING"}, "No active camera")
            return {"CANCELLED"}
        if _refuse_if_locked(self, cam):
            return {"CANCELLED"}
        p = context.scene.bb_sv
        if self.kind == "MOVE":
            step = p.nudge * self.amount
            if self.axis == "WORLD_Z":
                cam.location.z += step
            else:
                local = {"X": Vector((1, 0, 0)),
                         "Y": Vector((0, 1, 0)),
                         "Z": Vector((0, 0, 1))}[self.axis]
                cam.location += cam.matrix_world.to_quaternion() @ local * step
        else:
            cam.rotation_mode = "XYZ"
            step = math.radians(p.tilt) * self.amount
            idx = {"X": 0, "Y": 1, "Z": 2}[self.axis]
            if self.axis == "Z":
                cam.rotation_euler[2] += step          # pan, around world up
            else:
                cam.rotation_euler[idx] += step        # tilt / roll, camera local
        return {"FINISHED"}


CAMERA_COLLECTION = "Cameras"
FOCUS_SUFFIX = " Focus"
FOCUS_FALLBACK_DISTANCE = 3.0   # metres, when the camera looks at nothing


def _camera_collection(scene):
    col = bpy.data.collections.get(CAMERA_COLLECTION)
    if col is None:
        col = bpy.data.collections.new(CAMERA_COLLECTION)
    if col.name not in scene.collection.children:
        scene.collection.children.link(col)
    return col


def _next_camera_name(scene):
    used = {o.name for o in bpy.data.objects}
    i = 1
    while "BB Cam %02d" % i in used:
        i += 1
    return "BB Cam %02d" % i


def _aim_point(context, cam):
    """Where the camera's centre line first meets geometry, or a fallback distance."""
    origin = cam.matrix_world.translation
    forward = cam.matrix_world.to_quaternion() @ Vector((0.0, 0.0, -1.0))
    deps = context.evaluated_depsgraph_get()
    hit, loc, *_ = context.scene.ray_cast(deps, origin + forward * 0.05, forward)
    return loc if hit else origin + forward * FOCUS_FALLBACK_DISTANCE


def _ensure_focus_point(context, cam):
    """Give the camera its own focus empty and make it the depth-of-field target.

    The empty is what the lens focuses on, so anyone changing the f-stop gets
    a sharp subject rather than Blender's default focus distance.
    """
    focus = cam.data.dof.focus_object
    if focus is None:
        focus = bpy.data.objects.new(cam.name + FOCUS_SUFFIX, None)
        focus.empty_display_type = "SPHERE"
        focus.empty_display_size = 0.08
        focus.show_in_front = True
        for col in cam.users_collection:
            col.objects.link(focus)
        focus.parent = cam                   # moves with the camera
        focus.location = cam.matrix_world.inverted_safe() @ _aim_point(context, cam)
        cam.data.dof.focus_object = focus
    else:
        _parent_focus(cam)
    return focus


class BBSV_OT_add_camera(Operator):
    """Add a camera at the current viewpoint"""

    bl_idname = "bb_sv.add_camera"
    bl_label = "Add Camera Here"
    bl_options = {"REGISTER", "UNDO"}

    add_focus: BoolProperty(
        name="Add Focus Point",
        description="Also place a focus point where the camera is looking, used as the depth-of-field target",
        default=True,
    )

    def execute(self, context):
        area = next((a for a in context.screen.areas if a.type == "VIEW_3D"), None)
        if area is None:
            return {"CANCELLED"}
        rv3d = area.spaces.active.region_3d
        quat = rv3d.view_rotation.copy()
        eye = rv3d.view_location + quat @ Vector((0.0, 0.0, rv3d.view_distance))
        name = _next_camera_name(context.scene)
        data = bpy.data.cameras.new(name)
        obj = bpy.data.objects.new(name, data)
        _camera_collection(context.scene).objects.link(obj)
        obj.location = eye
        obj.rotation_mode = "XYZ"
        obj.rotation_euler = quat.to_euler("XYZ")
        context.view_layer.update()
        if self.add_focus:
            _ensure_focus_point(context, obj)
        context.scene.camera = obj
        context.scene.bb_sv.active_cam = obj.name
        self.report({"INFO"}, "Added %s%s" % (obj.name, " with focus point" if self.add_focus else ""))
        return {"FINISHED"}


class BBSV_OT_add_focus(Operator):
    """Give the active camera a focus point where it is looking"""

    bl_idname = "bb_sv.add_focus"
    bl_label = "Add Focus Point"
    bl_options = {"REGISTER", "UNDO"}

    def execute(self, context):
        cam = _active_cam(context)
        if cam is None:
            self.report({"WARNING"}, "No active camera")
            return {"CANCELLED"}
        if _refuse_if_locked(self, cam):
            return {"CANCELLED"}
        _ensure_focus_point(context, cam)
        return {"FINISHED"}


class BBSV_OT_focus_here(Operator):
    """Move the focus point to whatever sits in the centre of the frame"""

    bl_idname = "bb_sv.focus_here"
    bl_label = "Focus On Centre Of Frame"
    bl_options = {"REGISTER", "UNDO"}

    def execute(self, context):
        cam = _active_cam(context)
        if cam is None or _refuse_if_locked(self, cam):
            return {"CANCELLED"}
        focus = _ensure_focus_point(context, cam)
        focus.matrix_world = Matrix.Translation(_aim_point(context, cam))
        return {"FINISHED"}


class BBSV_OT_stand_on_floor(Operator):
    """Drop the viewpoint to standing height above whatever is below it"""

    bl_idname = "bb_sv.stand_on_floor"
    bl_label = "Stand On Floor"
    bl_options = {"REGISTER", "UNDO"}

    def execute(self, context):
        area = next((a for a in context.screen.areas if a.type == "VIEW_3D"), None)
        if area is None:
            return {"CANCELLED"}
        rv3d = area.spaces.active.region_3d
        cam = _active_cam(context) if rv3d.view_perspective == "CAMERA" else None
        if cam and _refuse_if_locked(self, cam):
            return {"CANCELLED"}
        if cam:
            eye = cam.matrix_world.translation.copy()
        else:
            quat = rv3d.view_rotation.copy()
            eye = rv3d.view_location + quat @ Vector((0.0, 0.0, rv3d.view_distance))
        deps = context.evaluated_depsgraph_get()
        hit, loc, *_ = context.scene.ray_cast(deps, eye, Vector((0, 0, -1)))
        if not hit:
            self.report({"WARNING"}, "Nothing below the viewpoint to stand on")
            return {"CANCELLED"}
        target = Vector((eye.x, eye.y, loc.z + context.scene.bb_sv.eye_height))
        if cam:
            cam.location = target      # camera has no parent in this workflow
        else:
            rv3d.view_location = target - quat @ Vector((0.0, 0.0, rv3d.view_distance))
        return {"FINISHED"}


# ---------------------------------------------------------------------------
# Small camera helpers
# ---------------------------------------------------------------------------

LENS_PRESETS = (18, 24, 35, 50, 85, 135)
# The number keys pick those presets in order: 1 is 18 mm, 6 is 135 mm. Numpad too,
# so a keyboard with a numpad works either way.
LENS_BY_KEY = dict(zip(("ONE", "TWO", "THREE", "FOUR", "FIVE", "SIX"), LENS_PRESETS))
LENS_BY_KEY.update(zip(("NUMPAD_%d" % i for i in range(1, len(LENS_PRESETS) + 1)), LENS_PRESETS))
# Capture size, as the long edge in pixels. The frame SHAPE is chosen separately (ASPECTS);
# this only decides how many pixels that shape is rendered at, so the two never fight.
CAPTURE_SIZES = (("1K", 1920), ("2K", 2560), ("4K", 3840))
CAPTURE_LONG_EDGE = dict(CAPTURE_SIZES)


def _apply_capture_size(scene):
    """Rescale the render to the chosen size, keeping whatever frame shape is set."""
    r = scene.render
    w, h = max(1, r.resolution_x), max(1, r.resolution_y)
    long_edge = CAPTURE_LONG_EDGE.get(scene.bb_sv.capture_size, 2560)
    scale = long_edge / float(max(w, h))
    r.resolution_x = max(2, int(round(w * scale / 2.0)) * 2)      # even numbers encode cleanly
    r.resolution_y = max(2, int(round(h * scale / 2.0)) * 2)
    r.resolution_percentage = 100


ASPECTS = (  # label, width, height - the SHAPE; the size above decides the pixels
    ("16:9", 1920, 1080),
    ("2.39:1", 1920, 804),
    ("9:16", 1080, 1920),
    ("4:5", 1080, 1350),
    ("1:1", 1080, 1080),
)


def _view3d_area(context):
    areas = [a for a in context.screen.areas if a.type == "VIEW_3D"]
    return max(areas, key=lambda a: a.width * a.height) if areas else None


def _active_cam(context):
    cam = context.scene.camera
    return cam if cam and cam.type == "CAMERA" and not _is_hidden(cam) else None


class BBSV_OT_set_lens(Operator):
    """Set the active camera's focal length"""

    bl_idname = "bb_sv.set_lens"
    bl_label = "Set Lens"
    bl_options = {"REGISTER", "UNDO"}

    mm: FloatProperty()

    def execute(self, context):
        cam = _active_cam(context)
        if not cam or _refuse_if_locked(self, cam):
            return {"CANCELLED"}
        cam.data.lens = self.mm
        return {"FINISHED"}


class BBSV_OT_set_aspect(Operator):
    """Set the frame shape used by every camera"""

    bl_idname = "bb_sv.set_aspect"
    bl_label = "Set Frame Shape"
    bl_options = {"REGISTER", "UNDO"}

    width: bpy.props.IntProperty()
    height: bpy.props.IntProperty()

    def execute(self, context):
        r = context.scene.render
        r.resolution_x, r.resolution_y, r.resolution_percentage = self.width, self.height, 100
        _apply_capture_size(context.scene)       # the shape changed, the size stays as chosen
        return {"FINISHED"}


class BBSV_OT_level_horizon(Operator):
    """Remove any roll so the horizon is level"""

    bl_idname = "bb_sv.level_horizon"
    bl_label = "Level Horizon"
    bl_options = {"REGISTER", "UNDO"}

    def execute(self, context):
        cam = _active_cam(context)
        if not cam or _refuse_if_locked(self, cam):
            return {"CANCELLED"}
        cam.rotation_mode = "XYZ"
        cam.rotation_euler[1] = 0.0
        return {"FINISHED"}


class BBSV_OT_camera_view(Operator):
    """Switch between looking through the active camera and the free view"""

    bl_idname = "bb_sv.camera_view"
    bl_label = "Camera View"
    bl_options = {"REGISTER"}

    def execute(self, context):
        area = _view3d_area(context)
        if area is None or not _active_cam(context):
            return {"CANCELLED"}
        rv3d = area.spaces.active.region_3d
        rv3d.view_perspective = "PERSP" if rv3d.view_perspective == "CAMERA" else "CAMERA"
        return {"FINISHED"}


class BBSV_OT_set_look(Operator):
    """Change how the set is drawn on screen"""

    bl_idname = "bb_sv.set_look"
    bl_label = "Set Look"
    bl_options = {"REGISTER"}

    mode: StringProperty()

    def execute(self, context):
        area = _view3d_area(context)
        if area is None:
            return {"CANCELLED"}
        p = context.scene.bb_sv
        sh = area.spaces.active.shading
        _apply_look(sh, self.mode, context.scene)
        _plain_background(sh)
        if self.mode == "RENDER":
            _force_eevee(context.scene)       # no Cycles in this workflow
            _scene_lighting(sh, True)         # a render view on the studio light is pointless
        else:
            _scene_lighting(sh, p.scene_lights)
        p.look_now = self.mode
        return {"FINISHED"}


def _enum_ok(owner, prop, value):
    """True if this Blender build offers that enum value (identifiers move between versions)."""
    try:
        return value in {i.identifier for i in owner.bl_rna.properties[prop].enum_items}
    except Exception:
        return False


def _plain_background(shading):
    if _enum_ok(shading, "background_type", "THEME"):
        shading.background_type = "THEME"


def _scene_lighting(shading, on=True):
    """Preview (and Rendered) use the set's own lights and world, not Blender's studio
    preview - otherwise the lighting the set was built with never shows. Off is the Set
    Lights toggle: Blender's studio light, for reading shapes in an unlit set."""
    for attr in ("use_scene_lights", "use_scene_world", "use_scene_lights_render", "use_scene_world_render"):
        if hasattr(shading, attr):
            setattr(shading, attr, on)


def _layer_coll(lc, name):
    if lc.collection.name == name:
        return lc
    for ch in lc.children:
        hit = _layer_coll(ch, name)
        if hit:
            return hit
    return None


def _set_parts(scene):
    """Top-level collections an artist may show or hide, with their children."""
    # cameras are managed in their own panel; the lighting rig is the supervisor's
    return [c for c in scene.collection.children
            if not c.name.startswith(("_", "00 ")) and c.name != CAMERA_COLLECTION]


class BBSV_OT_toggle_part(Operator):
    """Show or hide this part of the set, in the view and in renders"""

    bl_idname = "bb_sv.toggle_part"
    bl_label = "Show / Hide"
    bl_options = {"REGISTER", "UNDO"}

    name: StringProperty()

    def execute(self, context):
        lc = _layer_coll(context.view_layer.layer_collection, self.name)
        if lc is None:
            return {"CANCELLED"}
        hide = not lc.hide_viewport
        lc.hide_viewport = hide
        lc.collection.hide_render = hide
        return {"FINISHED"}


# ---------------------------------------------------------------------------
# Camera housekeeping: lock, rename, delete
# ---------------------------------------------------------------------------

class BBSV_OT_lock_camera(Operator):
    """Lock or unlock this camera. A locked camera cannot be moved, re-lensed, refocused or deleted"""

    bl_idname = "bb_sv.lock_camera"
    bl_label = "Lock Camera"
    bl_options = {"REGISTER", "UNDO"}

    name: StringProperty()

    def execute(self, context):
        cam = context.scene.objects.get(self.name)
        if cam is None or cam.type != "CAMERA":
            return {"CANCELLED"}
        _set_locked(cam, not _is_locked(cam))
        _flash("%s %s" % (cam.name, "locked" if _is_locked(cam) else "unlocked"))
        return {"FINISHED"}


class BBSV_OT_lock_hotkey(Operator):
    """Lock the active camera (Enter, in Artist Mode)"""

    bl_idname = "bb_sv.lock_hotkey"
    bl_label = "Lock Active Camera"
    bl_options = {"INTERNAL", "UNDO"}

    @classmethod
    def poll(cls, context):
        return _ARTIST["on"] and not _ARTIST.get("easy") and _active_cam(context) is not None

    def execute(self, context):
        cam = _active_cam(context)
        if not _is_locked(cam):
            _set_locked(cam, True)
        _flash("%s locked" % cam.name)
        return {"FINISHED"}


class BBSV_OT_rename_camera(Operator):
    """Rename this camera (its focus point follows)"""

    bl_idname = "bb_sv.rename_camera"
    bl_label = "Rename Camera"
    bl_options = {"REGISTER", "UNDO"}

    name: StringProperty(options={"HIDDEN"})
    new_name: StringProperty(name="Name")

    def invoke(self, context, event):
        self.new_name = self.name
        return context.window_manager.invoke_props_dialog(self, width=320)

    def execute(self, context):
        cam = context.scene.objects.get(self.name)
        new = self.new_name.strip()
        if cam is None or not new:
            return {"CANCELLED"}
        focus = cam.data.dof.focus_object
        cam.name = new
        cam.data.name = cam.name
        if focus is not None and focus.name.endswith(FOCUS_SUFFIX):
            focus.name = cam.name + FOCUS_SUFFIX
        if context.scene.bb_sv.active_cam == self.name:
            context.scene.bb_sv.active_cam = cam.name
        return {"FINISHED"}


class BBSV_OT_delete_camera(Operator):
    """Delete this camera and its focus point"""

    bl_idname = "bb_sv.delete_camera"
    bl_label = "Delete Camera"
    bl_options = {"REGISTER", "UNDO"}

    name: StringProperty()

    def invoke(self, context, event):
        return context.window_manager.invoke_confirm(self, event)

    def execute(self, context):
        scene = context.scene
        cam = scene.objects.get(self.name)
        if cam is None or cam.type != "CAMERA" or _refuse_if_locked(self, cam):
            return {"CANCELLED"}
        focus = cam.data.dof.focus_object
        data = cam.data
        bpy.data.objects.remove(cam, do_unlink=True)
        if data.users == 0:
            bpy.data.cameras.remove(data)
        if focus is not None and focus.name.endswith(FOCUS_SUFFIX):
            bpy.data.objects.remove(focus, do_unlink=True)
        if scene.camera is None:
            rest = _viewer_cams(scene)
            scene.camera = rest[0] if rest else None
        area = _view3d_area(context)
        if area and scene.camera is None:
            area.spaces.active.region_3d.view_perspective = "PERSP"
        _flash("Deleted %s" % self.name)
        return {"FINISHED"}


# ---------------------------------------------------------------------------
# Capture: a quick grab of what you see, or a full render of the shot
# ---------------------------------------------------------------------------

CAPTURE_DIR = "//Captures"
_RENDER_KEEP = {}
_LAST_SHOT = {"folder": ""}       # the folder the last Artist Mode capture went into


def _capture_dir():
    if bpy.data.filepath:
        folder = bpy.path.abspath(CAPTURE_DIR)
    else:
        folder = os.path.join(os.path.expanduser("~"), "BB Captures")
    os.makedirs(folder, exist_ok=True)
    return folder


def _shot_folder(name):
    """A folder of its own for one press of Capture, so a shot's passes stay together instead
    of a thousand loose files in one directory."""
    folder = os.path.join(_capture_dir(), re.sub(r'[\\/:*?"<>|]+', "-", name))
    n, base = 2, folder
    while os.path.exists(folder):          # never write into an existing shot's folder
        folder = "%s (%d)" % (base, n)
        n += 1
    os.makedirs(folder, exist_ok=True)
    return folder


def _capture_path(cam, kind):
    safe = re.sub(r'[\\/:*?"<>|]+', "-", cam.name)
    stamp = time.strftime("%Y-%m-%d %H%M%S")
    tag = "" if kind == "QUICK" else " - render"
    return os.path.join(_capture_dir(), "%s - %dmm - %s%s.png" % (safe, round(cam.data.lens), stamp, tag))


def _watch_render():
    """Main-thread timer: once Blender's render job ends, put the output settings
    back. Render handlers can fire off the main thread, where touching scene
    data or redrawing is unsafe, so they are deliberately not used here."""
    if bpy.app.is_job_running("RENDER"):
        return 0.5
    for name, keep in list(_RENDER_KEEP.items()):
        scene = bpy.data.scenes.get(name)
        _RENDER_KEEP.pop(name, None)
        if scene is None:
            continue
        path, scene.render.filepath, scene.render.image_settings.file_format = keep
        if os.path.exists(path):
            _flash("Render saved: %s" % os.path.basename(path), seconds=6)
        else:
            _flash("Render stopped - nothing saved", seconds=4)
    return None


def _is_blank(path):
    """True if a saved still is (almost) pure black - a view that had not drawn yet."""
    try:
        img = bpy.data.images.load(path, check_existing=False)
    except Exception:
        return False
    try:
        img.scale(64, 36)
        px = list(img.pixels)
        return max(max(px[i], px[i + 1], px[i + 2]) for i in range(0, len(px), 4)) < 0.02
    finally:
        bpy.data.images.remove(img)


def _grab_view(context, area, path, allow_rendered=False):
    """Save the camera's view exactly as drawn (no overlays, never a render). False if nothing
    saved. allow_rendered keeps Rendered shading, which the mist pass needs."""
    r = context.scene.render
    keep = (r.filepath, r.image_settings.file_format)
    r.filepath = path
    r.image_settings.file_format = "PNG"
    space = area.spaces.active
    rv3d = space.region_3d
    persp, overlays, shading = rv3d.view_perspective, space.overlay.show_overlays, space.shading.type
    rv3d.view_perspective = "CAMERA"
    space.overlay.show_overlays = False      # no camera frames or focus markers in the still
    if shading == "RENDERED" and not allow_rendered:   # a grab of the view, never a render
        space.shading.type = "SOLID"
    region = next(rg for rg in area.regions if rg.type == "WINDOW")
    try:
        with context.temp_override(area=area, region=region):
            bpy.ops.render.opengl(write_still=True, view_context=True)
    finally:
        r.filepath, r.image_settings.file_format = keep
        rv3d.view_perspective = persp
        space.overlay.show_overlays = overlays
        space.shading.type = shading
    if _is_blank(path):
        os.remove(path)
        _flash("The view was still loading - nothing saved. Try again in a moment.", seconds=5)
        return False
    return True


# The looks. One table drives both the view buttons and the capture passes, so what you see
# on screen and what lands in the Captures folder can never drift apart. Each is a recipe for
# Blender's own viewport shading - nothing here is a render except RENDER itself.
VIEW_LOOKS = (
    ("FAST", "Fast", "Solid view with the studio light - shapes and staging, nothing to wait for"),
    ("CLAY", "Clay", "Solid view, one clay colour under a soft studio light - form without "
                     "materials or lighting getting in the way"),
    ("LINE", "Line Art", "A line drawing: flat white, black outlines, creases picked out by "
                         "cavity. This is the pass the generation artists use most"),
    ("COLOUR", "Flat Colour", "Flat material colours with black outlines and no shading at all"),
    ("PREVIEW", "Preview", "Material preview: the set with its own materials"),
    ("RENDER", "Render", "EEVEE with ray tracing, the set's own lights and world"),
)
LOOK_LABEL = {k: l for k, l, _t in VIEW_LOOKS}


def _apply_look(shading, key, scene=None):
    """Put the viewport into one of the looks above. Values come from what Aman settled on by
    hand (2 Oct): the cavity numbers in particular are modest on purpose - turning them up
    stops the line art being a drawing and turns it into soft grey shading."""
    sh = shading
    if key == "PREVIEW":
        sh.type = "MATERIAL"
        return
    if key == "RENDER":
        sh.type = "RENDERED"
        return

    sh.type = "SOLID"
    for attr, value in (("show_specular_highlight", True), ("show_xray", False),
                        ("show_cavity", False), ("show_object_outline", False)):
        if hasattr(sh, attr):
            setattr(sh, attr, value)

    if key == "FAST":
        if _enum_ok(sh, "light", "STUDIO"):
            sh.light = "STUDIO"
        if _enum_ok(sh, "color_type", "MATERIAL"):
            sh.color_type = "MATERIAL"
        return

    if key == "CLAY":
        if _enum_ok(sh, "light", "STUDIO"):
            sh.light = "STUDIO"
        for name in ("paint.sl", "basic.sl", "Default"):
            try:
                sh.studio_light = name
                break
            except (TypeError, AttributeError):
                continue
        if _enum_ok(sh, "color_type", "SINGLE"):
            sh.color_type = "SINGLE"
            sh.single_color = (0.80, 0.80, 0.80)
        return

    # the two flat looks share everything except where the colour comes from
    if _enum_ok(sh, "light", "FLAT"):
        sh.light = "FLAT"
    if hasattr(sh, "show_specular_highlight"):
        sh.show_specular_highlight = False
    if hasattr(sh, "show_object_outline"):
        sh.show_object_outline = True
    if hasattr(sh, "object_outline_color"):
        sh.object_outline_color = (0.0, 0.0, 0.0)

    if key == "LINE":
        if _enum_ok(sh, "color_type", "OBJECT"):
            sh.color_type = "OBJECT"       # object colour is white unless someone set it
        if hasattr(sh, "show_cavity"):
            sh.show_cavity = True
        if _enum_ok(sh, "cavity_type", "BOTH"):
            sh.cavity_type = "BOTH"
        for attr, value in (("cavity_ridge_factor", 1.0), ("cavity_valley_factor", 1.0),
                            ("curvature_ridge_factor", 1.0), ("curvature_valley_factor", 2.0)):
            if hasattr(sh, attr):
                setattr(sh, attr, value)
    elif key == "COLOUR":
        if _enum_ok(sh, "color_type", "MATERIAL"):
            sh.color_type = "MATERIAL"


DEPTH_GRID = 9            # rays across the frame when measuring what the camera can see
DEPTH_SAMPLES = 16        # a depth map needs no sampling; this is pure insurance
LINEART_SCALE = 2          # drawn at twice the frame size: finer, denser lines
LINEART_CONTRAST = 1.0     # how hard the saved image is pushed to ink on paper

CAPTURE_PASSES = (
    ("look", "Current View", "RESTRICT_VIEW_OFF"),
    ("FAST", "Fast", "SHADING_SOLID"),
    ("CLAY", "Clay", "MATSPHERE"),
    ("LINE", "Line Art", "MOD_LINEART"),
    ("COLOUR", "Flat Colour", "COLOR"),
    ("PREVIEW", "Preview", "SHADING_TEXTURE"),
    ("grey", "Greyscale", "IMAGE_ZDEPTH"),
    ("depth", "Depth Map", "MOD_FLUIDSIM"),
)


def _enabled_passes(props):
    on = [k for k, _l, _i in CAPTURE_PASSES if getattr(props, "pass_" + k, False)]
    return on or ["look"]


def _pass_path(base, key):
    if key == "look":
        return base
    stem, ext = os.path.splitext(base)
    return "%s - %s%s" % (stem, key, ext)


def _desaturate(path):
    """Take the colour out of a saved still, keeping what the eye reads as brightness."""
    try:
        import numpy as np
        img = bpy.data.images.load(path, check_existing=False)
    except Exception:
        return False                      # no image was opened, so nothing to clean up
    try:
        px = np.empty(len(img.pixels), dtype=np.float32)
        img.pixels.foreach_get(px)
        px = px.reshape(-1, 4)
        lum = px[:, 0] * 0.2126 + px[:, 1] * 0.7152 + px[:, 2] * 0.0722
        px[:, 0] = px[:, 1] = px[:, 2] = lum
        img.pixels.foreach_set(px.ravel())
        img.filepath_raw = path
        img.file_format = "PNG"
        img.save()
        return True
    except Exception:
        return False
    finally:
        bpy.data.images.remove(img)


def _force_eevee(scene):
    """Cycles is not part of this workflow - previews, blocking and reference only."""
    if scene.render.engine == "BLENDER_EEVEE":
        return False
    try:
        scene.render.engine = "BLENDER_EEVEE"      # dynamic enum: the error lists what is valid
        return True
    except TypeError:
        return False


def _depth_node_group(scene, near_white):
    """Depth pass -> Normalize -> colour ramp -> out.

    Normalize takes whatever is in frame and stretches it across the full range, so the map
    reads properly wherever the camera is pointed, with nothing to set by hand. (The one place
    it struggles is an open set with sky in shot: the sky sits at 10^10 and takes the far end.)

    Blender 5's compositor is a node group on the scene; there is no Composite node any more,
    the group's output is the result, and the colour ramp is the shader one reused here."""
    name = "BB Depth Map"
    ng = bpy.data.node_groups.get(name)
    if ng is not None:
        bpy.data.node_groups.remove(ng)
    ng = bpy.data.node_groups.new(name, "CompositorNodeTree")
    try:
        ng.interface.new_socket("Image", in_out="OUTPUT", socket_type="NodeSocketColor")
    except Exception:
        pass

    rl = ng.nodes.new("CompositorNodeRLayers")
    rl.scene = scene
    rl.location = (-600, 0)
    norm = ng.nodes.new("CompositorNodeNormalize")
    norm.location = (-360, 0)
    ramp = ng.nodes.new("ShaderNodeValToRGB")
    ramp.location = (-160, 0)
    a, b = (1.0, 0.0) if near_white else (0.0, 1.0)
    ramp.color_ramp.elements[0].color = (a, a, a, 1.0)
    ramp.color_ramp.elements[1].color = (b, b, b, 1.0)
    out = ng.nodes.new("NodeGroupOutput")
    out.location = (60, 0)

    depth = rl.outputs.get("Depth") or rl.outputs.get("Z")
    if depth is None:
        return None
    ng.links.new(depth, norm.inputs["Value"])
    ng.links.new(norm.outputs["Value"], ramp.inputs["Factor"])
    ng.links.new(ramp.outputs["Color"], out.inputs[0])
    return ng


def _visible_depth_range(context, cam):
    """How near and how far the camera can actually see, by firing a grid of rays through the
    frame. Taking the range from the whole set instead puts one room into a sliver of the
    gradient, which is what made the first depth maps look flat."""
    scene = context.scene
    dg = context.evaluated_depsgraph_get()
    eye = cam.matrix_world.translation
    mat = cam.matrix_world.to_3x3()
    frame = [mat @ v for v in cam.data.view_frame(scene=scene)]
    hits = []
    for i in range(DEPTH_GRID):
        for j in range(DEPTH_GRID):
            u, v = i / (DEPTH_GRID - 1.0), j / (DEPTH_GRID - 1.0)
            top = frame[0].lerp(frame[1], u)
            bottom = frame[3].lerp(frame[2], u)
            d = top.lerp(bottom, v).normalized()
            hit, loc, _n, _i, _o, _m = scene.ray_cast(dg, eye, d)
            if hit:
                hits.append((loc - eye).length)
    if not hits:
        return cam.data.clip_start, min(cam.data.clip_end, 50.0)
    near = max(cam.data.clip_start, min(hits) * 0.97)
    far = max(near + 0.05, max(hits) * 1.03)
    return near, far


def _capture_mist(context, area, cam, path):
    """Grab the viewport's Mist pass instead of rendering a depth map.

    Mist is depth, already normalised between a near and a far distance, and EEVEE can show it
    live - so this is a viewport grab, not a render: instant, and nothing to compile. The range
    is set from what the camera can see. Mist runs black at the camera to white in the distance,
    so the saved image is inverted to put white nearest, which is the way depth maps are used."""
    scene = context.scene
    _force_eevee(scene)
    vl = context.view_layer
    space = area.spaces.active
    sh = space.shading
    world = scene.world
    if world is None:
        world = bpy.data.worlds.new("World")
        scene.world = world

    keep_pass = vl.use_pass_mist
    keep_mist = (world.mist_settings.use_mist, world.mist_settings.start,
                 world.mist_settings.depth, world.mist_settings.falloff)
    keep_shading = (sh.type, getattr(sh, "render_pass", "COMBINED"))
    try:
        vl.use_pass_mist = True
        near, far = _visible_depth_range(context, cam)
        ms = world.mist_settings
        ms.use_mist, ms.start, ms.depth = True, near, max(0.05, far - near)
        ms.falloff = "LINEAR"            # depth, not atmosphere: no curve on it
        sh.type = "RENDERED"
        if not _enum_ok(sh, "render_pass", "MIST"):
            return False
        sh.render_pass = "MIST"
        ok = _grab_view(context, area, path, allow_rendered=True)
    finally:
        sh.type, rp = keep_shading[0], keep_shading[1]
        try:
            sh.render_pass = rp
        except (TypeError, AttributeError):
            pass
        (world.mist_settings.use_mist, world.mist_settings.start,
         world.mist_settings.depth, world.mist_settings.falloff) = keep_mist
        vl.use_pass_mist = keep_pass
    if ok and scene.bb_sv.depth_near_white:
        _invert_image(path)              # mist is black near, white far - flip it
    return ok


def _invert_image(path):
    """Flip black and white on a saved greyscale image."""
    try:
        import numpy as np
        img = bpy.data.images.load(path, check_existing=False)
    except Exception:
        return False
    try:
        px = np.empty(len(img.pixels), dtype=np.float32)
        img.pixels.foreach_get(px)
        a = px.reshape(-1, 4)
        a[:, :3] = 1.0 - a[:, :3]
        a[:, 3] = 1.0
        img.pixels.foreach_set(a.ravel())
        img.filepath_raw = path
        img.file_format = "PNG"
        img.save()
        return True
    except Exception:
        return False
    finally:
        bpy.data.images.remove(img)


def _render_depth(context, cam, path):
    """Render the frame in EEVEE and save its depth map. Rendering is the only way to get a
    depth pass - the viewport cannot hand one over."""
    scene = context.scene
    switched = _force_eevee(scene)
    vl = context.view_layer
    keep_z = vl.use_pass_z
    vl.use_pass_z = True
    prev_group = getattr(scene, "compositing_node_group", None)
    ng = _depth_node_group(scene, scene.bb_sv.depth_near_white)
    if ng is None:
        _flash("Could not build the depth map nodes", seconds=4)
        return False
    r = scene.render
    keep = (r.filepath, r.image_settings.file_format, r.image_settings.color_mode)
    # A depth map must be saved exactly as computed. The default view transform (AgX/Filmic) is
    # a film response curve for pictures: it bends the gradient and turns white into about 0.77,
    # which is what makes a depth map come out flat and grey.
    vs = scene.view_settings
    keep_view = (vs.view_transform, vs.look, vs.exposure, vs.gamma)
    # A depth map is a measurement, not a picture: it needs no samples, no ray tracing and
    # certainly not Cycles. Files get left in Cycles by accident, which turns a two second
    # job into minutes for a result that looks exactly the same.
    ee = getattr(scene, "eevee", None)
    keep_eevee = {}
    for attr, cheap in (("taa_render_samples", DEPTH_SAMPLES), ("use_raytracing", False),
                        ("use_shadows", False), ("use_volumetric_lights", False)):
        if ee is not None and hasattr(ee, attr):
            keep_eevee[attr] = getattr(ee, attr)
            setattr(ee, attr, cheap)
    try:
        for name in ("Standard", "Raw"):
            try:
                vs.view_transform = name
                break
            except TypeError:
                continue
        try:
            vs.look = "None"
        except TypeError:
            pass
        vs.exposure, vs.gamma = 0.0, 1.0
        scene.compositing_node_group = ng
        r.filepath = path
        r.image_settings.file_format = "PNG"
        r.image_settings.color_mode = "BW"
        bpy.ops.render.render(write_still=True)        # blocking, so the next pass waits
    except Exception as exc:
        _flash("Depth render failed: %s" % exc, seconds=5)
        return False
    finally:
        # put the file's own compositor back: every later render would be a depth map otherwise
        scene.compositing_node_group = prev_group
        for attr, value in keep_eevee.items():
            setattr(ee, attr, value)
        vs.view_transform, vs.look, vs.exposure, vs.gamma = keep_view
        r.filepath, r.image_settings.file_format, r.image_settings.color_mode = keep
        vl.use_pass_z = keep_z
        if switched:
            _flash("Switched to EEVEE for the depth map - it does not need Cycles", seconds=4)
    return os.path.exists(path)


_LOOK_ATTRS = ("type", "light", "color_type", "single_color", "background_type",
               "background_color", "show_xray", "show_cavity", "cavity_type",
               "cavity_ridge_factor", "cavity_valley_factor", "curvature_ridge_factor",
               "curvature_valley_factor", "show_object_outline", "object_outline_color",
               "show_specular_highlight", "wireframe_color_type")


def _lift_lines(path, strength=1.0):
    """Turn a flat grey drawing into black lines on white paper.

    Solid view draws the paper at about 0.73 and the lines only a little darker than that, so
    straight out of the viewport it reads as grey on grey (measured on Happy 4Eva: paper 0.729,
    the darkest lines 0.46, nothing above 0.733). The paper is taken as the value most of the
    frame sits at, the darkest half a percent becomes black, and a gamma pushes what is left of
    the lines down without touching the paper."""
    try:
        import numpy as np
        img = bpy.data.images.load(path, check_existing=False)
    except Exception:
        return False
    try:
        px = np.empty(len(img.pixels), dtype=np.float32)
        img.pixels.foreach_get(px)
        a = px.reshape(-1, 4)
        lum = a[:, 0] * 0.2126 + a[:, 1] * 0.7152 + a[:, 2] * 0.0722
        white = float(np.percentile(lum, 97.0))
        black = float(np.percentile(lum, 0.5))
        if white - black < 1e-4:
            return False
        out = np.clip((lum - black) / (white - black), 0.0, 1.0)
        if strength > 0.0:
            out = out ** (1.0 + strength * 0.8)
        a[:, 0] = a[:, 1] = a[:, 2] = out
        a[:, 3] = 1.0
        img.pixels.foreach_set(a.ravel())
        img.filepath_raw = path
        img.file_format = "PNG"
        img.save()
        return True
    except Exception:
        return False
    finally:
        bpy.data.images.remove(img)


def _depth_image(context, area, cam, path):
    """A depth map, the cheapest way available: the viewport's mist pass if this Blender can
    show it, and a render only as a fallback."""
    if _capture_mist(context, area, cam, path):
        return True
    _flash("Mist pass unavailable - rendering the depth map instead", seconds=4)
    return _render_depth(context, cam, path)


def _capture_pass(context, area, cam, key, path):
    """One pass. Everything except the depth map is a grab of the viewport, so it is instant."""
    if key == "depth":
        return _depth_image(context, area, cam, path)
    space = area.spaces.active
    sh = space.shading
    keep = {a: (tuple(getattr(sh, a)) if a in ("single_color", "background_color",
                                               "object_outline_color") else getattr(sh, a))
            for a in _LOOK_ATTRS if hasattr(sh, a)}
    render = context.scene.render
    keep_res = render.resolution_percentage
    try:
        if key in LOOK_LABEL:                      # a named look: set the viewport to it
            _apply_look(sh, key, context.scene)
            if key == "RENDER":
                _force_eevee(context.scene)
                _scene_lighting(sh, True)
        if key == "LINE":
            render.resolution_percentage = keep_res * LINEART_SCALE
        ok = _grab_view(context, area, path)
    finally:
        render.resolution_percentage = keep_res
        for attr, value in keep.items():
            try:
                setattr(sh, attr, value)
            except Exception:
                pass
    if ok and key == "grey":
        _desaturate(path)
    if ok and key == "LINE":
        _lift_lines(path, LINEART_CONTRAST)
    return ok


def _capture_all(context, area, cam, base_path, keys=None):
    """Save the passes asked for - by default every one ticked in Artist Mode. Easy Mode passes
    an explicit list, because there it saves only what is on screen."""
    keys = keys if keys is not None else _enabled_passes(context.scene.bb_sv)
    written = []
    for key in keys:
        path = _pass_path(base_path, key)
        if _capture_pass(context, area, cam, key, path):
            written.append(os.path.basename(path))
    return written


class BBSV_OT_play(Operator):
    """Play or pause the animation - mocap takes, or anything else keyframed in the set"""

    bl_idname = "bb_sv.play"
    bl_label = "Play Animation"
    bl_options = {"INTERNAL"}

    def execute(self, context):
        # Both modes hide Blender's timeline, so this button is the only way to start playback.
        try:
            bpy.ops.screen.animation_play()
        except RuntimeError as exc:
            _flash("Could not start playback (%s)" % exc, seconds=4)
            return {"CANCELLED"}
        return {"FINISHED"}


class BBSV_OT_rewind(Operator):
    """Go back to the first frame"""

    bl_idname = "bb_sv.rewind"
    bl_label = "Back to Start"
    bl_options = {"INTERNAL"}

    def execute(self, context):
        context.scene.frame_set(context.scene.frame_start)
        return {"FINISHED"}


def _draw_play(lay, context):
    """Play, and a way back to frame one. Shown whenever the scene has anything animated."""
    scene = context.scene
    animated = any(o.animation_data and (o.animation_data.action or o.animation_data.nla_tracks)
                   for o in scene.objects)
    if not animated:
        animated = any(o.type == "ARMATURE" for o in scene.objects)
    if not animated:
        return
    playing = getattr(context.screen, "is_animation_playing", False)
    row = lay.row(align=True)
    row.scale_y = 1.3
    row.operator("bb_sv.play", text="Pause" if playing else "Play",
                 icon="PAUSE" if playing else "PLAY", depress=playing)
    sub = row.row(align=True)
    sub.scale_x = 0.45
    sub.operator("bb_sv.rewind", text="", icon="REW")
    sub = lay.row()
    sub.scale_y = 0.6
    sub.label(text="Frame %d of %d-%d" % (scene.frame_current, scene.frame_start, scene.frame_end))


class BBSV_OT_clear_cameras(Operator):
    """Delete every camera in the scene - including any the art team left behind"""

    bl_idname = "bb_sv.clear_cameras"
    bl_label = "Clear All Cameras"
    bl_options = {"REGISTER", "UNDO"}

    def invoke(self, context, event):
        n = sum(1 for o in context.scene.objects if o.type == "CAMERA")
        if not n:
            _flash("There are no cameras to clear")
            return {"CANCELLED"}
        return context.window_manager.invoke_confirm(
            self, event, message="Delete all %d camera(s) in this scene?" % n)

    def execute(self, context):
        gone = 0
        for o in list(context.scene.objects):
            if o.type == "CAMERA":
                data = o.data
                bpy.data.objects.remove(o)
                if data is not None and data.users == 0:
                    bpy.data.cameras.remove(data)
                gone += 1
        context.scene.camera = None
        _flash("Cleared %d camera(s)" % gone, seconds=4)
        self.report({"INFO"}, "Cleared %d camera(s)" % gone)
        return {"FINISHED"}


def _draw_looks(lay, p, columns=3):
    """The view buttons: what the artist actually sees on screen."""
    grid = lay.grid_flow(row_major=True, columns=columns, even_columns=True, align=True)
    grid.scale_y = 1.2
    for key, label, _tip in VIEW_LOOKS:
        grid.operator("bb_sv.set_look", text=label, depress=p.look_now == key).mode = key
    # Set Lights only means anything in Preview; Render always uses the set's own lighting
    if p.look_now == "PREVIEW":
        lay.prop(p, "scene_lights", toggle=True, icon="LIGHT")
    elif p.look_now == "RENDER":
        row = lay.row()
        row.enabled = False
        row.prop(p, "scene_lights", toggle=True, icon="LIGHT",
                 text="Set Lights (always on here)")


def _draw_passes(lay, p):
    """Which versions of the frame one press of Capture saves. Always on show: hiding this
    behind a toggle only made people wonder where it went."""
    col = lay.column(align=True)
    row = col.row()
    row.scale_y = 0.8
    row.label(text="Capture passes", icon="RENDERLAYERS")
    grid = col.grid_flow(row_major=True, columns=2, even_columns=True, align=True)
    for key, label, icon in CAPTURE_PASSES:
        grid.prop(p, "pass_" + key, text=label, icon=icon, toggle=True)
    if p.pass_depth:
        col.prop(p, "depth_near_white")


class BBSV_OT_capture(Operator):
    """Save a still of the active camera's shot into the Captures folder next to this file"""

    bl_idname = "bb_sv.capture"
    bl_label = "Capture"
    bl_options = {"REGISTER"}

    kind: EnumProperty(items=[
        ("QUICK", "Quick Capture", "Instant grab of the view as you see it - no rendering"),
        ("RENDER", "Render Still", "Final quality with the set's lighting - slower"),
    ])

    def execute(self, context):
        scene = context.scene
        cam = _active_cam(context)
        area = _view3d_area(context)
        if cam is None or area is None:
            self.report({"WARNING"}, "Add or pick a camera first")
            _flash("Add or pick a camera first")
            return {"CANCELLED"}
        if self.kind == "QUICK" and bpy.app.is_job_running("SHADER_COMPILATION"):
            _flash("Materials are still loading - try again in a few seconds", seconds=4)
            return {"CANCELLED"}
        path = _capture_path(cam, self.kind)
        if self.kind == "QUICK":
            # one folder per press, holding every pass of that shot
            folder = _shot_folder(os.path.splitext(os.path.basename(path))[0])
            path = os.path.join(folder, os.path.basename(path))
            written = _capture_all(context, area, cam, path)
            _LAST_SHOT["folder"] = folder
            if not written:
                return {"CANCELLED"}
            _flash("Captured %d pass(es) into %s" % (len(written), os.path.basename(folder))
                   if len(written) > 1 else "Captured: %s" % written[0], seconds=5)
            self.report({"INFO"}, "Captured %s" % ", ".join(written))
            return {"FINISHED"}
        _force_eevee(scene)          # no Cycles in this workflow
        r = scene.render
        keep = (r.filepath, r.image_settings.file_format)
        r.filepath = path
        r.image_settings.file_format = "PNG"
        # full render opens Blender's render window and saves when it finishes
        _RENDER_KEEP[scene.name] = (path,) + keep
        _flash("Rendering... it saves itself when done", seconds=4)
        result = bpy.ops.render.render("INVOKE_DEFAULT", write_still=True)
        if not bpy.app.timers.is_registered(_watch_render):
            bpy.app.timers.register(_watch_render, first_interval=1.0)
        return result


class BBSV_OT_open_captures(Operator):
    """Open the Captures folder in Finder or Explorer"""

    bl_idname = "bb_sv.open_captures"
    bl_label = "Open Captures Folder"

    def execute(self, context):
        folder = _LAST_SHOT.get("folder") or _capture_dir()
        if not os.path.isdir(folder):
            folder = _capture_dir()
        # wm.path_open is unreliable on a directory - on macOS it hands Launch Services a path
        # with no file to open and silently does nothing. Ask the OS directly instead.
        try:
            if sys.platform == "darwin":
                subprocess.Popen(["open", folder])
            elif sys.platform.startswith("win"):
                os.startfile(folder)                                  # noqa: S606
            else:
                subprocess.Popen(["xdg-open", folder])
        except Exception:
            try:
                bpy.ops.wm.path_open(filepath=folder)
            except Exception as exc:
                _flash("Could not open %s (%s)" % (folder, exc), seconds=6)
                self.report({"WARNING"}, folder)
                return {"CANCELLED"}
        self.report({"INFO"}, folder)
        return {"FINISHED"}


# ---------------------------------------------------------------------------
# First-run tutorial
# ---------------------------------------------------------------------------

def _tutorial_marker():
    name = "bb_set_viewer_easy_tutorial_seen" if _ARTIST.get("easy") else "bb_set_viewer_tutorial_seen"
    return os.path.join(bpy.utils.user_resource("CONFIG", create=True), name)


def _tutorial_seen():
    try:
        return os.path.exists(_tutorial_marker())
    except Exception:
        return True          # never nag if the config folder is unreachable


TUTORIAL = (
    ("VIEW_PAN", "Walk", "Press F to walk, F again to stop. Mouse looks, W A S D or the arrow keys move,",
     "Space goes up, Ctrl goes down, hold Shift to move faster."),
    ("OUTLINER_OB_CAMERA", "Make a shot", "Walk to a view you like and click Add Camera Here.",
     "Press 0 to look through it. Press F to walk the camera itself into position."),
    ("LOCKED", "Lock it", "Press Enter to finish and lock the camera, so nothing can bump it.",
     "The padlock in the camera list unlocks it. Esc stops walking without locking."),
    ("TOOL_SETTINGS", "Fine-tune", "Lens, Focus and Framing sit in the panel on the right.",
     "Right-click while walking undoes the walk. Cmd/Ctrl + Z undoes anything else."),
    ("DRIVER_DISTANCE", "Change the lens", "Number keys 1 to 6 are the focal lengths: 18, 24, 35, 50, 85, 135 mm.",
     "They work while you walk too, so the shot can be framed on the move."),
    ("RENDER_STILL", "Capture", "Press C, or click Quick Capture, to save exactly what you see.",
     "Render Still gives final quality. Both land in the Captures folder beside this file."),
)


TUTORIAL_EASY = (
    ("VIEW_PAN", "Walk", "Press F (or click Walk) to move the camera. Mouse looks, W A S D or the arrows move,",
     "Space goes up, Ctrl goes down, Shift is faster. F again to stop."),
    ("TOOL_SETTINGS", "Lens and focus", "Focal Length: small numbers are wide, big numbers are close.",
     "Number keys 1 to 6 jump to 18, 24, 35, 50, 85 and 135 mm, walking or not."),
    ("RENDER_STILL", "Capture", "Press C, or click Capture, to save the picture and the camera settings",
     "into the Captures folder beside this file."),
)


class BBSV_OT_tutorial(Operator):
    """How to frame a shot in this set"""

    bl_idname = "bb_sv.tutorial"
    bl_label = "How to frame a shot"
    bl_options = {"INTERNAL"}

    def invoke(self, context, event):
        wm = context.window_manager
        try:
            return wm.invoke_props_dialog(self, width=560, title="Welcome - framing shots in this set",
                                          confirm_text="Got it")
        except TypeError:      # Blender before 4.1
            return wm.invoke_props_dialog(self, width=560)

    def draw(self, context):
        lay = self.layout
        for icon, title, a, b in (TUTORIAL_EASY if _ARTIST.get("easy") else TUTORIAL):
            box = lay.box()
            row = box.row()
            row.label(text=title, icon=icon)
            col = box.column(align=True)
            col.scale_y = 0.8
            col.label(text=a)
            col.label(text=b)
        if not _ARTIST.get("easy"):
            lay.label(text="Reopen this any time: Panel Setup > Show Tutorial.", icon="INFO")

    def execute(self, context):
        try:
            with open(_tutorial_marker(), "w", encoding="utf-8") as f:
                f.write(time.strftime("%Y-%m-%d %H:%M:%S"))
        except Exception:
            pass
        return {"FINISHED"}


def _show_tutorial():
    wm = bpy.context.window_manager
    if not wm or not wm.windows:
        return None
    window = wm.windows[0]
    area = max((a for a in window.screen.areas if a.type == "VIEW_3D"), key=lambda a: a.width * a.height, default=None)
    if area is None:
        return None
    region = next(r for r in area.regions if r.type == "WINDOW")
    with bpy.context.temp_override(window=window, area=area, region=region):
        bpy.ops.bb_sv.tutorial("INVOKE_DEFAULT")
    return None


# ---------------------------------------------------------------------------
# On-screen label: the header is hidden in Artist Mode, so status lives here
# ---------------------------------------------------------------------------

_OVERLAY = {"handle": None, "flash": "", "until": 0.0}


def _flash(text, seconds=3.0):
    _OVERLAY["flash"], _OVERLAY["until"] = text, time.time() + seconds

    def _redraw():
        for win in bpy.context.window_manager.windows:
            for a in win.screen.areas:
                if a.type == "VIEW_3D":
                    a.tag_redraw()
        return None
    _redraw()
    bpy.app.timers.register(_redraw, first_interval=seconds + 0.1)


def _draw_overlay():
    if not (_ARTIST["on"] or _WALK["on"]):
        return
    ctx = bpy.context
    region, rv3d = ctx.region, ctx.region_data
    if region is None or rv3d is None:
        return
    cam = _active_cam(ctx)
    gold, white, grey = (1.0, 0.82, 0.35, 1.0), (1.0, 1.0, 1.0, 0.95), (0.85, 0.85, 0.85, 0.85)
    lines = []
    if _ARTIST.get("easy") and not _WALK["on"]:
        if cam:
            d = cam.data
            dof = ("f/%.1f, focus %.1f m" % (d.dof.aperture_fstop, d.dof.focus_distance)) if d.dof.use_dof else "no blur"
            lines.append(("%d mm   |   %s   |   F to walk" % (round(d.lens), dof), white))
    elif _WALK["on"]:
        tail = "   |   Enter: stop and lock camera" if _WALK["camera"] and not _ARTIST.get("easy") else ""
        lines.append(("WALKING  -  F or Esc to stop%s   |   Right-click: undo walk" % tail, gold))
    elif cam and rv3d.view_perspective == "CAMERA":
        state = "LOCKED" if _is_locked(cam) else "unlocked - press Enter to lock"
        lines.append(("%s   |   %d mm   |   %s" % (cam.name, round(cam.data.lens), state), white))
    else:
        lines.append(("Free view  -  press F to walk,  0 to look through the camera", grey))
    if _OVERLAY["flash"] and time.time() < _OVERLAY["until"]:
        lines.append((_OVERLAY["flash"], gold))
    scale = ctx.preferences.system.ui_scale
    fid = 0
    blf.size(fid, 15 * scale)
    blf.enable(fid, blf.SHADOW)
    blf.shadow(fid, 3, 0.0, 0.0, 0.0, 0.85)
    blf.shadow_offset(fid, 1, -1)
    y = region.height - 34 * scale
    for text, colour in lines:
        blf.color(fid, *colour)
        blf.position(fid, 20 * scale, y, 0)
        blf.draw(fid, text)
        y -= 24 * scale
    blf.disable(fid, blf.SHADOW)


# ---------------------------------------------------------------------------
# Artist Mode
# ---------------------------------------------------------------------------

_ARTIST = {"on": False, "easy": False, "hidden_panels": {}, "panel_set": []}

SPACE_SETTINGS = (
    ("show_region_header", False), ("show_region_tool_header", False),
    ("show_region_toolbar", False), ("show_region_ui", True),
    ("show_gizmo_navigate", False),
    # never hide the 'Light' object type: in Preview a hidden light gives no light (v2.5 bug)
)
OVERLAY_SETTINGS = (
    ("show_floor", False), ("show_ortho_grid", False), ("show_axis_x", False),
    ("show_axis_y", False), ("show_axis_z", False), ("show_cursor", False),
    ("show_relationship_lines", False), ("show_stats", False), ("show_text", False),
    ("show_face_orientation", False), ("show_annotation", False),
)
BACKUP_KEY = "bb_sv_artist_backup"


def artist_on():
    return _ARTIST["on"]


def _panel_subclasses(c):
    for s in c.__subclasses__():
        yield s
        yield from _panel_subclasses(s)


def _foreign_sidebar_panels():
    return [c for c in set(_panel_subclasses(Panel))
            if getattr(c, "bl_space_type", "") == "VIEW_3D"
            and getattr(c, "bl_region_type", "") == "UI"
            and not c.__name__.startswith("BBSV_")
            and getattr(c, "is_registered", False)]


def _reregister(classes):
    by_id = {getattr(c, "bl_idname", c.__name__): c for c in classes}

    def depth(c):
        d, pid = 0, getattr(c, "bl_parent_id", "")
        while pid:
            d, pid = d + 1, getattr(by_id.get(pid), "bl_parent_id", "")
        return d
    order = sorted(classes, key=depth)          # parents first
    for c in reversed(order):
        bpy.utils.unregister_class(c)
    return order


def _artist_poll(effective):
    # Blender insists on exactly (cls, context); extra defaulted args are rejected
    def poll(cls, context):
        if _ARTIST["on"]:
            return False
        return effective(context) if effective else True
    return classmethod(poll)


def _register_all(order):
    """Register parents before children. A panel that refuses its patched poll
    gets its original back and is registered as it was, so nothing goes missing."""
    for c in order:
        try:
            bpy.utils.register_class(c)
            continue
        except Exception as e:
            print("BB Set Viewer: re-register failed, restoring original:", c.__name__, e)
        if c in _ARTIST["hidden_panels"]:
            orig = _ARTIST["hidden_panels"].pop(c)
            if orig is None:
                if "poll" in c.__dict__:
                    del c.poll
            else:
                c.poll = orig
        try:
            bpy.utils.register_class(c)
        except Exception as e:
            print("BB Set Viewer: could not re-register", c.__name__, e)


def _hide_foreign_panels():
    """Every other sidebar tab gets a poll that is false while Artist Mode is on.

    Many built-in panels have no poll at all, and Blender only notices a poll
    at registration, so each panel is unregistered, patched and registered
    again. Nothing is persistent: a restart or leaving Artist Mode restores them.
    """
    if _ARTIST["panel_set"]:
        return
    order = _reregister(_foreign_sidebar_panels())
    _ARTIST["panel_set"] = list(order)
    for c in order:
        if not getattr(c, "bl_parent_id", ""):
            _ARTIST["hidden_panels"][c] = c.__dict__.get("poll")   # own poll, restored on exit
            c.poll = _artist_poll(getattr(c, "poll", None))          # own or inherited, bound to c
    _register_all(order)


def _restore_foreign_panels():
    if not _ARTIST["panel_set"]:
        return
    order = _ARTIST["panel_set"]
    for c in reversed(order):
        if getattr(c, "is_registered", False):
            bpy.utils.unregister_class(c)
    for c, orig in _ARTIST["hidden_panels"].items():
        if orig is None:
            if "poll" in c.__dict__:
                del c.poll
        else:
            c.poll = orig
    _ARTIST["hidden_panels"].clear()
    _ARTIST["panel_set"] = []
    _register_all(order)


def _lock_set(scene, lock):
    """Make every collection unselectable, so nothing can be clicked, moved or deleted."""
    backup = json.loads(scene.get(BACKUP_KEY, "{}"))
    if lock:
        sel = backup.setdefault("select", {})
        for c in scene.collection.children_recursive:
            sel.setdefault(c.name, c.hide_select)
            c.hide_select = True
        for o in scene.objects:
            o.select_set(False)
        bpy.context.view_layer.objects.active = None
    else:
        for name, was in backup.get("select", {}).items():
            c = bpy.data.collections.get(name)
            if c:
                c.hide_select = was
        backup.pop("select", None)
    scene[BACKUP_KEY] = json.dumps(backup)


def _backup_view(scene, space):
    """Record the normal-layout view settings once; a later entry never overwrites them."""
    backup = json.loads(scene.get(BACKUP_KEY, "{}"))
    saved = backup.setdefault("view", {})
    for key, _val in SPACE_SETTINGS:
        if hasattr(space, key):
            saved.setdefault("space." + key, getattr(space, key))
    for key, _val in OVERLAY_SETTINGS:
        if hasattr(space.overlay, key):
            saved.setdefault("overlay." + key, getattr(space.overlay, key))
    saved.setdefault("overlay.show_extras", space.overlay.show_extras)
    scene[BACKUP_KEY] = json.dumps(backup)


def _style_view(scene, space, strip):
    backup = json.loads(scene.get(BACKUP_KEY, "{}"))
    if strip:
        for key, val in SPACE_SETTINGS:
            if hasattr(space, key):
                setattr(space, key, val)
        for key, val in OVERLAY_SETTINGS:
            if hasattr(space.overlay, key):
                setattr(space.overlay, key, val)
        return
    else:
        for key, val in backup.get("view", {}).items():
            where, attr = key.split(".", 1)
            target = space if where == "space" else space.overlay
            if hasattr(target, attr):
                setattr(target, attr, val)
        backup.pop("view", None)
    scene[BACKUP_KEY] = json.dumps(backup)


def _full_screen(window, want):
    area = max((a for a in window.screen.areas if a.type == "VIEW_3D"), key=lambda a: a.width * a.height, default=None)
    if area is None:
        return None
    if bool(window.screen.show_fullscreen) != want:
        region = next(r for r in area.regions if r.type == "WINDOW")
        with bpy.context.temp_override(window=window, area=area, region=region):
            bpy.ops.screen.screen_full_area(use_hide_panels=True)
        area = max((a for a in window.screen.areas if a.type == "VIEW_3D"), key=lambda a: a.width * a.height)
    return area


def enter_artist_mode(window, easy=None):
    scene = window.scene
    if easy is None:
        easy = scene.bb_sv.easy_mode
    if not window.screen.show_fullscreen:
        normal = max((a for a in window.screen.areas if a.type == "VIEW_3D"),
                     key=lambda a: a.width * a.height, default=None)
        if normal is not None:
            _backup_view(scene, normal.spaces.active)
    area = _full_screen(window, True)
    if area is None:
        return False
    space = area.spaces.active
    _style_view(scene, space, True)
    space.show_object_viewport_light = True     # files stripped by v2.5 or earlier saved it off
    # Open in Fast. A heavy set in Material Preview has to compile a shader for every material
    # before it will draw, which is a long freeze and the easiest way to make Blender look
    # hung - or run a laptop out of memory. Fast draws immediately; the look buttons are right
    # there when the shot is framed.
    _apply_look(space.shading, "FAST", scene)
    scene.bb_sv.look_now = "FAST"
    _apply_capture_size(scene)
    _scene_lighting(space.shading, scene.bb_sv.scene_lights)
    _lock_set(scene, True)
    _ARTIST["on"] = True
    _ARTIST["easy"] = bool(easy)
    _hide_foreign_panels()
    scene.bb_sv.artist_mode = not easy
    scene.bb_sv.easy_mode = bool(easy)
    if easy:
        _easy_setup(window, area)
    area.tag_redraw()
    if not _tutorial_seen():
        bpy.app.timers.register(_show_tutorial, first_interval=0.6)
    return True


def exit_artist_mode(window):
    scene = window.scene
    _ARTIST["on"] = False
    _restore_foreign_panels()
    area = _full_screen(window, False)
    if area:
        _style_view(scene, area.spaces.active, False)
        area.tag_redraw()
    _lock_set(scene, False)
    scene.bb_sv.artist_mode = False
    scene.bb_sv.easy_mode = False
    _ARTIST["easy"] = False
    return True


class BBSV_OT_artist_enter(Operator):
    """Hide everything but this panel, lock the set, and switch off Blender's own shortcuts. Saved with the file"""

    bl_idname = "bb_sv.artist_enter"
    bl_label = "Enter Artist Mode"

    easy: BoolProperty(default=False, options={"SKIP_SAVE"})

    def execute(self, context):
        if not enter_artist_mode(context.window, easy=self.easy):
            self.report({"WARNING"}, "Needs a 3D view on screen")
            return {"CANCELLED"}
        self.report({"INFO"}, "%s on - save the file to open it this way next time"
                    % ("Easy Mode" if self.easy else "Artist Mode"))
        return {"FINISHED"}


class BBSV_OT_artist_exit(Operator):
    """Bring back the full Blender interface"""

    bl_idname = "bb_sv.artist_exit"
    bl_label = "Back to full Blender"

    def invoke(self, context, event):
        return context.window_manager.invoke_confirm(self, event)

    def execute(self, context):
        exit_artist_mode(context.window)
        return {"FINISHED"}


class BBSV_OT_switch_mode(Operator):
    """Switch between Easy Mode (one camera, one panel) and Artist Mode (cameras, locking, framing)"""

    bl_idname = "bb_sv.switch_mode"
    bl_label = "Switch Mode"

    easy: BoolProperty(default=True, options={"SKIP_SAVE"})

    def execute(self, context):
        window = context.window
        exit_artist_mode(window)
        if not enter_artist_mode(window, easy=self.easy):
            return {"CANCELLED"}
        _flash("%s Mode - save to open this way next time" % ("Easy" if self.easy else "Artist"), seconds=4)
        return {"FINISHED"}


class BBSV_OT_blocked(Operator):
    """Switched off in Artist Mode"""

    bl_idname = "bb_sv.blocked"
    bl_label = "Switched off in Artist Mode"
    bl_options = {"INTERNAL"}

    @classmethod
    def poll(cls, context):
        return _ARTIST["on"]       # when off, the key falls through to Blender as normal

    def invoke(self, context, event):
        # Blender merges add-on keymap items into the user keymap in REVERSE order, so a
        # blocker can sit in front of our own shortcut for the same key (F stopped starting
        # the walk in v2.4). Our shortcuts pass through; the next keymap item takes them.
        if _allowed_key(event):
            return {"PASS_THROUGH"}
        return {"FINISHED"}

    def execute(self, context):
        return {"FINISHED"}


class BBSV_OT_walk_hotkey(Operator):
    """Start walking (Artist Mode shortcut)"""

    bl_idname = "bb_sv.walk_hotkey"
    bl_label = "Walk"
    bl_options = {"INTERNAL"}

    @classmethod
    def poll(cls, context):
        return _ARTIST["on"] and context.area is not None and context.area.type == "VIEW_3D"

    def invoke(self, context, event):
        region = next((r for r in context.area.regions if r.type == "WINDOW"), None)
        if region is None:
            return {"CANCELLED"}
        with context.temp_override(region=region):
            return bpy.ops.bb_sv.flythrough("INVOKE_DEFAULT")


class BBSV_OT_camera_view_hotkey(Operator):
    """Toggle camera view (Artist Mode shortcut)"""

    bl_idname = "bb_sv.camera_view_hotkey"
    bl_label = "Camera View"
    bl_options = {"INTERNAL"}

    @classmethod
    def poll(cls, context):
        return _ARTIST["on"] and not _ARTIST.get("easy")

    def execute(self, context):
        return bpy.ops.bb_sv.camera_view()


class BBSV_OT_capture_hotkey(Operator):
    """Capture this shot (C, in Artist and Easy Mode)"""

    bl_idname = "bb_sv.capture_hotkey"
    bl_label = "Capture"
    bl_options = {"INTERNAL"}

    @classmethod
    def poll(cls, context):
        return _ARTIST["on"]

    def execute(self, context):
        # C does whatever that mode's Capture button does: the saved shot plus its
        # settings in Easy Mode, the instant grab in Artist Mode. Render Still stays
        # a deliberate click - it is the slow one.
        if _ARTIST.get("easy"):
            return bpy.ops.bb_sv.easy_capture()
        return bpy.ops.bb_sv.capture(kind="QUICK")


class BBSV_OT_lens_hotkey(Operator):
    """Pick a focal length with the number keys (Artist and Easy Mode shortcut)"""

    bl_idname = "bb_sv.lens_hotkey"
    bl_label = "Lens Preset"
    bl_options = {"INTERNAL"}

    mm: FloatProperty()

    @classmethod
    def poll(cls, context):
        return _ARTIST["on"]

    def execute(self, context):
        cam = _active_cam(context)
        if cam is None or _refuse_if_locked(self, cam):
            return {"CANCELLED"}
        cam.data.lens = self.mm
        _flash("%d mm" % round(self.mm))
        return {"FINISHED"}


# Keys: everything a stray press could do something with.
_LETTERS = [chr(c) for c in range(ord("A"), ord("Z") + 1)]
_DIGITS = ["ZERO", "ONE", "TWO", "THREE", "FOUR", "FIVE", "SIX", "SEVEN", "EIGHT", "NINE"]
_FKEYS = ["F%d" % i for i in range(1, 13)]
_OTHER = ["TAB", "DEL", "BACK_SPACE", "HOME", "END", "PAGE_UP", "PAGE_DOWN", "INSERT",
          "LEFT_ARROW", "RIGHT_ARROW", "UP_ARROW", "DOWN_ARROW", "SPACE", "ACCENT_GRAVE",
          "MINUS", "EQUAL", "PERIOD", "COMMA", "SLASH", "BACK_SLASH", "SEMI_COLON", "QUOTE",
          "LEFT_BRACKET", "RIGHT_BRACKET", "NUMPAD_PERIOD", "NUMPAD_SLASH", "NUMPAD_ASTERIX",
          "NUMPAD_MINUS", "NUMPAD_PLUS", "NUMPAD_ENTER"] + ["NUMPAD_%d" % i for i in range(10)]
# Mouse and trackpad navigation - the source of drift - plus the right-click menu
_MOUSE = ["MIDDLEMOUSE", "WHEELUPMOUSE", "WHEELDOWNMOUSE", "WHEELINMOUSE", "WHEELOUTMOUSE",
          "TRACKPADPAN", "TRACKPADZOOM", "MOUSEROTATE", "MOUSESMARTZOOM", "RIGHTMOUSE",
          "BUTTON4MOUSE", "BUTTON5MOUSE"]
# Keymaps checked, region level first, then area, then window
_KEYMAPS = (("3D View", "VIEW_3D"), ("Object Mode", "EMPTY"), ("Object Non-modal", "EMPTY"),
            ("3D View Generic", "VIEW_3D"), ("Frames", "EMPTY"), ("Screen", "EMPTY"),
            ("Window", "EMPTY"))
_addon_keymaps = []


def _allowed_key(event):
    t, cmd = event.type, event.ctrl or event.oskey
    if t in {"Z", "S"} and cmd and not event.alt:
        return True                                  # undo, redo, save
    if t == "F" and not (cmd or event.alt or event.shift):
        return True                                  # walk
    if t == "ACCENT_GRAVE" and event.shift:
        return True                                  # walk (Blender's own walk key)
    plain = not (cmd or event.alt or event.shift)
    if t == "C" and plain:
        return True                                  # capture
    if t in LENS_BY_KEY and plain:
        return True                                  # 1-6 lens presets
    if _ARTIST.get("easy"):
        return False                                 # Easy Mode: no camera list, no locking
    return t in {"ZERO", "NUMPAD_0", "RET", "NUMPAD_ENTER"} and not (cmd or event.alt)


def _register_keymaps():
    kc = bpy.context.window_manager.keyconfigs.addon
    if kc is None:           # background mode
        return
    for name, space in _KEYMAPS:
        km = kc.keymaps.new(name=name, space_type=space)
        # allowed first: undo, redo, save, walk, camera view
        for mod in ("ctrl", "oskey"):
            k = km.keymap_items.new("ed.undo", "Z", "PRESS", **{mod: True})
            _addon_keymaps.append((km, k))
            k = km.keymap_items.new("ed.redo", "Z", "PRESS", shift=True, **{mod: True})
            _addon_keymaps.append((km, k))
            k = km.keymap_items.new("wm.save_mainfile", "S", "PRESS", **{mod: True})
            _addon_keymaps.append((km, k))
        for key, shift in (("F", False), ("ACCENT_GRAVE", True)):
            k = km.keymap_items.new("bb_sv.walk_hotkey", key, "PRESS", shift=shift)
            _addon_keymaps.append((km, k))
        for key in ("NUMPAD_0", "ZERO"):
            k = km.keymap_items.new("bb_sv.camera_view_hotkey", key, "PRESS")
            _addon_keymaps.append((km, k))
        for key in ("RET", "NUMPAD_ENTER"):
            k = km.keymap_items.new("bb_sv.lock_hotkey", key, "PRESS")
            _addon_keymaps.append((km, k))
        k = km.keymap_items.new("bb_sv.capture_hotkey", "C", "PRESS")
        _addon_keymaps.append((km, k))
        for key, mm in LENS_BY_KEY.items():
            k = km.keymap_items.new("bb_sv.lens_hotkey", key, "PRESS")
            k.properties.mm = mm
            _addon_keymaps.append((km, k))
        # then the blockers, any modifier combination
        for key in _LETTERS + _DIGITS + _FKEYS + _OTHER + _MOUSE:
            k = km.keymap_items.new("bb_sv.blocked", key, "ANY", any=True)
            _addon_keymaps.append((km, k))


def _unregister_keymaps():
    for km, k in _addon_keymaps:
        try:
            km.keymap_items.remove(k)
        except Exception:
            pass
    _addon_keymaps.clear()


@persistent
def _on_load(_dummy):
    # a new file starts from a normal interface; its own flag decides the rest
    _ARTIST["on"] = False
    _ARTIST["easy"] = False
    _restore_foreign_panels()
    scene = bpy.context.scene
    if scene is None or not getattr(scene, "bb_sv", None):
        return
    for cam in (o for o in scene.objects if o.type == "CAMERA"):
        focus = cam.data.dof.focus_object
        if focus is not None and focus.name.endswith(FOCUS_SUFFIX) and not _is_hidden(cam):
            _parent_focus(cam)
    if scene.bb_sv.artist_mode or scene.bb_sv.easy_mode:
        bpy.app.timers.register(_enter_after_load, first_interval=0.5)


def _enter_after_load():
    wm = bpy.context.window_manager
    if wm and wm.windows:
        window = wm.windows[0]
        with bpy.context.temp_override(window=window):
            enter_artist_mode(window)
    return None


# ---------------------------------------------------------------------------
# Easy Mode: one camera, one panel. The viewport is the camera.
# ---------------------------------------------------------------------------

EASY_CAM = "BB View"
EASY_STATES = "bb_easy_states"       # scene property: JSON list of every captured shot


def easy_camera(scene, eye=None, quat=None):
    """The one camera Easy Mode drives, made at eye/quat (or the origin) if it is missing."""
    cam = scene.objects.get(EASY_CAM)
    if cam is None or cam.type != "CAMERA":
        data = bpy.data.cameras.new(EASY_CAM)
        data.lens = 35.0
        data.dof.use_dof = False
        data.dof.focus_distance = 3.0
        data.dof.aperture_fstop = 2.8
        data.show_passepartout, data.passepartout_alpha = True, 1.0    # nothing outside the frame
        cam = bpy.data.objects.new(EASY_CAM, data)
        _camera_collection(scene).objects.link(cam)
        cam.rotation_mode = "XYZ"
        if eye is not None:
            cam.location = eye
        if quat is not None:
            cam.rotation_euler = quat.to_euler("XYZ")
    _set_locked(cam, False)
    scene.camera = cam
    return cam


def _easy_setup(window, area):
    space = area.spaces.active
    rv3d = space.region_3d
    quat = rv3d.view_rotation.copy()
    eye = rv3d.view_location + quat @ Vector((0.0, 0.0, rv3d.view_distance))
    easy_camera(window.scene, eye, quat)
    _apply_look(space.shading, "FAST", window.scene)        # same reason as Artist Mode
    window.scene.bb_sv.look_now = "FAST"
    _apply_capture_size(window.scene)
    _scene_lighting(space.shading, window.scene.bb_sv.scene_lights)
    space.overlay.show_extras = False           # no light or camera outlines over the shot
    rv3d.view_perspective = "CAMERA"
    _fit_camera(window, area)
    # going full screen resizes the view a moment later: fit once more
    bpy.app.timers.register(lambda: _fit_camera(window, None), first_interval=0.4)


def _fit_camera(window, area):
    try:
        if area is None:
            area = max((a for a in window.screen.areas if a.type == "VIEW_3D"),
                       key=lambda a: a.width * a.height, default=None)
        if area is None:
            return None
        region = next(r for r in area.regions if r.type == "WINDOW")
        with bpy.context.temp_override(window=window, area=area, region=region):
            bpy.ops.view3d.view_center_camera()
    except Exception as e:           # a closed window or a changed screen: nothing to fit
        print("BB Set Viewer: could not fit the camera view:", e)
    return None


class BBSV_OT_easy_capture(Operator):
    """Save a picture of this view and the camera settings that made it, into the Captures folder"""

    bl_idname = "bb_sv.easy_capture"
    bl_label = "Capture"
    bl_options = {"REGISTER"}

    def execute(self, context):
        scene = context.scene
        cam = _active_cam(context)
        area = _view3d_area(context)
        if cam is None or area is None:
            return {"CANCELLED"}
        if bpy.app.is_job_running("SHADER_COMPILATION"):
            _flash("Materials are still loading - try again in a few seconds", seconds=4)
            return {"CANCELLED"}
        states = json.loads(scene.get(EASY_STATES, "[]"))
        n = len(states) + 1
        stamp = time.strftime("%Y-%m-%d %H%M%S")
        base = "Shot %02d - %dmm - %s" % (n, round(cam.data.lens), stamp)
        path = os.path.join(_capture_dir(), base + ".png")
        written = _capture_all(context, area, cam, path, keys=["look"])   # what you see
        if not written:
            return {"CANCELLED"}
        d = cam.data
        state = {
            "shot": n, "image": base + ".png", "saved": stamp,
            "file": os.path.basename(bpy.data.filepath) or "(unsaved)",
            "location": list(cam.matrix_world.translation),
            "rotation_euler": list(cam.matrix_world.to_euler("XYZ")),
            "lens_mm": d.lens, "sensor_width_mm": d.sensor_width,
            "depth_of_field": d.dof.use_dof, "focus_distance_m": d.dof.focus_distance,
            "f_stop": d.dof.aperture_fstop,
            "resolution": [scene.render.resolution_x, scene.render.resolution_y],
            "passes": written,
        }
        with open(os.path.join(_capture_dir(), base + ".json"), "w", encoding="utf-8") as f:
            json.dump(state, f, indent=2)
        states.append(state)
        scene[EASY_STATES] = json.dumps(states)
        _flash("Shot %02d saved (%d file(s) + camera settings)" % (n, len(written)), seconds=5)
        self.report({"INFO"}, "Captured %s" % path)
        return {"FINISHED"}


DEPTH_LOOKS = {"CLAY", "LINE", "COLOUR"}      # the drawing looks depth is useful against


def _multiply_with_depth(art_path, depth_path, out_path):
    """Shade a drawing with its own depth map: every pixel times the depth value there.

    With the depth map set to near-white (the default), near surfaces keep their brightness and
    far ones fall away - the drawing gains the distance it cannot show on its own."""
    try:
        import numpy as np
        art = bpy.data.images.load(art_path, check_existing=False)
    except Exception:
        return False
    depth = None
    try:
        depth = bpy.data.images.load(depth_path, check_existing=False)
        if tuple(art.size) != tuple(depth.size):
            return False
        a = np.empty(len(art.pixels), dtype=np.float32)
        art.pixels.foreach_get(a)
        d = np.empty(len(depth.pixels), dtype=np.float32)
        depth.pixels.foreach_get(d)
        a = a.reshape(-1, 4)
        d = d.reshape(-1, 4)
        shade = d[:, 0] * 0.2126 + d[:, 1] * 0.7152 + d[:, 2] * 0.0722
        a[:, 0] *= shade
        a[:, 1] *= shade
        a[:, 2] *= shade
        a[:, 3] = 1.0
        out = bpy.data.images.new("bb_multiplied", art.size[0], art.size[1])
        try:
            out.pixels.foreach_set(a.ravel())
            out.filepath_raw = out_path
            out.file_format = "PNG"
            out.save()
        finally:
            bpy.data.images.remove(out)
        return True
    except Exception:
        return False
    finally:
        bpy.data.images.remove(art)
        if depth is not None:
            bpy.data.images.remove(depth)


class BBSV_OT_easy_depth(Operator):
    """Render a depth map of this shot. It cannot be shown on screen, so it is its own button"""

    bl_idname = "bb_sv.easy_depth"
    bl_label = "Depth Map"
    bl_options = {"REGISTER"}

    def execute(self, context):
        cam = _active_cam(context)
        area = _view3d_area(context)
        if cam is None or area is None:
            return {"CANCELLED"}
        base = _capture_path(cam, "QUICK")
        path = _pass_path(base, "depth")
        _flash("Making the depth map...", seconds=3)
        if not _depth_image(context, area, cam, path):
            return {"CANCELLED"}
        _flash("Depth map saved: %s" % os.path.basename(path), seconds=5)
        self.report({"INFO"}, path)
        return {"FINISHED"}


class BBSV_OT_easy_depth_multiply(Operator):
    """Capture this view and multiply it with its own depth map, into one picture"""

    bl_idname = "bb_sv.easy_depth_multiply"
    bl_label = "Multiply with Depth Map"
    bl_options = {"REGISTER"}

    def execute(self, context):
        cam = _active_cam(context)
        area = _view3d_area(context)
        if cam is None or area is None:
            return {"CANCELLED"}
        if bpy.app.is_job_running("SHADER_COMPILATION"):
            _flash("Materials are still loading - try again in a few seconds", seconds=4)
            return {"CANCELLED"}
        look = context.scene.bb_sv.look_now
        base = _capture_path(cam, "QUICK")
        art = _pass_path(base, "view")
        depth = _pass_path(base, "depth")
        out = _pass_path(base, "depth multiplied")

        _flash("Capturing and rendering the depth map...", seconds=3)
        if not _grab_view(context, area, art):
            return {"CANCELLED"}
        if look == "LINE":
            _lift_lines(art, LINEART_CONTRAST)      # the drawing has to be ink on paper first
        made = _depth_image(context, area, cam, depth) and _multiply_with_depth(art, depth, out)
        for tmp in (art, depth):        # the separate button is there for anyone who wants these
            try:
                os.remove(tmp)
            except OSError:
                pass
        if not made:
            _flash("Could not make the depth-multiplied picture", seconds=4)
            return {"CANCELLED"}
        _flash("Saved: %s" % os.path.basename(out), seconds=5)
        self.report({"INFO"}, out)
        return {"FINISHED"}


class BBSV_PT_easy(Panel):
    bl_space_type = "VIEW_3D"
    bl_region_type = "UI"
    bl_category = "BB Set"
    bl_label = "Shot"
    bl_idname = "BBSV_PT_easy"
    bl_order = 1

    @classmethod
    def poll(cls, context):
        return _ARTIST.get("easy", False) and _active_cam(context) is not None

    def draw(self, context):
        lay = self.layout
        p = context.scene.bb_sv
        d = _active_cam(context).data

        row = lay.row(align=True)
        row.scale_y = 1.8
        row.operator("bb_sv.flythrough", text="Walk  (F)", icon="VIEW_PAN")
        sub = row.row(align=True)
        sub.scale_x = 0.55
        sub.prop(p, "speed", text="")
        _draw_play(lay, context)

        lay.separator()
        _draw_looks(lay, p, columns=2)      # in Easy Mode the looks ARE the choice
        col = lay.column(align=True)
        col.enabled = p.look_now in DEPTH_LOOKS
        col.operator("bb_sv.easy_depth", text="Generate Separate Depth Map", icon="MOD_FLUIDSIM")
        col.operator("bb_sv.easy_depth_multiply", text="Multiply with Depth Map",
                     icon="IMAGE_ZDEPTH")
        lay.separator()

        lay.prop(p, "lens_slider", slider=True)
        lay.prop(p, "dof_toggle")
        col = lay.column(align=True)
        col.enabled = d.dof.use_dof
        col.prop(p, "focus_pull", text="Focus Distance", slider=True)
        col.prop(p, "fstop_slider", slider=True)
        lay.separator()

        col = lay.column(align=True)
        col.scale_y = 2.0
        col.operator("bb_sv.easy_capture", text="Capture  (C)", icon="RENDER_STILL")
        lay.operator("bb_sv.open_captures", text="Open Captures Folder", icon="FILE_FOLDER",
                     emboss=False)


class BBSV_PT_easy_more(Panel):
    """Closed by default: the way back to full Blender, for whoever set the file up"""
    bl_space_type = "VIEW_3D"
    bl_region_type = "UI"
    bl_category = "BB Set"
    bl_label = "More"
    bl_idname = "BBSV_PT_easy_more"
    bl_order = 7
    bl_parent_id = "BBSV_PT_easy"
    bl_options = {"DEFAULT_CLOSED"}

    def draw(self, context):
        lay = self.layout
        r = context.scene.render
        lay.label(text="Capture size", icon="IMAGE_DATA")
        row = lay.row(align=True)
        row.prop(context.scene.bb_sv, "capture_size", expand=True)
        sub = lay.row()
        sub.scale_y = 0.6
        sub.label(text="Saving at %d x %d" % (r.resolution_x, r.resolution_y))
        lay.separator()
        self.layout.operator("bb_sv.tutorial", text="Show Tutorial", icon="HELP")
        self.layout.operator("bb_sv.switch_mode", text="Switch to Artist Mode", icon="OUTLINER_OB_CAMERA").easy = False
        self.layout.operator("bb_sv.artist_exit", text="Exit Easy Mode", icon="LOOP_BACK")


# ---------------------------------------------------------------------------
# Panels - each section can be switched off from the checklist
# ---------------------------------------------------------------------------

class _BBPanel:
    bl_space_type = "VIEW_3D"
    bl_region_type = "UI"
    bl_category = "BB Set"
    flag = ""

    @classmethod
    def poll(cls, context):
        # Outside Artist/Easy Mode the sidebar shows only the two enter buttons
        # (BBSV_PT_mode); the tools appear once you are in the mode (Aman, 4 Oct 2026).
        if not artist_on() or _ARTIST.get("easy"):
            return False
        return not cls.flag or getattr(context.scene.bb_sv, cls.flag)


# ---------------------------------------------------------------------------
# The mini map: a plan of the set in the corner of the viewport, with the cameras on it.
#
# Drawn straight to the viewport rather than built as an image in a panel, because that way it
# is live - the cameras and your own position move as you walk, with no refresh button. The
# plan itself is every object's footprint (its bounding box flattened to the floor), worked out
# once and cached: no render, no image file.
# ---------------------------------------------------------------------------

_MAP = {"key": None, "lines": None, "bounds": None, "handle": None}
MAP_SIZE = 220          # pixels at 1x; scaled by the interface scale below
MAP_PAD = 16
MAP_MIN_SIZE = 1.2      # metres: smaller things are clutter on a plan
MAP_MAX_SHAPES = 120    # the biggest footprints only, so the plan stays readable


def _map_plan(scene):
    """The set as a floor plan: the outline of every object big enough to be a wall, a counter
    or a piece of furniture. Cached until the set changes.

    Only the big things, and outlines rather than filled boxes - a set like Happy 4Eva has
    nearly 8,000 objects, and drawing all of them solid gives one grey blob that tells you
    nothing about where you are."""
    import numpy as np
    objs = [o for o in scene.objects
            if o.type == "MESH" and o.data is not None and len(o.data.polygons)]
    key = (scene.name, len(objs))
    if _MAP["key"] == key and _MAP["lines"] is not None:
        return _MAP["lines"], _MAP["bounds"]

    boxes, full = [], []
    for o in objs:
        m = np.array(o.matrix_world.to_4x4())
        pts = np.array([list(c) for c in o.bound_box])
        w = pts @ m[:3, :3].T + m[:3, 3]
        box = (w[:, 0].min(), w[:, 1].min(), w[:, 0].max(), w[:, 1].max())
        full.append(box)
        if (box[2] - box[0]) >= MAP_MIN_SIZE or (box[3] - box[1]) >= MAP_MIN_SIZE:
            boxes.append(box)
    if not full:
        _MAP.update(key=key, lines=None, bounds=None)
        return None, None
    if not boxes:
        boxes = full                      # a small set: draw everything rather than nothing
    b = np.array(boxes, dtype=np.float32)
    if len(b) > MAP_MAX_SHAPES:
        # Keep the biggest footprints: walls, counters, the furniture you navigate by. A room
        # full of identical chairs drawn in full is a hatch pattern, not a plan.
        w = b[:, 2] - b[:, 0]
        h = b[:, 3] - b[:, 1]
        # Rank by the SMALLER side, not by area: a curtain strip is long and paper-thin and
        # wins on area, then a hundred of them draw as a hatch pattern over the whole plan.
        b = b[np.argsort(-np.minimum(w, h))[:MAP_MAX_SHAPES]]
    x0, y0, x1, y1 = b[:, 0], b[:, 1], b[:, 2], b[:, 3]
    segs = np.empty((len(b) * 8, 2), dtype=np.float32)        # four edges, two points each
    corners = ((x0, y0, x1, y0), (x1, y0, x1, y1), (x1, y1, x0, y1), (x0, y1, x0, y0))
    for i, (ax, ay, bx, by) in enumerate(corners):
        segs[i * 2::8, 0], segs[i * 2::8, 1] = ax, ay
        segs[i * 2 + 1::8, 0], segs[i * 2 + 1::8, 1] = bx, by
    # Framed on the objects actually drawn. Using every object instead lets one stray prop
    # parked far from the set shrink the plan into a corner of the panel.
    bounds = (float(x0.min()), float(y0.min()), float(x1.max()), float(y1.max()))
    _MAP.update(key=key, lines=segs, bounds=bounds)
    return segs, bounds


def _map_draw():
    """POST_PIXEL: the plan, the cameras, and where you are standing."""
    try:
        context = bpy.context
        if not _ARTIST.get("on") or _ARTIST.get("easy"):
            return
        scene = context.scene
        if not getattr(scene, "bb_sv", None) or not scene.bb_sv.show_minimap:
            return
        region = context.region
        if region is None or region.type != "WINDOW":
            return
        lines, bounds = _map_plan(scene)
        if lines is None:
            return

        import gpu
        import numpy as np
        from gpu_extras.batch import batch_for_shader

        # POST_PIXEL coordinates are real device pixels, so on a Retina screen a raw 220 draws
        # at half the size it should. Everything here is multiplied by the interface scale.
        ui = getattr(context.preferences.system, "ui_scale", 1.0) or 1.0
        size, pad = MAP_SIZE * ui, MAP_PAD * ui
        minx, miny, maxx, maxy = bounds
        span = max(maxx - minx, maxy - miny) or 1.0
        scale = size / span
        ox = pad + (size - (maxx - minx) * scale) * 0.5
        oy = pad + (size - (maxy - miny) * scale) * 0.5

        def to_px(xy, clamp=False):
            out = np.empty_like(xy, dtype=np.float32)
            out[:, 0] = (xy[:, 0] - minx) * scale + ox
            out[:, 1] = (xy[:, 1] - miny) * scale + oy
            if clamp:          # a camera outside the plan is pinned to the edge, not lost
                out[:, 0] = np.clip(out[:, 0], pad + 4 * ui, pad + size - 4 * ui)
                out[:, 1] = np.clip(out[:, 1], pad + 4 * ui, pad + size - 4 * ui)
            return out

        shader = gpu.shader.from_builtin("UNIFORM_COLOR")
        gpu.state.blend_set("ALPHA")

        m = 6 * ui
        x0b, y0b, x1b, y1b = pad - m, pad - m, pad + size + m, pad + size + m
        frame = np.array([(x0b, y0b), (x1b, y0b), (x1b, y1b),
                          (x0b, y0b), (x1b, y1b), (x0b, y1b)], dtype=np.float32)
        shader.bind()
        shader.uniform_float("color", (0.04, 0.04, 0.05, 0.72))
        batch_for_shader(shader, "TRIS", {"pos": frame}).draw(shader)

        gpu.state.line_width_set(max(1.0, ui))
        shader.uniform_float("color", (0.72, 0.76, 0.82, 0.6))
        batch_for_shader(shader, "LINES", {"pos": to_px(lines)}).draw(shader)

        # where you are looking from
        rv3d = context.region_data
        if rv3d is not None:
            eye = rv3d.view_matrix.inverted().translation
            fwd = (rv3d.view_rotation @ Vector((0.0, 0.0, -1.0))).normalized()
            me = to_px(np.array([[eye.x, eye.y]], dtype=np.float32), clamp=True)[0]
            tip = me + np.array([fwd.x, fwd.y], dtype=np.float32) * 18.0 * ui
            shader.uniform_float("color", (1.0, 0.85, 0.2, 0.95))
            batch_for_shader(shader, "LINES", {"pos": [tuple(me), tuple(tip)]}).draw(shader)
            batch_for_shader(shader, "TRIS", {"pos": _map_dot(me, 3.8 * ui)}).draw(shader)

        for cam in _viewer_cams(scene):
            at = cam.matrix_world.translation
            look = (cam.matrix_world.to_3x3() @ Vector((0.0, 0.0, -1.0))).normalized()
            c = to_px(np.array([[at.x, at.y]], dtype=np.float32), clamp=True)[0]
            tip = c + np.array([look.x, look.y], dtype=np.float32) * 15.0 * ui
            active = scene.camera is cam
            shader.uniform_float("color", (0.25, 0.8, 1.0, 1.0) if active else (0.8, 0.8, 0.85, 0.8))
            batch_for_shader(shader, "LINES", {"pos": [tuple(c), tuple(tip)]}).draw(shader)
            batch_for_shader(shader, "TRIS", {"pos": _map_dot(c, (4.6 if active else 3.2) * ui)}).draw(shader)

        gpu.state.line_width_set(1.0)
        gpu.state.blend_set("NONE")
    except Exception:
        pass            # a HUD must never take the viewport down with it


def _map_dot(centre, r):
    import math
    import numpy as np
    pts = []
    for i in range(8):
        a0 = i * math.pi / 4.0
        a1 = (i + 1) * math.pi / 4.0
        pts += [tuple(centre),
                (centre[0] + math.cos(a0) * r, centre[1] + math.sin(a0) * r),
                (centre[0] + math.cos(a1) * r, centre[1] + math.sin(a1) * r)]
    return np.array(pts, dtype=np.float32)


def _map_enable(on):
    if on and _MAP["handle"] is None:
        _MAP["handle"] = bpy.types.SpaceView3D.draw_handler_add(
            _map_draw, (), "WINDOW", "POST_PIXEL")
    elif not on and _MAP["handle"] is not None:
        bpy.types.SpaceView3D.draw_handler_remove(_MAP["handle"], "WINDOW")
        _MAP["handle"] = None


class BBSV_OT_refresh_map(Operator):
    """Rebuild the mini map after the set has changed"""

    bl_idname = "bb_sv.refresh_map"
    bl_label = "Refresh Map"

    def execute(self, context):
        _MAP["key"] = None
        for a in context.screen.areas:
            a.tag_redraw()
        return {"FINISHED"}


class BBSV_PT_mode(Panel):
    """Always first, always open: which mode you are in and how to leave it."""

    bl_space_type = "VIEW_3D"
    bl_region_type = "UI"
    bl_category = "BB Set"
    bl_label = "BB Set"
    bl_idname = "BBSV_PT_mode"
    bl_order = 0

    def draw(self, context):
        col = self.layout.column(align=True)
        col.scale_y = 1.5
        if not artist_on():
            col.operator("bb_sv.artist_enter", text="Enter Artist Mode",
                         icon="FULLSCREEN_ENTER").easy = False
            col.operator("bb_sv.artist_enter", text="Enter Easy Mode",
                         icon="VIEW_CAMERA").easy = True
        elif _ARTIST.get("easy"):
            col.operator("bb_sv.switch_mode", text="Enter Artist Mode",
                         icon="FULLSCREEN_ENTER").easy = False
            col.operator("bb_sv.artist_exit", text="Exit to Blender", icon="LOOP_BACK")
        else:
            col.operator("bb_sv.switch_mode", text="Enter Easy Mode",
                         icon="VIEW_CAMERA").easy = True
            col.operator("bb_sv.artist_exit", text="Exit to Blender", icon="LOOP_BACK")


class BBSV_PT_shot(_BBPanel, Panel):
    """Everything you touch while working a shot: move, look, capture."""

    bl_label = "Shot"
    bl_idname = "BBSV_PT_shot"
    bl_order = 2

    def draw(self, context):
        lay = self.layout
        p = context.scene.bb_sv
        row = lay.row(align=True)
        row.scale_y = 1.6
        row.operator("bb_sv.flythrough", text="Walk  (F)", icon="VIEW_PAN")
        sub = row.row(align=True)
        sub.scale_x = 0.55
        sub.prop(p, "speed", text="")
        _draw_play(lay, context)

        lay.separator()
        _draw_looks(lay, p)

        lay.separator()
        cam = _active_cam(context)
        col = lay.column(align=True)
        col.enabled = cam is not None
        col.scale_y = 1.6
        col.operator("bb_sv.capture", text="Capture  (C)", icon="RENDER_STILL").kind = "QUICK"
        _draw_passes(lay, p)
        if cam is None:
            lay.label(text="Add a camera to capture its shot", icon="INFO")
        lay.operator("bb_sv.open_captures", text="Open Captures Folder", icon="FILE_FOLDER",
                     emboss=False)


class BBSV_PT_cameras(_BBPanel, Panel):
    bl_label = "Cameras"
    bl_idname = "BBSV_PT_cameras"
    bl_order = 3
    flag = "show_cameras"

    def draw(self, context):
        lay = self.layout
        scene = context.scene
        p = scene.bb_sv
        cams = _viewer_cams(scene)

        if not cams:
            lay.label(text="No cameras yet - walk to a view, then add one", icon="INFO")
        else:
            col = lay.box().column(align=True)
            for cam in cams:
                active = scene.camera is cam
                locked = _is_locked(cam)
                row = col.row(align=True)
                op = row.operator("bb_sv.look_through", text=cam.name,
                                  icon="OUTLINER_OB_CAMERA" if active else "CAMERA_DATA",
                                  depress=active)
                op.name = cam.name
                row.operator("bb_sv.lock_camera", text="", icon="LOCKED" if locked else "UNLOCKED",
                             depress=locked).name = cam.name
                row.operator("bb_sv.rename_camera", text="", icon="SORTALPHA").name = cam.name
                sub = row.row(align=True)
                sub.enabled = not locked
                sub.operator("bb_sv.delete_camera", text="", icon="X").name = cam.name

        row = lay.row(align=True)
        row.scale_y = 1.3
        row.operator("bb_sv.add_camera", icon="ADD").add_focus = p.focus_on_add
        row.prop(p, "focus_on_add", text="", icon="PIVOT_CURSOR")

        if _active_cam(context):
            area = _view3d_area(context)
            through = area and area.spaces.active.region_3d.view_perspective == "CAMERA"
            lay.operator("bb_sv.camera_view", depress=bool(through),
                         text="Looking Through Camera (0)" if through else "Look Through Camera (0)",
                         icon="VIEW_CAMERA")
        lay.separator()
        row = lay.row(align=True)
        row.prop(p, "show_minimap", toggle=True, icon="VIEW_ORTHO")
        if p.show_minimap:
            row.operator("bb_sv.refresh_map", text="", icon="FILE_REFRESH")
        if any(o.type == "CAMERA" for o in scene.objects):
            lay.separator()
            lay.operator("bb_sv.clear_cameras", text="Clear All Cameras", icon="TRASH")


def _locked_banner(layout, cam):
    """Show the lock state; return a column that is greyed out while locked."""
    if _is_locked(cam):
        row = layout.row(align=True)
        row.label(text="%s is locked" % cam.name, icon="LOCKED")
        row.operator("bb_sv.lock_camera", text="Unlock", icon="UNLOCKED").name = cam.name
    col = layout.column()
    col.enabled = not _is_locked(cam)
    return col


class BBSV_PT_camera_settings(_BBPanel, Panel):
    """Lens, focus and the small camera moves, in one place."""

    bl_label = "Camera Settings"
    bl_idname = "BBSV_PT_camera_settings"
    bl_order = 4
    flag = "show_lens"

    @classmethod
    def poll(cls, context):
        return super().poll(context) and _active_cam(context) is not None

    def draw(self, context):
        lay = _locked_banner(self.layout, _active_cam(context))
        p = context.scene.bb_sv
        data = _active_cam(context).data

        row = lay.row(align=True)
        for mm in LENS_PRESETS:
            row.operator("bb_sv.set_lens", text=str(mm), depress=abs(data.lens - mm) < 0.5).mm = mm
        sub = lay.row()
        sub.scale_y = 0.6
        sub.label(text="Number keys 1-%d pick these, walking or not" % len(LENS_PRESETS))
        lay.prop(data, "lens", text="Focal Length")

        lay.separator()
        if data.dof.focus_object is None:
            lay.operator("bb_sv.add_focus", icon="ADD")
        else:
            lay.label(text="Focus point: %s" % data.dof.focus_object.name, icon="PIVOT_CURSOR")
            lay.operator("bb_sv.focus_here", icon="RESTRICT_SELECT_OFF")
            lay.prop(p, "focus_pull", slider=True)
        lay.prop(data.dof, "use_dof", text="Depth of Field")
        col = lay.column(align=True)
        col.enabled = data.dof.use_dof        # greyed out, not hidden: the settings stay visible
        col.prop(data.dof, "aperture_fstop", text="F-Stop")
        if data.dof.focus_object is None:
            col.prop(data.dof, "focus_distance", text="Focus Distance")

        lay.separator()
        col = lay.column(align=True)
        col.prop(p, "tilt", text="Roll Step")
        row = col.row(align=True)
        op = row.operator("bb_sv.nudge", text="Roll Left")
        op.axis, op.amount, op.kind = "Y", 1.0, "TILT"
        row.operator("bb_sv.level_horizon", text="Reset Horizon", icon="ALIGN_JUSTIFY")
        op = row.operator("bb_sv.nudge", text="Roll Right")
        op.axis, op.amount, op.kind = "Y", -1.0, "TILT"


class BBSV_PT_parts(_BBPanel, Panel):
    bl_label = "Show / Hide Set Parts"
    bl_idname = "BBSV_PT_parts"
    bl_order = 5
    flag = "show_parts"

    def draw(self, context):
        lay = self.layout
        root = context.view_layer.layer_collection
        for top in _set_parts(context.scene):
            lc = _layer_coll(root, top.name)
            if lc is None:
                continue
            col = lay.column(align=True)
            op = col.operator("bb_sv.toggle_part", text=top.name,
                              icon="HIDE_ON" if lc.hide_viewport else "HIDE_OFF",
                              depress=not lc.hide_viewport)
            op.name = top.name
            if not lc.hide_viewport and top.children:
                flow = col.grid_flow(columns=2, align=True)
                for ch in sorted(top.children, key=lambda c: c.name):
                    clc = _layer_coll(root, ch.name)
                    if clc is None:
                        continue
                    op = flow.operator("bb_sv.toggle_part", text=ch.name,
                                       icon="HIDE_ON" if clc.hide_viewport else "HIDE_OFF",
                                       depress=not clc.hide_viewport)
                    op.name = ch.name


class BBSV_PT_settings(_BBPanel, Panel):
    """The things you set once and forget: framing guides, the slower walk settings, which
    panels are on, the tutorial. Closed by default so the panel above it stays short."""

    bl_label = "Settings"
    bl_idname = "BBSV_PT_settings"
    bl_order = 6
    bl_options = {"DEFAULT_CLOSED"}

    def draw(self, context):
        lay = self.layout
        p = context.scene.bb_sv
        r = context.scene.render
        cam = _active_cam(context)

        lay.label(text="Capture size", icon="IMAGE_DATA")
        row = lay.row(align=True)
        row.prop(p, "capture_size", expand=True)
        sub = lay.row()
        sub.scale_y = 0.6
        sub.label(text="Saving at %d x %d" % (r.resolution_x, r.resolution_y))

        lay.separator()
        lay.label(text="Frame shape", icon="IMAGE_PLANE")
        row = lay.row(align=True)
        for label, w, h in ASPECTS:
            op = row.operator("bb_sv.set_aspect", text=label,
                              depress=(r.resolution_x, r.resolution_y) == (w, h))
            op.width, op.height = w, h
        if cam:
            col = lay.column(align=True)
            col.prop(cam.data, "show_composition_thirds", text="Rule of Thirds")
            col.prop(cam.data, "show_composition_center", text="Centre Cross")
            col.prop(cam.data, "show_passepartout", text="Darken Outside Frame")
            col = lay.column(align=True)
            col.prop(cam.data, "clip_start", text="Clip Near")
            col.prop(cam.data, "clip_end", text="Clip Far")

        lay.separator()
        lay.label(text="Walking", icon="VIEW_PAN")
        col = lay.column(align=True)
        col.prop(p, "sprint")
        col.prop(p, "sensitivity")
        col.prop(p, "invert_y")
        col.prop(p, "fly_target")
        col = lay.column(align=True)
        col.operator("bb_sv.stand_on_floor", icon="TRIA_DOWN_BAR")
        col.prop(p, "eye_height")

        if cam:
            lay.separator()
            lay.label(text="Move the camera", icon="ORIENTATION_GIMBAL")
            col = lay.column(align=True)
            col.prop(p, "nudge")
            grid = col.grid_flow(row_major=True, columns=2, align=True)
            for label, axis, amt, icon in (
                ("Left", "X", -1.0, "TRIA_LEFT"), ("Right", "X", 1.0, "TRIA_RIGHT"),
                ("Down", "Y", -1.0, "TRIA_DOWN"), ("Up", "Y", 1.0, "TRIA_UP"),
                ("Back", "Z", 1.0, "SORT_DESC"), ("Forward", "Z", -1.0, "SORT_ASC"),
            ):
                op = grid.operator("bb_sv.nudge", text=label, icon=icon)
                op.axis, op.amount, op.kind = axis, amt, "MOVE"

        lay.separator()
        lay.label(text="Panels", icon="MENU_PANEL")
        col = lay.column(align=True)
        for key in ("show_cameras", "show_lens", "show_parts"):
            col.prop(p, key)
        lay.operator("bb_sv.tutorial", text="Show Tutorial", icon="HELP")


CLASSES = (
    BBSV_Props,
    BBSV_OT_flythrough,
    BBSV_OT_look_through,
    BBSV_OT_nudge,
    BBSV_OT_add_camera,
    BBSV_OT_add_focus,
    BBSV_OT_focus_here,
    BBSV_OT_stand_on_floor,
    BBSV_OT_set_lens,
    BBSV_OT_set_aspect,
    BBSV_OT_level_horizon,
    BBSV_OT_camera_view,
    BBSV_OT_set_look,
    BBSV_OT_toggle_part,
    BBSV_OT_artist_enter,
    BBSV_OT_artist_exit,
    BBSV_OT_switch_mode,
    BBSV_OT_blocked,
    BBSV_OT_walk_hotkey,
    BBSV_OT_camera_view_hotkey,
    BBSV_OT_capture_hotkey,
    BBSV_OT_lens_hotkey,
    BBSV_OT_lock_camera,
    BBSV_OT_lock_hotkey,
    BBSV_OT_rename_camera,
    BBSV_OT_delete_camera,
    BBSV_OT_capture,
    BBSV_OT_play,
    BBSV_OT_rewind,
    BBSV_OT_clear_cameras,
    BBSV_OT_refresh_map,
    BBSV_OT_open_captures,
    BBSV_OT_tutorial,
    BBSV_OT_easy_capture,
    BBSV_OT_easy_depth,
    BBSV_OT_easy_depth_multiply,
    BBSV_PT_easy,
    BBSV_PT_easy_more,
    BBSV_PT_mode,
    BBSV_PT_shot,
    BBSV_PT_cameras,
    BBSV_PT_camera_settings,
    BBSV_PT_parts,
    BBSV_PT_settings,
)


_OWNS = {"registered": False}      # this copy registered the tools (another copy may have)


def register():
    # One copy only: the extension, an old single-file install, or the copy embedded in a set
    # file. Whichever loads second stands aside instead of failing on duplicate classes.
    if hasattr(bpy.types.Scene, "bb_sv"):
        print("BB Set Viewer: another copy is already active - this one stays idle")
        return
    _OWNS["registered"] = True
    for c in CLASSES:
        bpy.utils.register_class(c)
    bpy.types.Scene.bb_sv = PointerProperty(type=BBSV_Props)
    _register_keymaps()
    if _on_load not in bpy.app.handlers.load_post:
        bpy.app.handlers.load_post.append(_on_load)
    _OVERLAY["handle"] = bpy.types.SpaceView3D.draw_handler_add(_draw_overlay, (), "WINDOW", "POST_PIXEL")


def unregister():
    if not _OWNS["registered"]:
        return
    _OWNS["registered"] = False
    if _OVERLAY["handle"] is not None:
        bpy.types.SpaceView3D.draw_handler_remove(_OVERLAY["handle"], "WINDOW")
        _OVERLAY["handle"] = None
    _map_enable(False)                 # the mini map draws from its own handler
    if _on_load in bpy.app.handlers.load_post:
        bpy.app.handlers.load_post.remove(_on_load)
    _ARTIST["on"] = False
    _restore_foreign_panels()
    _unregister_keymaps()
    del bpy.types.Scene.bb_sv
    for c in reversed(CLASSES):
        bpy.utils.unregister_class(c)


# Safe to run twice: an installed copy and a copy embedded in the .blend never both register.
if __name__ == "__main__" and not hasattr(bpy.types.Scene, "bb_sv"):
    register()
