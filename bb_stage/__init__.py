"""BB Stage — staging & blocking previz for Beta Builder sets (View3D > Sidebar > BB Stage).

Two worlds, one plan: the finished 3D set (SET) and the grey-studio blockout (STUDIO), with the
staged action (STAGE: character pegs, props, cameras, beats) on top. Each studio setup lives in its
own scene ("STG <label>") inside the set's .blend; the master set scene stays untouched.

Modes: EASY (direction team — characters, beats, cameras) / ARTIST (everything: staging builder,
studio kit, stand-ins, outputs, settings). Separate from BB Set Viewer for now (Aman, 4 Oct 2026).
"""

import json
import math
import os
import re
from contextlib import contextmanager

import bpy
import bmesh
from bpy.app.handlers import persistent
from mathutils import Matrix, Quaternion, Vector

bl_info = {
    "name": "BB Stage",
    "author": "Beta Builder",
    "version": (0, 9, 1),
    "blender": (5, 0, 0),
    "location": "View3D > Sidebar > BB Stage",
    "category": "3D View",
}

STG_PREFIX = "STG "
LAYER_KEY = "bb_st_layer"          # on collections: SET / STUDIO / STAGE
ROLE_KEY = "bb_st_role"            # on objects: char / prop / studio / boundary / cam
SOURCE_KEY = "bb_st_source"        # stand-in: name of the set object it stands in for
STANDIN_KEY = "bb_st_standin"      # prop flag: placeholder that must never appear in outputs
DT_BACKUP_KEY = "bb_st_dt0"        # ghost mode: original display_type backup
LOCK_KEY = "bb_st_locked"

PEG_COLORS = [
    (0.90, 0.25, 0.20, 1.0), (0.20, 0.55, 0.95, 1.0), (0.25, 0.75, 0.30, 1.0),
    (0.95, 0.75, 0.10, 1.0), (0.70, 0.35, 0.90, 1.0), (0.95, 0.45, 0.15, 1.0),
    (0.15, 0.75, 0.75, 1.0), (0.90, 0.40, 0.65, 1.0), (0.55, 0.60, 0.25, 1.0),
    (0.45, 0.45, 0.95, 1.0),
]
# studio colour code (Aman, 5 Oct 2026): the studio's own floor and walls light white, the
# surface pieces built on it (kit, stand-ins) dark grey, contact props magenta
SHELL_WHITE = (0.90, 0.90, 0.88, 1.0)
KIT_GREY = (0.30, 0.30, 0.32, 1.0)
PROP_MAGENTA = (0.85, 0.18, 0.75, 1.0)
STANDIN_PINK = (1.0, 0.62, 0.92, 1.0)
STUDIO_GREY = KIT_GREY
SHELL_KEY = "bb_st_shell"          # studio floor / default walls: rebuilt from the settings
GHOST_RGBA = (0.55, 0.62, 0.72, 0.28)

LEVEL_ITEMS = [('GROUND', "Ground floor", "Work on the ground floor — upper floor and roof hidden"),
               ('L1', "Upper floor", "Work on the upper floor — only the roof hidden"),
               ('ALL', "All levels", "Show the whole building")]

KIT_PIECES = {
    # name: (x, y, z) metres — matched to what the grey studio actually owns
    'FLAT': ("Wall flat", 1.22, 0.06, 2.44),
    'DOOR': ("Door flat", 1.00, 0.06, 2.10),
    'TABLE': ("Table", 1.80, 0.75, 0.74),
    'BOX': ("Box", 0.50, 0.50, 0.50),
    'CHAIR': ("Chair", 0.45, 0.45, 0.45),
    'CUBE': ("Custom block", 1.00, 1.00, 1.00),
}


# ------------------------------------------------------------------ helpers

WS_NAME = "BB Stage"
CEIL_COLL = "Ceilings — hidden in top view"
L1_COLL = "Upper floor — Level 1"
SUB_KEY = "bb_st_sub"              # on STAGE sub-collections: Characters / Props / Cameras
HOME_KEY = "bb_st_home"            # set object moved into a level collection: where it came from
TINT_KEY = "bb_st_c0"              # ghost tint: the object's own colour, restored before saving
DATA_VERSION = 8
EYE_HEIGHT = 1.6
_QUIET = {"floor": False, "beats": False}     # True while an upgrade sets play_level
WORLD_ITEMS = [('STUDIO', "Studio", "The grey studio blockout"),
               ('SET', "Set", "The finished 3D location"),
               ('GHOST', "Ghost", "Studio solid, the set faded behind it")]
SHADING_ITEMS = [('SOLID', "Solid", "Flat clay colours"),
                 ('MATERIAL', "Preview", "Material preview"),
                 ('RENDERED', "Render", "Full render (slow on big sets)")]
SET_TYPES = {'MESH', 'CURVE', 'SURFACE', 'META', 'FONT', 'LIGHT', 'VOLUME', 'POINTCLOUD',
             'CURVES', 'GREASEPENCIL', 'GPENCIL', 'LIGHT_PROBE'}


def coll_objects(coll):
    """Objects in coll and its child collections. Never Collection.all_objects: Blender 5.2.1
    keeps a parent collection's object cache across undo and hands back freed objects
    (Ctrl+Z after Add Character crashed Blender)."""
    seen, out = set(), []
    for c in [coll] + list(coll.children_recursive):
        for ob in c.objects:
            p = ob.as_pointer()
            if p not in seen:
                seen.add(p)
                out.append(ob)
    return out


def is_staging(scene):
    return scene is not None and scene.name.startswith(STG_PREFIX)


def staging_label(scene):
    return scene.name[len(STG_PREFIX):] if is_staging(scene) else scene.name


def stagings():
    return [s for s in bpy.data.scenes if is_staging(s)]


def master_scene():
    for s in bpy.data.scenes:
        if not s.name.startswith(STG_PREFIX):
            return s
    return bpy.data.scenes[0] if len(bpy.data.scenes) else None


def fstate():
    """File-level state (Stage Mode on/off, Easy/Artist, floor heights, level collections)
    lives on the set scene, so every staging reads the same values."""
    m = master_scene()
    return getattr(m, "bb_st", None) if m is not None else None


def _root_child(scene, coll):
    return coll is not None and scene.collection.children.get(coll.name) == coll


def layer_colls(scene, kind):
    """The staging's SET / STUDIO / STAGE root collection: pointer first, tag fallback."""
    st = getattr(scene, "bb_st", None)
    attr = {"SET": "set_coll", "STUDIO": "studio_coll", "STAGE": "stage_coll"}[kind]
    c = getattr(st, attr, None) if st is not None else None
    if _root_child(scene, c):
        return [c]
    return [c for c in scene.collection.children if c.get(LAYER_KEY) == kind][:1]


def sub_coll(scene, kind, child):
    st = getattr(scene, "bb_st", None)
    attr = {"Characters": "chars_coll", "Props": "props_coll", "Cameras": "cams_coll"}.get(child)
    roots = layer_colls(scene, kind)
    c = getattr(st, attr, None) if (st is not None and attr) else None
    if c is not None and roots and roots[0].children.get(c.name) == c:
        return c
    for r in roots:
        for ch in r.children:
            if ch.get(SUB_KEY) == child or ch.name.split(" · ")[0] == child:
                return ch
    return None


def stage_objects(scene, roles=("char", "prop")):
    out = []
    for c in layer_colls(scene, "STAGE"):
        for ob in coll_objects(c):
            if ob.get(ROLE_KEY) in roles:
                out.append(ob)
    return out


def boundary_of(scene):
    st = getattr(scene, "bb_st", None)
    b = st.boundary if st is not None else None
    if b is not None and scene.objects.get(b.name) == b:
        return b
    for c in layer_colls(scene, "STUDIO"):
        for ob in c.objects:
            if ob.get(ROLE_KEY) == "boundary":
                return ob
    return None


def migrate_staging(scene):
    """Fill the robust pointers for stagings made by older versions (tags and names)."""
    if not is_staging(scene):
        return
    st = scene.bb_st
    for kind, attr in (("SET", "set_coll"), ("STUDIO", "studio_coll"), ("STAGE", "stage_coll")):
        if not _root_child(scene, getattr(st, attr)):
            found = [c for c in scene.collection.children if c.get(LAYER_KEY) == kind]
            if found:
                setattr(st, attr, found[0])
    for child, attr in (("Characters", "chars_coll"), ("Props", "props_coll"), ("Cameras", "cams_coll")):
        c = sub_coll(scene, "STAGE", child)
        if c is not None:
            if c.get(SUB_KEY) != child:
                c[SUB_KEY] = child
            if getattr(st, attr) != c:
                setattr(st, attr, c)
    b = boundary_of(scene)
    if b is not None and st.boundary != b:
        st.boundary = b
    for c in layer_colls(scene, "SET"):
        if not c.hide_select:
            c.hide_select = True
    upgrade_beats(scene)
    if not st.shell_built and boundary_of(scene) is not None and layer_colls(scene, "STUDIO"):
        build_studio_shell(scene)
    if st.data_version < DATA_VERSION:
        _QUIET["floor"] = True          # an upgrade must not re-detect the floor and move things
        try:
            st.play_level = st.active_level
        finally:
            _QUIET["floor"] = False
        st.data_version = DATA_VERSION


def find_layer_collection(layer_coll, coll):
    if layer_coll is None:
        return None
    if layer_coll.collection == coll:
        return layer_coll
    for ch in layer_coll.children:
        r = find_layer_collection(ch, coll)
        if r:
            return r
    return None


def channelbag_fcurves(action):
    fcs = []
    for layer in action.layers:
        for strip in layer.strips:
            for cb in strip.channelbags:
                fcs.extend(cb.fcurves)
    return fcs


def ensure_peg_material():
    mat = bpy.data.materials.get("BB Stage Peg")
    if mat is None:
        mat = bpy.data.materials.new("BB Stage Peg")
        mat.use_nodes = True
        nt = mat.node_tree
        bsdf = next((n for n in nt.nodes if n.type == 'BSDF_PRINCIPLED'), None)
        info = nt.nodes.new('ShaderNodeObjectInfo')
        if bsdf:
            nt.links.new(info.outputs['Color'], bsdf.inputs['Base Color'])
    return mat


def ensure_flat_material(name="BB Stage Grey", color=KIT_GREY):
    mat = bpy.data.materials.get(name)
    if mat is None:
        mat = bpy.data.materials.new(name)
        mat.use_nodes = True
        nt = mat.node_tree
        bsdf = next((n for n in nt.nodes if n.type == 'BSDF_PRINCIPLED'), None)
        if bsdf:
            bsdf.inputs['Base Color'].default_value = color
            bsdf.inputs['Roughness'].default_value = 0.9
        mat.diffuse_color = color
    return mat


def ensure_grey_material():
    return ensure_flat_material("BB Stage Grey", KIT_GREY)


def stage_dir(scene):
    base = os.path.dirname(bpy.data.filepath) or os.path.expanduser("~")
    d = os.path.join(base, "Stage", staging_label(scene))
    os.makedirs(d, exist_ok=True)
    return d


def view3d_area(context, biggest=True):
    areas = [a for a in context.screen.areas if a.type == 'VIEW_3D']
    if not areas:
        return None
    return max(areas, key=lambda a: a.width * a.height) if biggest else areas[0]


# ------------------------------------------------------------------ mesh builders

def _box_bmesh(bm, size, offset=(0, 0, 0)):
    mat = Matrix.Translation(Vector(offset)) @ Matrix.Diagonal(Vector(size) / 2).to_4x4()
    bmesh.ops.create_cube(bm, size=2.0, matrix=mat)


def build_box_object(name, size, location=(0, 0, 0), color=KIT_GREY, role="studio"):
    bm = bmesh.new()
    _box_bmesh(bm, size, offset=(0, 0, size[2] / 2))   # origin at floor
    me = bpy.data.meshes.new(name)
    bm.to_mesh(me)
    bm.free()
    ob = bpy.data.objects.new(name, me)
    ob.location = location
    ob.color = color
    ob[ROLE_KEY] = role
    if tuple(color) == SHELL_WHITE:
        me.materials.append(ensure_flat_material("BB Stage Studio White", SHELL_WHITE))
    else:
        me.materials.append(ensure_grey_material())
    return ob


def peg_material(ob):
    """Per-peg material so the colour shows in material-shaded panes and renders too."""
    name = f"BB Peg · {ob.name}"
    mat = bpy.data.materials.get(name)
    if mat is None or (mat.users and mat not in list(ob.data.materials)):
        mat = bpy.data.materials.new(name)     # never share another peg's material
    mat.use_nodes = True
    nt = mat.node_tree
    bsdf = next((n for n in nt.nodes if n.type == 'BSDF_PRINCIPLED'), None)
    if bsdf:
        bsdf.inputs['Base Color'].default_value = tuple(ob.color)
    mat.diffuse_color = tuple(ob.color)
    ob.data.materials.clear()
    ob.data.materials.append(mat)
    return mat


def _rgba_differs(a, b):
    """Colours are float32 in Blender: never compare them to Python floats with ==."""
    return any(abs(x - y) > 1e-4 for x, y in zip(a, b))


def _peg_mat(ob):
    return ob.data.materials[0] if (ob.type == 'MESH' and len(ob.data.materials)) else None


def peg_colors_stale(scene):
    for ob in stage_objects(scene, roles=("char", "prop")):
        mat = _peg_mat(ob)
        if ob.type == 'MESH' and (mat is None or mat.users > 1 or _rgba_differs(mat.diffuse_color, ob.color)):
            return True
    return False


def sync_peg_colors(scene):
    """Every peg and prop owns a material carrying its colour (camera panes draw material
    colour). A Shift+D copy shares its original's material until this gives it its own."""
    for ob in stage_objects(scene, roles=("char", "prop")):
        if ob.type != 'MESH':
            continue
        if ob.data.users > 1:
            ob.data = ob.data.copy()
        mat = _peg_mat(ob)
        if mat is None or mat.users > 1 or not mat.name.startswith("BB Peg"):
            peg_material(ob)            # writes the colour too
            continue
        if _rgba_differs(mat.diffuse_color, ob.color):
            mat.diffuse_color = tuple(ob.color)
        bsdf = next((n for n in mat.node_tree.nodes if n.type == 'BSDF_PRINCIPLED'), None) if mat.use_nodes else None
        if bsdf and _rgba_differs(bsdf.inputs['Base Color'].default_value, ob.color):
            bsdf.inputs['Base Color'].default_value = tuple(ob.color)


def build_peg_object(name, height=1.75, color=(0.8, 0.2, 0.2, 1.0)):
    bm = bmesh.new()
    r = 0.13 * height / 1.75                 # body radius
    body_h = height * 0.80
    head_r = height * 0.075
    # base disc + direction wedge, so the character reads as a solid dot in the plan view
    mat = Matrix.Translation((0, 0, 0.012)) @ Matrix.Diagonal((0.34, 0.34, 0.012)).to_4x4()
    bmesh.ops.create_cone(bm, cap_ends=True, segments=20, radius1=1, radius2=1, depth=2, matrix=mat)
    mat = Matrix.Translation((0, 0.42, 0.012)) @ Matrix.Diagonal((0.10, 0.12, 0.012)).to_4x4()
    bmesh.ops.create_cone(bm, cap_ends=True, segments=3, radius1=1, radius2=0.15, depth=2, matrix=mat)
    # body: cylinder from floor to shoulders
    mat = Matrix.Translation((0, 0, body_h / 2)) @ Matrix.Diagonal((r, r, body_h / 2)).to_4x4()
    bmesh.ops.create_cone(bm, cap_ends=True, segments=16, radius1=1, radius2=0.85, depth=2, matrix=mat)
    # head
    mat = Matrix.Translation((0, 0, body_h + head_r * 1.1)) @ Matrix.Scale(head_r, 4)
    bmesh.ops.create_uvsphere(bm, u_segments=12, v_segments=8, radius=1, matrix=mat)
    # nose: cone pointing +Y at head height
    mat = (Matrix.Translation((0, head_r * 1.35, body_h + head_r * 1.1))
           @ Matrix.Rotation(-math.pi / 2, 4, 'X')
           @ Matrix.Diagonal((head_r * 0.45, head_r * 0.45, head_r * 0.9)).to_4x4())
    bmesh.ops.create_cone(bm, cap_ends=True, segments=10, radius1=1, radius2=0.0, depth=1.2, matrix=mat)
    me = bpy.data.meshes.new(name)
    bm.to_mesh(me)
    bm.free()
    ob = bpy.data.objects.new(name, me)
    ob.color = color
    ob[ROLE_KEY] = "char"
    ob.show_name = True
    ob.lock_location[2] = True
    ob.lock_rotation[0] = True
    ob.lock_rotation[1] = True
    peg_material(ob)
    return ob


def build_boundary_object(label, w, d, h):
    """Wire box marking the studio working space."""
    name = f"Studio Space · {label}"
    me = bpy.data.meshes.get(name)
    if me is None:
        me = bpy.data.meshes.new(name)
    bm = bmesh.new()
    hw, hd = w / 2, d / 2
    vs = [bm.verts.new(v) for v in [
        (-hw, -hd, 0), (hw, -hd, 0), (hw, hd, 0), (-hw, hd, 0),
        (-hw, -hd, h), (hw, -hd, h), (hw, hd, h), (-hw, hd, h)]]
    for a, b in [(0, 1), (1, 2), (2, 3), (3, 0), (4, 5), (5, 6), (6, 7), (7, 4),
                 (0, 4), (1, 5), (2, 6), (3, 7)]:
        bm.edges.new((vs[a], vs[b]))
    bm.to_mesh(me)
    bm.free()
    ob = bpy.data.objects.get(name)
    if ob is None or ob.data != me:
        ob = bpy.data.objects.new(name, me)
    ob[ROLE_KEY] = "boundary"
    ob.display_type = 'WIRE'
    ob.hide_render = True
    ob.color = (0.2, 0.8, 0.9, 1.0)
    return ob


# ------------------------------------------------------------------ view layer + ghost

def normalize_view_layer(scene):
    """Stage Mode owns visibility through per-pane local view, so the staging's view layer
    itself must show everything: un-exclude, un-hide (outliner eye) and un-H every object of
    the staging. Repairs files damaged by v0.7 (global isolate) and by careless hiding."""
    if not is_staging(scene):
        return
    roots = [c for k in ("SET", "STUDIO", "STAGE") for c in layer_colls(scene, k)]
    for vl in scene.view_layers:
        for root in roots:
            lc = find_layer_collection(vl.layer_collection, root)
            stack = [lc] if lc is not None else []
            while stack:
                x = stack.pop()
                if x.exclude:
                    x.exclude = False
                if x.hide_viewport:
                    x.hide_viewport = False
                stack.extend(x.children)
        for ob in scene.objects:
            try:
                if ob.hide_get(view_layer=vl):
                    ob.hide_set(False, view_layer=vl)
            except RuntimeError:
                pass


def apply_view_state(scene, context=None):
    """Older versions excluded layers here; now it only repairs the view layer."""
    normalize_view_layer(scene)


def ghost_tint(scene, on):
    """Fade the SET to translucent grey via object-colour alpha. Only panes in solid shading
    with OBJECT colour show it, so camera panes stay clean. Undone before every save."""
    for coll in layer_colls(scene, "SET"):
        for ob in coll_objects(coll):
            try:
                if on and ob.type in SET_TYPES:     # not the set's own cameras / empties
                    if TINT_KEY not in ob:
                        ob[TINT_KEY] = list(ob.color)
                    if _rgba_differs(ob.color, GHOST_RGBA):
                        ob.color = GHOST_RGBA
                elif TINT_KEY in ob:
                    ob.color = ob[TINT_KEY]
                    del ob[TINT_KEY]
                if DT_BACKUP_KEY in ob:
                    ob.display_type = ob[DT_BACKUP_KEY]
                    del ob[DT_BACKUP_KEY]
            except Exception:
                pass


def untint_everything():
    for ob in bpy.data.objects:
        if TINT_KEY in ob:
            try:
                ob.color = ob[TINT_KEY]
                del ob[TINT_KEY]
            except Exception:
                pass


def _view_state_update(self, context):
    pass


def _shell_update(self, context):
    scene = self.id_data if isinstance(getattr(self, "id_data", None), bpy.types.Scene) else context.scene
    if is_staging(scene) and not _QUIET["floor"]:
        build_studio_shell(scene)
        request_sync(0.0)


def _studio_dims_update(self, context):
    scene = self.id_data if isinstance(getattr(self, "id_data", None), bpy.types.Scene) else context.scene
    if not is_staging(scene):
        return
    st = scene.bb_st
    studio = layer_colls(scene, "STUDIO")
    if not studio:
        return
    old = boundary_of(scene)
    loc = old.location.copy() if old is not None else None
    new = build_boundary_object(staging_label(scene), st.studio_w, st.studio_d, st.studio_h)
    if old is not None and old != new:
        bpy.data.objects.remove(old)
    if studio[0].objects.get(new.name) is None:
        studio[0].objects.link(new)
    if loc is not None:
        new.location = loc
    st.boundary = new
    build_studio_shell(scene)
    request_sync()


# ------------------------------------------------------------------ beats

def fps(scene):
    return scene.render.fps / scene.render.fps_base


def beat_marker(scene, i):
    name = f"B{i + 1}"
    for m in scene.timeline_markers:
        if m.name == name or m.name.startswith(name + " "):
            return m
    return None


def sync_markers(scene):
    st = scene.bb_st
    keep = set()
    for i, b in enumerate(st.beats):
        name = f"B{i + 1}" + (f" {b.label}" if b.label else "")
        m = beat_marker(scene, i)
        if m is None:
            m = scene.timeline_markers.new(name, frame=b.frame)
        m.name = name
        m.frame = b.frame
        keep.add(m.name)
    for m in list(scene.timeline_markers):
        if m.name.startswith("B") and m.name not in keep:
            parts = m.name.split(" ", 1)[0][1:]
            if parts.isdigit():
                scene.timeline_markers.remove(m)


def keyed_objects(scene):
    st = scene.bb_st
    obs = stage_objects(scene, roles=("char", "prop"))
    if st.key_cameras:
        obs += [o for o in stage_objects(scene, roles=("cam",))]
        cams = sub_coll(scene, "STAGE", "Cameras")
        if cams:
            obs += [o for o in cams.objects if o.type == 'CAMERA' and o not in obs]
    return obs


def beat_out(b):
    return max(b.frame, b.frame_out)


def save_beat(scene, index):
    """Key everyone's current pose on this beat: on its arrival frame and, when it holds, on
    the frame it leaves, so the hold stays still."""
    st = scene.bb_st
    b = st.beats[index]
    sync_peg_colors(scene)
    for ob in keyed_objects(scene):
        for f in sorted({b.frame, beat_out(b)}):
            ob.keyframe_insert("location", frame=f, group="BB Stage")
            ob.keyframe_insert("rotation_euler", frame=f, group="BB Stage")
    b.dirty = False


def beat_layout(scene, start=None):
    """(arrive, leave) frames for every beat from its Move and Hold times."""
    st = scene.bb_st
    f = fps(scene)
    out = []
    t = st.beats[0].frame if (start is None and len(st.beats)) else (start or 1)
    for i, b in enumerate(st.beats):
        if i:
            t = out[-1][1] + max(1, round(b.move_s * f))    # a 0 s move is a cut on the next frame
        out.append((t, t + max(0, round(b.hold_s * f))))
    return out


_BLOCK_PATHS = ("location", "rotation_euler")


def sample_beat_poses(scene):
    """Every keyed object's pose on every beat: {object name: [{(path, index): value}, ...]}."""
    st = scene.bb_st
    poses = {}
    for ob in keyed_objects(scene):
        ad = ob.animation_data
        fcs = [fc for fc in channelbag_fcurves(ad.action) if fc.data_path in _BLOCK_PATHS] if (ad and ad.action) else []
        if fcs:
            poses[ob.name] = [{(fc.data_path, fc.array_index): fc.evaluate(b.frame) for fc in fcs} for b in st.beats]
    return poses


def write_beat_layout(scene, poses, start=None):
    """Re-key the blocking from the beat poses on the current Move/Hold timing."""
    st = scene.bb_st
    if not len(st.beats):
        return
    layout = beat_layout(scene, start)
    for ob in keyed_objects(scene):
        p = poses.get(ob.name)
        ad = ob.animation_data
        if p is None or not (ad and ad.action):
            continue
        for fc in channelbag_fcurves(ad.action):
            if fc.data_path not in _BLOCK_PATHS:
                continue
            key = (fc.data_path, fc.array_index)
            pts = []
            for (a, d), pose in zip(layout, p):
                if key in pose:
                    pts.append((a, pose[key]))
                    if d > a:
                        pts.append((d, pose[key]))
            while len(fc.keyframe_points):
                fc.keyframe_points.remove(fc.keyframe_points[-1], fast=True)
            fc.keyframe_points.add(len(pts))
            for kp, (fr, v) in zip(fc.keyframe_points, pts):
                kp.co = (fr, v)
                kp.interpolation = 'BEZIER'
                kp.handle_left_type = kp.handle_right_type = 'AUTO_CLAMPED'
            fc.update()
    for b, (a, d) in zip(st.beats, layout):
        b.frame, b.frame_out = a, d
    sync_markers(scene)
    scene.frame_end = max(layout[-1][1], layout[0][0] + 1)


def relayout_beats(scene):
    """A Move or Hold time changed: keep every beat's pose, re-time everything."""
    if _QUIET["beats"] or not (is_staging(scene) and len(scene.bb_st.beats)):
        return
    st = scene.bb_st
    i = beat_at_frame(scene)
    if i is not None and st.beats[i].dirty:
        save_beat(scene, i)                 # unsaved moves are kept, never thrown away
    _QUIET["beats"] = True
    try:
        write_beat_layout(scene, sample_beat_poses(scene))
    finally:
        _QUIET["beats"] = False
    scene.frame_set(st.beats[_clamped_beat(st)].frame)


def _beat_time_update(self, context):
    scene = self.id_data
    if isinstance(scene, bpy.types.Scene):
        relayout_beats(scene)


def upgrade_beats(scene):
    """Stagings made before v0.9 timed beats by their frames: turn the gaps into Move times."""
    st = scene.bb_st
    if not len(st.beats) or all(b.frame_out for b in st.beats):
        return
    f = fps(scene)
    _QUIET["beats"] = True
    try:
        prev = None
        for b in st.beats:
            b.move_s = round((b.frame - prev) / f, 2) if prev is not None else st.beat_spacing
            b.hold_s = 0.0
            b.frame_out = b.frame
            prev = b.frame
    finally:
        _QUIET["beats"] = False


def _clamped_beat(st):
    """The active beat, pulled back into range (undo or a hand edit can leave it out). Written
    as an ID property so the click-to-jump update does not fire."""
    i = min(max(st.beat_index, 0), len(st.beats) - 1)
    if i != st.beat_index:
        st["beat_index"] = i
    return i


def beat_at_frame(scene, frame=None):
    """The beat the playhead is on: its arrival frame or anywhere in its hold."""
    st = scene.bb_st
    f = scene.frame_current if frame is None else frame
    for i, b in enumerate(st.beats):
        if b.frame - 0.5 <= f <= beat_out(b) + 0.5:
            return i
    return None


def _bbst_on_depsgraph(scene, depsgraph):
    """Mark the beat at the playhead orange when a staged object moves off its saved keys."""
    try:
        if (scene is not None and is_staging(scene)
                and any(isinstance(u.id, bpy.types.Object) and not u.is_updated_transform
                        and u.id.get(ROLE_KEY) in ("char", "prop") for u in depsgraph.updates)
                and peg_colors_stale(scene)):
            request_sync(0.05)      # a recolour (or a Shift+D copy) reaches the camera panes
        if not (scene is not None and is_staging(scene) and scene.bb_st.beats):
            return
        scr = getattr(bpy.context, "screen", None)
        if scr is not None and scr.is_animation_playing:
            return
        i = beat_at_frame(scene)
        if i is None or scene.bb_st.beats[i].dirty:
            return
        stage_ids = {ob.name for ob in keyed_objects(scene)}
        moved = None
        for up in depsgraph.updates:
            if up.is_updated_transform and isinstance(up.id, bpy.types.Object) and up.id.name in stage_ids:
                moved = bpy.data.objects.get(up.id.name)
                break
        if moved is None:
            return
        ad = moved.animation_data
        if not (ad and ad.action):
            scene.bb_st.beats[i].dirty = True
            return
        f = scene.bb_st.beats[i].frame
        for fc in channelbag_fcurves(ad.action):
            cur = None
            if fc.data_path == "location":
                cur = moved.location[fc.array_index]
            elif fc.data_path == "rotation_euler":
                cur = moved.rotation_euler[fc.array_index]
            if cur is not None and abs(fc.evaluate(f) - cur) > 1e-4:
                scene.bb_st.beats[i].dirty = True
                return
    except Exception:
        pass


def _beat_label_update(self, context):
    sync_markers(context.scene)


def beat_top_speed(scene, i):
    """Fastest character between beat i and i+1, in m/s (walking tops out ~1.5)."""
    st = scene.bb_st
    if i >= len(st.beats) - 1:
        return None
    f0, f1 = beat_out(st.beats[i]), st.beats[i + 1].frame
    secs = (f1 - f0) / fps(scene)
    if secs <= 0:
        return None
    worst = None
    for ob in stage_objects(scene, roles=("char",)):
        ad = ob.animation_data
        if not (ad and ad.action):
            continue
        p0, p1 = [0, 0], [0, 0]
        for fc in channelbag_fcurves(ad.action):
            if fc.data_path == "location" and fc.array_index in (0, 1):
                p0[fc.array_index] = fc.evaluate(f0)
                p1[fc.array_index] = fc.evaluate(f1)
        v = math.hypot(p1[0] - p0[0], p1[1] - p0[1]) / secs
        if worst is None or v > worst[1]:
            worst = (ob.name, v)
    return worst


# ------------------------------------------------------------------ properties

def _black_outside_update(self, context):
    apply_passepartout(context.scene)   # defined further down; resolved at call time


class BBST_Beat(bpy.types.PropertyGroup):
    label: bpy.props.StringProperty(name="Label", default="", update=_beat_label_update)
    frame: bpy.props.IntProperty(name="Frame", default=1)          # arrives here
    frame_out: bpy.props.IntProperty(default=0)                    # leaves here (after the hold); 0 = pre-v0.9
    move_s: bpy.props.FloatProperty(name="Move (s)", default=3.0, min=0.0, soft_max=30.0, step=50,
                                    precision=1, update=_beat_time_update,
                                    description="Seconds everyone takes to move from the previous beat into this one")
    hold_s: bpy.props.FloatProperty(name="Hold (s)", default=0.0, min=0.0, soft_max=30.0, step=50,
                                    precision=1, update=_beat_time_update,
                                    description="Seconds everyone stays on this beat before moving to the next")
    note: bpy.props.StringProperty(name="Note", default="")
    dirty: bpy.props.BoolProperty(default=False)   # something moved on this beat and isn't saved


def _beat_index_update(self, context):
    """Clicking a beat row jumps the whole scene to that beat. Unsaved moves on the beat being
    left are saved first: the jump re-reads the keys and would wipe them."""
    st = self
    scene = context.scene
    if 0 <= st.beat_index < len(st.beats):
        cur = beat_at_frame(scene)
        if cur is not None and st.beats[cur].dirty:
            save_beat(scene, cur)      # also when re-clicking the active beat: frame_set re-reads the keys
        scene.frame_set(st.beats[st.beat_index].frame)


def _play_level_update(self, context):
    """Settings › Plays on: the studio floor follows the level."""
    scene = self.id_data
    if _QUIET["floor"] or not (isinstance(scene, bpy.types.Scene) and is_staging(scene)):
        return
    if boundary_of(scene) is not None:      # New Staging sets the floor itself
        refresh_floor(scene)
        request_sync(0.0)


def _select_row(context, kind, idx):
    """Clicking a character or prop row selects it, so Turn and drags act on it."""
    scene = context.scene
    c = sub_coll(scene, "STAGE", kind) if is_staging(scene) else None
    if c is not None and 0 <= idx < len(c.objects) and not c.objects[idx].hide_select:
        _select_only(context, c.objects[idx])


class BBST_Props(bpy.types.PropertyGroup):
    mode: bpy.props.EnumProperty(name="Mode", items=[
        ('EASY', "Easy", "Characters, beats and cameras only"),
        ('ARTIST', "Artist", "Full control: studio build, stand-ins, outputs")],
        default='ARTIST')
    view_state: bpy.props.EnumProperty(name="World", items=[
        ('SET', "Set", "The finished 3D location"),
        ('STUDIO', "Studio", "The grey studio blockout"),
        ('BOTH', "Both", "Studio solid, set faded to a translucent ghost"),
        ('SPLIT', "Split", "Both worlds on; each pane of the Stage Layout picks its own")],
        default='SET', update=_view_state_update)
    studio_w: bpy.props.FloatProperty(name="Width", default=12.0, min=2, max=60, update=_studio_dims_update)
    studio_d: bpy.props.FloatProperty(name="Depth", default=10.0, min=2, max=60, update=_studio_dims_update)
    studio_h: bpy.props.FloatProperty(name="Height", default=4.0, min=2, max=20, update=_studio_dims_update)
    wall_count: bpy.props.IntProperty(name="Studio walls", default=4, min=0, max=12, update=_shell_update,
                                      description="Wall flats standing along the back of the studio")
    wall_width: bpy.props.FloatProperty(name="Wall width (m)", default=2.4, min=0.3, max=10, update=_shell_update)
    wall_height: bpy.props.FloatProperty(name="Wall height (m)", default=3.0, min=0.5, max=10, update=_shell_update)
    shell_built: bpy.props.BoolProperty(default=False)
    beat_spacing: bpy.props.FloatProperty(name="Default move time (s)", default=3.0, min=0.0, max=60,
                                          description="How long the move into a new beat takes")
    key_cameras: bpy.props.BoolProperty(name="Key cameras on beats", default=False)
    black_outside: bpy.props.BoolProperty(name="Black outside camera", default=True,
                                          update=_black_outside_update,
                                          description="Camera panes show nothing outside the frame")
    ceiling_cut: bpy.props.FloatProperty(name="Upper floor plan cut (m)", default=9.5, min=0.5, max=60,
                                         update=lambda self, ctx: request_sync(0.0),
                                         description="The plan of the upper floor is cut at this height")
    level1_cut: bpy.props.FloatProperty(name="Ground floor plan cut (m)", default=5.5, min=0.5, max=60,
                                        update=lambda self, ctx: request_sync(0.0),
                                        description="The plan of the ground floor is cut at this height (just under the floor above)")
    active_level: bpy.props.EnumProperty(name="Working level", items=[
        ('GROUND', "Ground floor", ""), ('L1', "Upper floor", ""), ('ALL', "All levels", "")],
        default='GROUND')
    beats: bpy.props.CollectionProperty(type=BBST_Beat)
    beat_index: bpy.props.IntProperty(default=0, update=_beat_index_update)
    stage_mode: bpy.props.BoolProperty(default=False)   # the kiosk layout is active
    prev_workspace: bpy.props.StringProperty(default="")
    ui_tab: bpy.props.EnumProperty(name="Section", items=[
        ('SCENES', "Scenes", "Pick the set scene or a staging", 'SCENE_DATA', 0),
        ('STUDIO', "Studio Build", "Build the grey studio blockout", 'MOD_BUILD', 1),
        ('CAST', "Characters & Props", "Who and what is in the scene", 'COMMUNITY', 2),
        ('BEATS', "Beats", "Stage the action beat by beat", 'KEYFRAME_HLT', 3),
        ('CAMS', "Cameras", "Cameras", 'OUTLINER_OB_CAMERA', 4),
        ('OUT', "Outputs", "Playblasts and the staging pack", 'EXPORT', 5),
        ('PREFS', "Settings", "Studio size and defaults", 'PREFERENCES', 6)],
        default='BEATS')
    char_index: bpy.props.IntProperty(default=0, update=lambda self, ctx: _select_row(ctx, "Characters", self.char_index))
    prop_index: bpy.props.IntProperty(default=0, update=lambda self, ctx: _select_row(ctx, "Props", self.prop_index))
    new_char_name: bpy.props.StringProperty(name="Name", default="")
    next_color: bpy.props.IntProperty(default=0)
    # ---- v0.8: robust references (per staging)
    set_coll: bpy.props.PointerProperty(type=bpy.types.Collection)
    studio_coll: bpy.props.PointerProperty(type=bpy.types.Collection)
    stage_coll: bpy.props.PointerProperty(type=bpy.types.Collection)
    chars_coll: bpy.props.PointerProperty(type=bpy.types.Collection)
    props_coll: bpy.props.PointerProperty(type=bpy.types.Collection)
    cams_coll: bpy.props.PointerProperty(type=bpy.types.Collection)
    boundary: bpy.props.PointerProperty(type=bpy.types.Object)
    data_version: bpy.props.IntProperty(default=0)
    play_level: bpy.props.EnumProperty(name="Plays on", items=LEVEL_ITEMS, default='GROUND',
                                       update=_play_level_update)
    floor_z: bpy.props.FloatProperty(name="Studio floor height (m)", default=0.0, soft_min=-5, soft_max=30,
                                     description="Where characters stand and cameras measure eye level from")
    needs_place: bpy.props.BoolProperty(default=False)
    # ---- v0.8: what each pane shows (per staging)
    work_world: bpy.props.EnumProperty(name="Plan shows", items=WORLD_ITEMS, default='GHOST')
    work_shading: bpy.props.EnumProperty(items=SHADING_ITEMS, default='SOLID')
    cam0_world: bpy.props.EnumProperty(items=WORLD_ITEMS, default='SET')
    cam0_shading: bpy.props.EnumProperty(items=SHADING_ITEMS, default='SOLID')
    cam1_world: bpy.props.EnumProperty(items=WORLD_ITEMS, default='SET')
    cam1_shading: bpy.props.EnumProperty(items=SHADING_ITEMS, default='SOLID')
    cam0: bpy.props.PointerProperty(type=bpy.types.Object)
    cam1: bpy.props.PointerProperty(type=bpy.types.Object)
    # ---- v0.8: file level (read from the set scene)
    level1_coll: bpy.props.PointerProperty(type=bpy.types.Collection)
    ceiling_coll: bpy.props.PointerProperty(type=bpy.types.Collection)
    floors_detected: bpy.props.BoolProperty(default=False)
    has_upper: bpy.props.BoolProperty(name="This set has an upper floor", default=True)
    ground_z: bpy.props.FloatProperty(name="Ground floor height (m)", default=-999.0)   # -999 = not detected yet
    upper_z: bpy.props.FloatProperty(name="Upper floor height (m)", default=-999.0)


# ------------------------------------------------------------------ staging builder

def set_bounds_center(scene):
    """Where the set's things are: the median of mesh positions (a giant ground plane or a
    stray object far away does not drag it off the building)."""
    xs, ys = [], []
    for c in layer_colls(scene, "SET"):
        for ob in coll_objects(c):
            if ob.type == 'MESH':
                p = ob.matrix_world.translation
                xs.append(p.x)
                ys.append(p.y)
    if not xs:
        return Vector((0.0, 0.0, 0.0))
    xs.sort()
    ys.sort()
    return Vector((xs[len(xs) // 2], ys[len(ys) // 2], 0.0))


def _scene_depsgraph(scene):
    vl = scene.view_layers[0]
    dg = vl.depsgraph
    try:
        dg.update()
    except Exception:
        pass
    return dg


def floors_known(fs):
    """Detect Floors has run with a version that stores the floor heights."""
    return fs is not None and fs.floors_detected and fs.ground_z > -900.0


def store_floors(fs, scene):
    g, u, gc, uc = detect_floors(scene)
    fs.level1_cut, fs.ceiling_cut = gc, uc
    fs.ground_z = g
    fs.upper_z = u if u is not None else -999.0
    fs.has_upper = u is not None
    fs.floors_detected = True
    return g, u, gc, uc


@contextmanager
def set_only(scene):
    """Ray-casts in a staging that see the set alone: its STUDIO and STAGE layers are hidden for
    the cast (a peg or kit piece standing on the probe point masked the floor)."""
    vl = scene.view_layers[0]
    dg = _scene_depsgraph(scene)      # also brings a new scene's layer collections into being
    hidden = []
    root = vl.layer_collection
    for kind in ("STUDIO", "STAGE"):
        for c in layer_colls(scene, kind):
            lc = find_layer_collection(root, c)
            if lc is not None and not lc.hide_viewport:
                lc.hide_viewport = True
                hidden.append(lc)
    try:
        yield _scene_depsgraph(scene) if hidden else dg
    finally:
        for lc in hidden:
            lc.hide_viewport = False


def detect_floor_z(scene, x, y, level):
    """Height of the floor under (x, y) on the given level: the highest big upward-facing set
    surface in a band just above that level's detected floor (rugs and slabs count, tables do not).
    The band was anchored on the plan cut, which v0.8 puts 2.2 m above the ground floor, so upper-
    floor stagings landed at 2.7 m on Daaruwala and a raised ground floor (Shefali 1.22 m) was missed."""
    fs = fstate()
    l1cut = fs.level1_cut if fs is not None else 5.5
    known = floors_known(fs)
    if level == 'L1':
        if known and fs.upper_z > -900.0:
            base = fs.upper_z
            top, low = base + 0.6, max(l1cut, base - 0.5)
        else:
            base = l1cut + 0.5
            top, low = l1cut + 1.5, l1cut - 1.0
    else:
        base = fs.ground_z if known else 0.0
        top, low = base + 1.2, base - 3.0
    set_names = set()
    for c in layer_colls(scene, "SET"):
        set_names |= {o.name for o in coll_objects(c)}
    if not set_names:
        return round(base, 4)
    origin = Vector((x, y, top))
    best_big = lowest = None
    with set_only(scene) as dg:
        for _ in range(96):
            try:
                hit, loc, nrm, _i, ob, _m = scene.ray_cast(dg, origin, Vector((0.0, 0.0, -1.0)))
            except Exception:
                break
            if not hit or loc.z < low:
                break
            name = ob.original.name if (ob is not None and getattr(ob, "original", None)) else (ob.name if ob else "")
            if name in set_names and nrm.z > 0.5:
                src = bpy.data.objects.get(name)
                d = src.dimensions if src is not None else Vector((0, 0, 0))
                if best_big is None and d.x * d.y >= 6.0:
                    best_big = loc.z
                if lowest is None or loc.z < lowest:
                    lowest = loc.z
            origin = loc - Vector((0.0, 0.0, 0.002))
    if best_big is not None:
        return round(best_big, 4)
    if lowest is not None:
        return round(lowest, 4)
    return round(base, 4)


def studio_center(scene):
    st = scene.bb_st
    b = boundary_of(scene)
    if b is not None:
        return Vector((b.location.x, b.location.y, st.floor_z))
    c = set_bounds_center(scene)
    c.z = st.floor_z
    return c


def refresh_floor(scene, carry=True):
    st = scene.bb_st
    b = boundary_of(scene)
    c = studio_center(scene)
    old = st.floor_z
    st.floor_z = detect_floor_z(scene, c.x, c.y, st.play_level)
    if b is not None:
        b.location.z = st.floor_z
    if carry:      # what stands on the studio floor moves with it
        carry_with_studio(scene, Vector((0.0, 0.0, st.floor_z - old)))


def _carried_objects(scene):
    b = boundary_of(scene)
    obs = set(stage_objects(scene, roles=("char", "prop", "cam"))) | set(stage_cams(scene))
    for c in layer_colls(scene, "STUDIO"):
        obs |= {o for o in coll_objects(c) if o != b}
    # stand-ins / matched pieces sit where their set object is: they never move with the studio
    return [o for o in obs if o.parent is None and o.get(SOURCE_KEY) is None]


def carry_with_studio(scene, d):
    """Move the studio's pieces, pegs and cameras by d, their beat keys included."""
    if d.length < 1e-5:
        return
    for ob in _carried_objects(scene):
        ob.location += d
        ad = ob.animation_data
        for fc in (channelbag_fcurves(ad.action) if ad and ad.action else []):
            if fc.data_path == "location" and fc.array_index in (0, 1, 2) and abs(d[fc.array_index]) > 1e-6:
                k = d[fc.array_index]
                for kp in fc.keyframe_points:
                    kp.co.y += k
                    kp.handle_left.y += k
                    kp.handle_right.y += k
                fc.update()


def build_studio_shell(scene):
    """The studio's own floor and its default run of wall flats along the back (+Y) edge, in
    light white. Rebuilt from Settings (wall count / width / height) and from the studio size;
    pieces the user moved by hand are replaced only when those settings change."""
    studio = layer_colls(scene, "STUDIO")
    b = boundary_of(scene)
    if not studio or b is None:
        return
    st = scene.bb_st
    for ob in list(coll_objects(studio[0])):
        if ob.get(SHELL_KEY):
            me = ob.data
            bpy.data.objects.remove(ob)
            if me is not None and me.users == 0:
                bpy.data.meshes.remove(me)
    label = staging_label(scene)
    rot = Matrix.Rotation(b.rotation_euler.z, 4, 'Z')
    base = Matrix.Translation(Vector((b.location.x, b.location.y, st.floor_z))) @ rot

    def place(ob, local):
        ob.location = (base @ Vector(local))
        ob.rotation_euler.z = b.rotation_euler.z
        ob[SHELL_KEY] = True
        studio[0].objects.link(ob)

    w, d = st.studio_w, st.studio_d
    floor = build_box_object(unique_object_name(f"Studio Floor · {label}"), (w, d, 0.04),
                             color=SHELL_WHITE)
    floor["bb_st_kind"] = "Studio floor"
    place(floor, (0.0, 0.0, -0.04))          # its top is the studio floor
    n = max(0, st.wall_count)
    if n:
        ww = min(st.wall_width, w / n)
        x0 = -ww * n / 2 + ww / 2
        for i in range(n):
            wall = build_box_object(unique_object_name(f"Studio Wall {i + 1:02d} · {label}"),
                                    (ww - 0.02, 0.10, st.wall_height), color=SHELL_WHITE)
            wall["bb_st_kind"] = "Studio wall"
            place(wall, (x0 + i * ww, d / 2 - 0.05, 0.0))
    st.shell_built = True


def cursor_to_studio(scene):
    try:
        scene.cursor.location = studio_center(scene)
        scene.cursor.rotation_euler = (0.0, 0.0, 0.0)
    except Exception:
        pass


def unique_object_name(base):
    if bpy.data.objects.get(base) is None:
        return base
    i = 2
    while bpy.data.objects.get(f"{base} {i}") is not None:
        i += 1
    return f"{base} {i}"


def make_stage_camera(scene, lens=35.0):
    """A camera in the middle of the studio at eye level, level, looking along +Y."""
    cams = sub_coll(scene, "STAGE", "Cameras")
    if cams is None:
        return None
    n = len([o for o in cams.objects if o.type == 'CAMERA'])
    letter = chr(ord('A') + min(25, n))
    name = unique_object_name(f"STG Cam {letter}")
    data = bpy.data.cameras.new(name)
    data.lens = lens
    ob = bpy.data.objects.new(name, data)
    ob[ROLE_KEY] = "cam"
    # back from the centre (where the first character appears), stopping short of a wall;
    # each further camera one step to the side so two panes never show the same picture
    c = studio_center(scene)
    p = Vector((c.x + (0.0, 1.5, -1.5)[n % 3], c.y, c.z + EYE_HEIGHT))
    back = min(3.0, max(0.0, scene.bb_st.studio_d / 2 - 0.5))
    try:
        with set_only(scene) as dg:
            hit, loc, *_r = scene.ray_cast(dg, p, Vector((0.0, -1.0, 0.0)), distance=back + 0.4)
        if hit:
            back = max(0.0, (p - loc).length - 0.4)
    except Exception:
        pass
    ob.location = (p.x, p.y - back, p.z)
    ob.rotation_euler = (math.radians(90.0), 0.0, 0.0)
    cams.objects.link(ob)
    apply_passepartout(scene)
    return ob


def spawn_point(scene, n, studio_only=True):
    """Spread new things around the studio centre so they do not stack on one spot."""
    c = studio_center(scene)
    if n <= 0:
        return c
    st = scene.bb_st
    ang = n * 2.39996
    r = 0.8 * math.sqrt(n)
    lim_x, lim_y = max(0.3, st.studio_w / 2 - 0.4), max(0.3, st.studio_d / 2 - 0.4)
    return Vector((c.x + max(-lim_x, min(lim_x, r * math.cos(ang))),
                   c.y + max(-lim_y, min(lim_y, r * math.sin(ang))), c.z))


class BBST_OT_new_staging(bpy.types.Operator):
    """Create a new staging: one studio setup for one scene of this set"""
    bl_idname = "bbst.new_staging"
    bl_label = "New Staging"
    bl_options = {'REGISTER', 'UNDO'}

    label: bpy.props.StringProperty(name="Staging name", default="")
    level: bpy.props.EnumProperty(name="Plays on", items=LEVEL_ITEMS, default='GROUND',
                                  description="Which floor this scene plays on — everything above it hides")

    def invoke(self, context, event):
        return context.window_manager.invoke_props_dialog(self)

    def execute(self, context):
        label = " ".join(self.label.split())
        if not label:
            self.report({'ERROR'}, "Give the staging a name")
            return {'CANCELLED'}
        src = master_scene()
        if src is None:
            return {'CANCELLED'}
        name = STG_PREFIX + label
        if bpy.data.scenes.get(name) is not None:
            self.report({'ERROR'}, f"A staging called '{label}' already exists")
            return {'CANCELLED'}
        sc = bpy.data.scenes.new(name)
        for attr in ("fps", "fps_base", "resolution_x", "resolution_y", "resolution_percentage"):
            setattr(sc.render, attr, getattr(src.render, attr))
        try:
            sc.render.engine = src.render.engine
        except TypeError:
            pass
        sc.world = src.world
        sc.frame_start, sc.frame_end = 1, 240
        st = sc.bb_st
        # the whole set, linked (never copied) under one unselectable wrapper: the model can
        # only be edited in its own scene (Aman, 5 Oct 2026)
        wrapper = bpy.data.collections.new(f"SET · {label}")
        wrapper[LAYER_KEY] = "SET"
        wrapper.hide_select = True
        sc.collection.children.link(wrapper)
        for coll in src.collection.children:
            if coll.get(LAYER_KEY) in ("SET", "STUDIO", "STAGE"):
                continue
            wrapper.children.link(coll)
        for ob in src.collection.objects:
            if ob.get(ROLE_KEY) is None:
                wrapper.objects.link(ob)
        studio = bpy.data.collections.new(f"STUDIO · {label}")
        studio[LAYER_KEY] = "STUDIO"
        sc.collection.children.link(studio)
        stage = bpy.data.collections.new(f"STAGE · {label}")
        stage[LAYER_KEY] = "STAGE"
        sc.collection.children.link(stage)
        st.set_coll, st.studio_coll, st.stage_coll = wrapper, studio, stage
        subs = {}
        for child in ("Characters", "Props", "Cameras"):
            c = bpy.data.collections.new(f"{child} · {label}")
            c[SUB_KEY] = child
            stage.children.link(c)
            subs[child] = c
        st.chars_coll, st.props_coll, st.cams_coll = subs["Characters"], subs["Props"], subs["Cameras"]
        fs = fstate()
        if fs is not None and not floors_known(fs):
            store_floors(fs, sc)        # first staging of this set: find its floors and plan cuts
        level = self.level
        if level == 'L1' and fs is not None and not fs.has_upper:
            level = 'GROUND'
            self.report({'WARNING'}, "This set has one floor: the staging plays on the ground floor")
        st.play_level = level
        st.active_level = level
        st.data_version = DATA_VERSION
        # studio space: middle of the set, standing on this level's floor
        centre = set_bounds_center(sc)
        bound = build_boundary_object(label, st.studio_w, st.studio_d, st.studio_h)
        studio.objects.link(bound)
        st.boundary = bound
        bound.location = (centre.x, centre.y, 0.0)
        st.floor_z = detect_floor_z(sc, centre.x, centre.y, level)
        bound.location.z = st.floor_z
        build_studio_shell(sc)
        cam = make_stage_camera(sc)
        if cam is not None:
            sc.camera = cam
            st.cam0 = cam
        st.needs_place = True
        context.window.scene = sc
        normalize_view_layer(sc)
        cursor_to_studio(sc)
        if stage_on() and context.window.workspace.name == WS_NAME:
            _build_stage_screen(sc.name)
        else:
            enter_stage_mode(context, sc)
        self.report({'INFO'}, f"Staging '{label}' created — now drag the studio space where the scene plays")
        return {'FINISHED'}


class BBST_OT_delete_staging(bpy.types.Operator):
    """Delete this staging: its scene, studio build, characters, props, cameras and beats.
The set model and the other stagings are untouched"""
    bl_idname = "bbst.delete_staging"
    bl_label = "Delete Staging?"
    bl_options = {'REGISTER', 'UNDO'}
    scene_name: bpy.props.StringProperty()

    def invoke(self, context, event):
        return context.window_manager.invoke_confirm(self, event)

    def execute(self, context):
        sc = bpy.data.scenes.get(self.scene_name)
        if sc is None or not is_staging(sc):
            return {'CANCELLED'}
        own_roots = layer_colls(sc, "STUDIO") + layer_colls(sc, "STAGE")
        wrappers = layer_colls(sc, "SET")
        others = [s for s in stagings() if s != sc]
        for win in context.window_manager.windows:
            if win.scene == sc:
                win.scene = others[0] if others else master_scene()
        doomed_colls = []
        for root in own_roots:
            doomed_colls += [root] + list(root.children_recursive)
        keep = {c.name for c in doomed_colls}
        doomed_obs = {ob for c in doomed_colls for ob in c.objects}
        for ob in list(doomed_obs):
            if any(uc.name not in keep for uc in ob.users_collection):
                doomed_obs.discard(ob)
        for ob in doomed_obs:
            bpy.data.objects.remove(ob)
        for c in doomed_colls + wrappers:
            try:
                bpy.data.collections.remove(c)
            except Exception:
                pass
        bpy.data.scenes.remove(sc)
        if stage_on():
            if others:
                cur = context.window.scene
                _build_stage_screen(cur.name if is_staging(cur) else others[0].name)
            else:
                exit_stage_mode(context)
        self.report({'INFO'}, "Staging deleted")
        return {'FINISHED'}


class BBST_OT_goto_scene(bpy.types.Operator):
    """Switch to this staging"""
    bl_idname = "bbst.goto_scene"
    bl_label = "Go to staging"
    scene_name: bpy.props.StringProperty()

    def execute(self, context):
        sc = bpy.data.scenes.get(self.scene_name)
        if sc is None:
            return {'CANCELLED'}
        context.window.scene = sc
        if is_staging(sc):
            migrate_staging(sc)
            normalize_view_layer(sc)
            cursor_to_studio(sc)
            if stage_on() and context.window.workspace.name == WS_NAME:
                _build_stage_screen(sc.name)
        return {'FINISHED'}


# ------------------------------------------------------------------ studio build

class BBST_OT_add_kit(bpy.types.Operator):
    """Add a studio kit piece in the middle of the studio, on its floor"""
    bl_idname = "bbst.add_kit"
    bl_label = "Add Kit Piece"
    bl_options = {'REGISTER', 'UNDO'}

    piece: bpy.props.EnumProperty(items=[(k, v[0], "") for k, v in KIT_PIECES.items()])
    size: bpy.props.FloatVectorProperty(name="Size", size=3, default=(1, 1, 1), min=0.05)

    def invoke(self, context, event):
        _label, x, y, z = KIT_PIECES[self.piece]
        self.size = (x, y, z)
        return self.execute(context)

    def execute(self, context):
        scene = context.scene
        studio = layer_colls(scene, "STUDIO") if is_staging(scene) else []
        if not studio:
            self.report({'ERROR'}, "Open a staging first")
            return {'CANCELLED'}
        label = KIT_PIECES[self.piece][0]
        n = sum(1 for o in studio[0].objects if o.get("bb_st_kind") == label) + 1
        loc = spawn_point(scene, 6 + sum(1 for o in studio[0].objects if o.get(ROLE_KEY) == "studio"))   # own ring, not the pegs' spot
        ob = build_box_object(unique_object_name(f"Studio {label} {n:02d}"), tuple(self.size), loc)
        ob["bb_st_kind"] = label
        studio[0].objects.link(ob)
        _select_only(context, ob)
        request_sync(0.0)
        return {'FINISHED'}


def _select_only(context, ob):
    vl = context.view_layer
    try:
        for o in context.selected_objects:
            o.select_set(False)
        ob.select_set(True)
        vl.objects.active = ob
    except Exception:
        pass


def make_standin(scene, objs):
    """A grounded grey box in STUDIO matching the world bounds of the given set objects."""
    studio = layer_colls(scene, "STUDIO")
    if not (studio and objs):
        return None
    pts = []
    for o in objs:
        pts += [o.matrix_world @ Vector(c) for c in o.bound_box]
    lo = Vector((min(p.x for p in pts), min(p.y for p in pts), min(p.z for p in pts)))
    hi = Vector((max(p.x for p in pts), max(p.y for p in pts), max(p.z for p in pts)))
    fz = scene.bb_st.floor_z if is_staging(scene) else 0.0
    if fz < lo.z < fz + 1.2:
        lo.z = fz   # a table is built from the floor up, not a floating slab
    size = hi - lo
    size = Vector((max(size.x, 0.02), max(size.y, 0.02), max(size.z, 0.02)))
    ob = build_box_object("SI " + objs[0].name, tuple(size),
                          (lo.x + size.x / 2, lo.y + size.y / 2, max(lo.z, 0)))
    ob[SOURCE_KEY] = objs[0].name
    ob["bb_st_kind"] = "Stand-in"
    studio[0].objects.link(ob)
    return ob


def match_piece(piece, src):
    """Move + resize a studio piece onto a set object's world bounds."""
    pts = [src.matrix_world @ Vector(c) for c in src.bound_box]
    lo = Vector((min(p.x for p in pts), min(p.y for p in pts), min(p.z for p in pts)))
    hi = Vector((max(p.x for p in pts), max(p.y for p in pts), max(p.z for p in pts)))
    size = hi - lo
    piece.location = (lo.x + size.x / 2, lo.y + size.y / 2, max(lo.z, 0))
    dims = piece.dimensions
    piece.scale = (piece.scale.x * size.x / max(dims.x, 1e-5),
                   piece.scale.y * size.y / max(dims.y, 1e-5),
                   piece.scale.z * size.z / max(dims.z, 1e-5))
    piece[SOURCE_KEY] = src.name


def pick_set_object(context, event):
    """The object under the mouse in whichever 3D pane it is over — only what that pane
    actually shows (skips things hidden in the pane or cut away above the level)."""
    from bpy_extras import view3d_utils
    win = context.window
    for area in context.screen.areas:
        if area.type != 'VIEW_3D':
            continue
        region = next((r for r in area.regions if r.type == 'WINDOW'), None)
        if not region or not (region.x <= event.mouse_x <= region.x + region.width
                              and region.y <= event.mouse_y <= region.y + region.height):
            continue
        sp = area.spaces.active
        co = (event.mouse_x - region.x, event.mouse_y - region.y)
        rv3d = sp.region_3d
        direction = view3d_utils.region_2d_to_vector_3d(region, rv3d, co)
        origin = view3d_utils.region_2d_to_origin_3d(region, rv3d, co)
        cut = None
        if rv3d.use_clip_planes and len(rv3d.clip_planes):
            p = rv3d.clip_planes[0]
            if abs(p[2] + 1.0) < 1e-3:
                cut = p[3]
        dg = context.evaluated_depsgraph_get()
        vl = context.view_layer
        for _ in range(64):
            hit, loc, _n, _i, ob, _m = context.scene.ray_cast(dg, origin, direction)
            if not hit:
                return None
            src = ob.original if getattr(ob, "original", None) else ob
            shown = True
            try:
                shown = src.visible_get(view_layer=vl, viewport=sp)
            except Exception:
                pass
            if shown and (cut is None or loc.z <= cut + 1e-4):
                return src
            origin = loc + direction * 0.002
        return None
    return None


def _is_set_object(ob):
    return ob is not None and ob.get(ROLE_KEY) is None


class BBST_OT_pick_standin(bpy.types.Operator):
    """Click set objects (table, shelf, wall) one after another — each click makes a grey
box of that size in the studio layer. Right-click or Esc to finish"""
    bl_idname = "bbst.pick_standin"
    bl_label = "Grey Box from Set Object"
    bl_options = {'REGISTER', 'UNDO'}

    def invoke(self, context, event):
        self.made = 0
        context.workspace.status_text_set("Click a set object to make its grey box · right-click or Esc to finish")
        context.window.cursor_modal_set('EYEDROPPER')
        context.window_manager.modal_handler_add(self)
        return {'RUNNING_MODAL'}

    def finish(self, context):
        context.workspace.status_text_set(None)
        context.window.cursor_modal_restore()
        self.report({'INFO'}, f"{self.made} stand-in(s) made")
        return {'FINISHED'} if self.made else {'CANCELLED'}

    def modal(self, context, event):
        if event.type == 'LEFTMOUSE' and event.value == 'PRESS':
            ob = pick_set_object(context, event)
            if _is_set_object(ob):
                if make_standin(context.scene, [ob]):
                    self.made += 1
                    context.workspace.status_text_set(
                        f"{self.made} made (last: {ob.name}) · keep clicking · right-click or Esc to finish")
            elif ob is not None:
                context.workspace.status_text_set("That is already a studio or stage piece — click a SET object")
            return {'RUNNING_MODAL'}
        if event.type in ('RIGHTMOUSE', 'ESC', 'RET'):
            return self.finish(context)
        return {'PASS_THROUGH'}


class BBST_OT_pick_match(bpy.types.Operator):
    """First select the kit piece to place, press this, then click the set object it
should stand in for — the piece moves and resizes onto it"""
    bl_idname = "bbst.pick_match"
    bl_label = "Match Piece to Set Object"
    bl_options = {'REGISTER', 'UNDO'}

    def invoke(self, context, event):
        self.piece = context.view_layer.objects.active
        if not (self.piece and self.piece.get(ROLE_KEY) == "studio"):
            self.report({'ERROR'}, "Select a studio kit piece first (in the Studio or Ghost view)")
            return {'CANCELLED'}
        context.workspace.status_text_set(f"Click the set object that {self.piece.name} stands in for · Esc cancels")
        context.window.cursor_modal_set('EYEDROPPER')
        context.window_manager.modal_handler_add(self)
        return {'RUNNING_MODAL'}

    def modal(self, context, event):
        if event.type == 'LEFTMOUSE' and event.value == 'PRESS':
            ob = pick_set_object(context, event)
            if _is_set_object(ob):
                match_piece(self.piece, ob)
                context.workspace.status_text_set(None)
                context.window.cursor_modal_restore()
                return {'FINISHED'}
            return {'RUNNING_MODAL'}
        if event.type in ('RIGHTMOUSE', 'ESC'):
            context.workspace.status_text_set(None)
            context.window.cursor_modal_restore()
            return {'CANCELLED'}
        return {'PASS_THROUGH'}


class BBST_OT_standin(bpy.types.Operator):
    """Pick a real set object (table, shelf, wall) in the Set or Ghost view and click this:
a grey box the same size appears in the studio layer — the thing the crew will build to
stand in for it on the real floor"""
    bl_idname = "bbst.standin"
    bl_label = "Stand-in from Selected"
    bl_options = {'REGISTER', 'UNDO'}

    combined: bpy.props.BoolProperty(name="One box for all selected", default=False)

    def execute(self, context):
        scene = context.scene
        studio = layer_colls(scene, "STUDIO")
        if not studio:
            self.report({'ERROR'}, "Not in a staging scene")
            return {'CANCELLED'}
        sel = [o for o in context.selected_objects if o.type == 'MESH' and o.get(ROLE_KEY) is None]
        if not sel:
            self.report({'ERROR'}, "Select set objects first (switch World to Set)")
            return {'CANCELLED'}
        groups = [sel] if self.combined else [[o] for o in sel]
        made = 0
        for grp in groups:
            pts = []
            for o in grp:
                pts += [o.matrix_world @ Vector(c) for c in o.bound_box]
            lo = Vector((min(p.x for p in pts), min(p.y for p in pts), min(p.z for p in pts)))
            hi = Vector((max(p.x for p in pts), max(p.y for p in pts), max(p.z for p in pts)))
            if 0 < lo.z < 1.2:
                lo.z = 0.0   # a table is built from the floor up, not a floating slab
            size = hi - lo
            if min(size) < 0.01:
                size = Vector((max(size.x, 0.02), max(size.y, 0.02), max(size.z, 0.02)))
            name = "SI " + grp[0].name
            ob = build_box_object(name, tuple(size), (lo.x + size.x / 2, lo.y + size.y / 2, max(lo.z, 0)))
            ob[SOURCE_KEY] = grp[0].name
            ob["bb_st_kind"] = "Stand-in"
            studio[0].objects.link(ob)
            made += 1
        self.report({'INFO'}, f"{made} stand-in(s) made")
        return {'FINISHED'}


class BBST_OT_match_to_set(bpy.types.Operator):
    """Move and resize an existing kit piece so it sits exactly where a set object is:
click the set object, shift-click the kit piece, then this button"""
    bl_idname = "bbst.match_to_set"
    bl_label = "Match to Set Object"
    bl_options = {'REGISTER', 'UNDO'}

    def execute(self, context):
        act = context.view_layer.objects.active
        others = [o for o in context.selected_objects if o != act and o.get(ROLE_KEY) is None]
        if not (act and act.get(ROLE_KEY) == "studio" and others):
            self.report({'ERROR'}, "Select a set object, then shift-select the studio piece")
            return {'CANCELLED'}
        src = others[0]
        pts = [src.matrix_world @ Vector(c) for c in src.bound_box]
        lo = Vector((min(p.x for p in pts), min(p.y for p in pts), min(p.z for p in pts)))
        hi = Vector((max(p.x for p in pts), max(p.y for p in pts), max(p.z for p in pts)))
        size = hi - lo
        act.location = (lo.x + size.x / 2, lo.y + size.y / 2, max(lo.z, 0))
        dims = act.dimensions
        act.scale = (act.scale.x * size.x / max(dims.x, 1e-5),
                     act.scale.y * size.y / max(dims.y, 1e-5),
                     act.scale.z * size.z / max(dims.z, 1e-5))
        act[SOURCE_KEY] = src.name
        return {'FINISHED'}


# ------------------------------------------------------------------ characters & props

class BBST_OT_add_char(bpy.types.Operator):
    """Add a character in the middle of the studio, standing on its floor"""
    bl_idname = "bbst.add_char"
    bl_label = "Add Character"
    bl_options = {'REGISTER', 'UNDO'}

    height: bpy.props.FloatProperty(name="Height", default=1.75, min=0.5, max=2.3)

    def execute(self, context):
        scene = context.scene
        chars = sub_coll(scene, "STAGE", "Characters") if is_staging(scene) else None
        if chars is None:
            self.report({'ERROR'}, "Open a staging first")
            return {'CANCELLED'}
        st = scene.bb_st
        typed = " ".join(st.new_char_name.split())
        k = len(chars.objects) + 1
        while not typed and bpy.data.objects.get(f"Character {k}") is not None:
            k += 1          # 'Character 3', never 'Character 2 2'
        name = unique_object_name(typed or f"Character {k}")
        color = PEG_COLORS[st.next_color % len(PEG_COLORS)]
        st.next_color += 1
        ob = build_peg_object(name, self.height, color)
        ob.location = spawn_point(scene, len(chars.objects))
        chars.objects.link(ob)
        st.new_char_name = ""
        _select_only(context, ob)
        request_sync(0.0)
        return {'FINISHED'}


class BBST_OT_add_prop(bpy.types.Operator):
    """Add a prop block in the middle of the studio, on its floor"""
    bl_idname = "bbst.add_prop"
    bl_label = "Add Prop"
    bl_options = {'REGISTER', 'UNDO'}

    standin: bpy.props.BoolProperty(name="Placeholder stand-in (banned from outputs)", default=False)
    size: bpy.props.FloatVectorProperty(name="Size", size=3, default=(0.4, 0.4, 0.4), min=0.02)

    def execute(self, context):
        scene = context.scene
        props_c = sub_coll(scene, "STAGE", "Props") if is_staging(scene) else None
        if props_c is None:
            self.report({'ERROR'}, "Open a staging first")
            return {'CANCELLED'}
        n = len(props_c.objects) + 1
        base = f"STAND-IN Prop {n:02d}" if self.standin else f"Prop {n:02d}"
        loc = spawn_point(scene, len(props_c.objects) + 3)
        ob = build_box_object(unique_object_name(base), tuple(self.size), loc,
                              color=PROP_MAGENTA, role="prop")
        ob.show_name = True
        if self.standin:
            ob[STANDIN_KEY] = True
            ob.color = STANDIN_PINK
        props_c.objects.link(ob)
        _select_only(context, ob)
        request_sync(0.0)
        return {'FINISHED'}


class BBST_OT_obj_action(bpy.types.Operator):
    """Act on one staged object from the list"""
    bl_idname = "bbst.obj_action"
    bl_label = "Object Action"
    bl_options = {'REGISTER', 'UNDO'}

    obj_name: bpy.props.StringProperty()
    action: bpy.props.EnumProperty(items=[
        ('SELECT', "Select", ""), ('LOCK', "Lock", ""), ('DELETE', "Delete", ""),
        ('EYE', "Eyeline", ""), ('FLOOR', "Drop to floor", "")])

    def execute(self, context):
        ob = bpy.data.objects.get(self.obj_name)
        if not ob:
            return {'CANCELLED'}
        if self.action == 'SELECT':
            for sel in context.selected_objects:
                sel.select_set(False)
            ob.select_set(True)
            context.view_layer.objects.active = ob
        elif self.action == 'LOCK':
            locked = not ob.get(LOCK_KEY, False)
            ob[LOCK_KEY] = locked
            ob.lock_location = (locked, locked, True if ob.get(ROLE_KEY) == "char" else locked)
            ob.lock_rotation = (True, True, locked) if ob.get(ROLE_KEY) == "char" else (locked, locked, locked)
            ob.hide_select = locked
        elif self.action == 'DELETE':
            sc = context.scene
            was_cam = ob.type == 'CAMERA'
            bpy.data.objects.remove(ob)
            if was_cam and is_staging(sc) and sc.camera is None:
                cams = stage_cams(sc)
                if cams:
                    sc.camera = cams[0]      # playblast and F12 need a scene camera
            request_sync(0.0)
        elif self.action == 'FLOOR':
            dg = context.evaluated_depsgraph_get()
            origin = ob.location.copy()
            origin.z += 2.0
            ob.hide_set(True)
            hit, loc, *_ = context.scene.ray_cast(dg, origin, Vector((0, 0, -1)))
            ob.hide_set(False)
            if hit:
                ob.location.z = loc.z
        elif self.action == 'EYE':
            area = view3d_area(context)
            if area and ob.get(ROLE_KEY) == "char":
                r3d = area.spaces.active.region_3d
                head = ob.matrix_world @ Vector((0, 0, ob.dimensions.z * 0.95))
                fwd = (ob.matrix_world.to_3x3() @ Vector((0, 1, 0))).normalized()
                # the viewpoint sits just in front of and above the head, never inside the mesh
                eye = head + fwd * 0.35 + Vector((0, 0, 0.08))
                r3d.view_perspective = 'PERSP'
                if hasattr(r3d, "lock_rotation"):
                    r3d.lock_rotation = False
                r3d.view_rotation = (-fwd).to_track_quat('Z', 'Y')
                dist = 1.5
                r3d.view_location = eye + fwd * dist
                r3d.view_distance = dist
        return {'FINISHED'}


class BBST_UL_objects(bpy.types.UIList):
    def draw_item(self, context, layout, data, item, icon, active_data, active_prop, index):
        ob = item
        row = layout.row(align=True)
        row.prop(ob, "color", text="")
        row.prop(ob, "name", text="", emboss=False)
        locked = ob.get(LOCK_KEY, False)
        op = row.operator("bbst.obj_action", text="", icon='LOCKED' if locked else 'UNLOCKED')
        op.obj_name = ob.name; op.action = 'LOCK'
        row.prop(ob, "hide_viewport", text="", emboss=False,
                 icon='HIDE_ON' if ob.hide_viewport else 'HIDE_OFF')
        if ob.get(ROLE_KEY) == "char":
            op = row.operator("bbst.obj_action", text="", icon='USER')   # eyeline: look as this character
            op.obj_name = ob.name; op.action = 'EYE'
        op = row.operator("bbst.obj_action", text="", icon='X')
        op.obj_name = ob.name; op.action = 'DELETE'


# ------------------------------------------------------------------ beats operators

class BBST_OT_beat_add(bpy.types.Operator):
    """Add a beat after the last one and save everyone's positions to it"""
    bl_idname = "bbst.beat_add"
    bl_label = "Add Beat"
    bl_options = {'REGISTER', 'UNDO'}

    def execute(self, context):
        scene = context.scene
        st = scene.bb_st
        upgrade_beats(scene)
        if st.beats:
            frame = beat_out(st.beats[-1]) + max(1, round(st.beat_spacing * fps(scene)))
        else:
            frame = 1
        _QUIET["beats"] = True
        try:
            b = st.beats.add()
            b.move_s = st.beat_spacing if len(st.beats) > 1 else 0.0
            b.hold_s = 0.0
            b.frame = b.frame_out = frame
        finally:
            _QUIET["beats"] = False
        sync_markers(scene)
        # key the current (just-arranged) positions FIRST — setting beat_index jumps the
        # playhead (click-to-jump), and any frame change before saving re-evaluates the
        # action and wipes the arrangement
        save_beat(scene, len(st.beats) - 1)
        for other in st.beats:      # the arrangement just moved into the new beat
            other.dirty = False
        st.beat_index = len(st.beats) - 1
        scene.frame_set(frame)
        scene.frame_end = max(frame, scene.frame_start + 1)
        return {'FINISHED'}


class BBST_OT_beat_save(bpy.types.Operator):
    """Save everyone's current positions to the active beat"""
    bl_idname = "bbst.beat_save"
    bl_label = "Save Beat"
    bl_options = {'REGISTER', 'UNDO'}

    def execute(self, context):
        scene = context.scene
        st = scene.bb_st
        if not st.beats:
            return {'CANCELLED'}
        save_beat(scene, _clamped_beat(st))
        return {'FINISHED'}


class BBST_OT_beat_goto(bpy.types.Operator):
    """Jump to a beat"""
    bl_idname = "bbst.beat_goto"
    bl_label = "Go to Beat"
    index: bpy.props.IntProperty()

    def execute(self, context):
        scene = context.scene
        st = scene.bb_st
        if 0 <= self.index < len(st.beats):
            st.beat_index = self.index
            scene.frame_set(st.beats[self.index].frame)
        return {'FINISHED'}


class BBST_OT_beat_delete(bpy.types.Operator):
    """Delete the active beat (keeps the time of the others)"""
    bl_idname = "bbst.beat_delete"
    bl_label = "Delete Beat"
    bl_options = {'REGISTER', 'UNDO'}

    def execute(self, context):
        scene = context.scene
        st = scene.bb_st
        if not st.beats:
            return {'CANCELLED'}
        i = _clamped_beat(st)
        upgrade_beats(scene)
        cur = beat_at_frame(scene)
        if cur is not None and cur != i and st.beats[cur].dirty:
            save_beat(scene, cur)
        poses = sample_beat_poses(scene)
        for p in poses.values():
            del p[i]
        start = st.beats[0].frame
        # markers are matched by name (B1, B2...): retire this beat's marker and rename the later
        # ones now, or each later beat takes over the marker (and camera cut) of the one before
        dead = beat_marker(scene, i)
        later = [beat_marker(scene, j) for j in range(i + 1, len(st.beats))]
        if dead is not None:
            scene.timeline_markers.remove(dead)
        for j, mk in enumerate(later, start=i):
            if mk is not None:
                rest = mk.name.split(" ", 1)
                mk.name = f"B{j + 1}" + (" " + rest[1] if len(rest) > 1 else "")
        st.beats.remove(i)
        if len(st.beats):
            _QUIET["beats"] = True
            try:
                if i == 0:
                    st.beats[0].move_s = 0.0
                write_beat_layout(scene, poses, start)
            finally:
                _QUIET["beats"] = False
        st.beat_index = max(0, i - 1)
        sync_markers(scene)
        return {'FINISHED'}


class BBST_OT_play(bpy.types.Operator):
    """Play / pause the staging"""
    bl_idname = "bbst.play"
    bl_label = "Play / Pause"

    def execute(self, context):
        scene = context.scene
        if is_staging(scene) and not (context.screen and context.screen.is_animation_playing):
            i = beat_at_frame(scene)
            if i is not None and scene.bb_st.beats[i].dirty:
                save_beat(scene, i)      # playback re-reads the keys and would wipe unsaved moves
        bpy.ops.screen.animation_play()
        return {'FINISHED'}


class BBST_OT_from_start(bpy.types.Operator):
    """Jump to the first beat"""
    bl_idname = "bbst.from_start"
    bl_label = "From Start"

    def execute(self, context):
        st = context.scene.bb_st
        if st.beats:
            st.beat_index = 0
        return {'FINISHED'}


class BBST_OT_step_beat(bpy.types.Operator):
    """Skip to the next / previous beat"""
    bl_idname = "bbst.step_beat"
    bl_label = "Step Beat"
    forward: bpy.props.BoolProperty(default=True)

    def execute(self, context):
        scene = context.scene
        st = scene.bb_st
        if st.beats:     # from the playhead, not from the highlighted row
            f = scene.frame_current
            fr = [b.frame for b in st.beats]
            if self.forward:
                i = next((k for k, x in enumerate(fr) if x > f + 0.5), len(fr) - 1)
            else:
                i = next((k for k in reversed(range(len(fr))) if fr[k] < f - 0.5), 0)
            st.beat_index = i
        return {'FINISHED'}


class BBST_OT_fit_range(bpy.types.Operator):
    """Set the playback range to the beats"""
    bl_idname = "bbst.fit_range"
    bl_label = "Fit Range to Beats"

    def execute(self, context):
        scene = context.scene
        st = scene.bb_st
        if st.beats:
            scene.frame_start = st.beats[0].frame
            scene.frame_end = max(beat_out(st.beats[-1]), st.beats[0].frame + 1)
        return {'FINISHED'}


class BBST_UL_beats(bpy.types.UIList):
    def draw_item(self, context, layout, data, item, icon, active_data, active_prop, index):
        # data is the BBST_Props group itself (the list lives on it)
        b = item
        row = layout.row(align=True)
        active = (getattr(active_data, active_prop) == index)
        # the badge is the beat's save state (orange = unsaved moves); click it to jump
        op = row.operator("bbst.beat_goto", text="", emboss=active, depress=active,
                          icon='STRIP_COLOR_02' if b.dirty else 'DECORATE_KEYFRAME')
        op.index = index
        tag = row.row(align=True)
        tag.ui_units_x = 1.3
        tag.label(text=f"B{index + 1}")
        row.prop(b, "label", text="", emboss=False, placeholder="beat name")
        nums = row.row(align=True)
        nums.ui_units_x = 7.2
        mv = nums.row(align=True)
        mv.enabled = index > 0                      # the first beat has nothing to move from
        mv.prop(b, "move_s", text="")
        nums.prop(b, "hold_s", text="")


# ------------------------------------------------------------------ cameras

class BBST_OT_cam_add(bpy.types.Operator):
    """Add a camera in the middle of the studio at eye level, looking forward"""
    bl_idname = "bbst.cam_add"
    bl_label = "Add Camera"
    bl_options = {'REGISTER', 'UNDO'}

    lens: bpy.props.FloatProperty(name="Lens", default=35.0)

    def execute(self, context):
        scene = context.scene
        if not is_staging(scene):
            self.report({'ERROR'}, "Open a staging first")
            return {'CANCELLED'}
        ob = make_stage_camera(scene, self.lens)
        if ob is None:
            return {'CANCELLED'}
        st = scene.bb_st
        if scene.camera is None:
            scene.camera = ob
        if st.cam0 is None:
            st.cam0 = ob
        elif st.cam1 is None or st.cam1 == st.cam0:
            st.cam1 = ob          # the second camera pane picks up the new camera
        request_sync(0.0)
        return {'FINISHED'}


class BBST_OT_cam_look(bpy.types.Operator):
    """Look through this camera in the clicked viewport"""
    bl_idname = "bbst.cam_look"
    bl_label = "Look Through"
    cam_name: bpy.props.StringProperty()

    def execute(self, context):
        ob = bpy.data.objects.get(self.cam_name)
        if not ob:
            return {'CANCELLED'}
        area = context.area if context.area and context.area.type == 'VIEW_3D' else view3d_area(context)
        space = area.spaces.active
        space.use_local_camera = True
        space.camera = ob
        space.region_3d.view_perspective = 'CAMERA'
        return {'FINISHED'}


class BBST_OT_cam_bind(bpy.types.Operator):
    """Cut to this camera at the active beat during playback"""
    bl_idname = "bbst.cam_bind"
    bl_label = "Cut Here at Beat"
    cam_name: bpy.props.StringProperty()

    def execute(self, context):
        scene = context.scene
        st = scene.bb_st
        ob = bpy.data.objects.get(self.cam_name)
        if not (ob and st.beats):
            return {'CANCELLED'}
        b = st.beats[_clamped_beat(st)]
        for m in scene.timeline_markers:
            if m.frame == b.frame:
                m.camera = ob
        return {'FINISHED'}


# ------------------------------------------------------------------ layout

# ------------------------------------------------------------------ panes + visibility engine
#
# Stage Mode visibility is a pure function of stored state: every staging remembers what each
# pane shows (world, display, camera) and which level the plan works on. sync_window() applies
# that state to the panes with Blender's LOCAL VIEW (per object, per pane — readable and
# settable, no index arithmetic, no global fallback) and a SECTION-CUT clip plane for levels.
# It is idempotent: running it once or ten times gives the same result, and it re-checks what
# each pane really shows afterwards (Aman's v0.7 dry run broke on stateful toggles).

def _set_top_view(space):
    r3d = space.region_3d
    r3d.view_perspective = 'ORTHO'
    r3d.view_rotation = Quaternion((1, 0, 0, 0))
    if hasattr(r3d, "lock_rotation"):
        r3d.lock_rotation = True
    ov = space.overlay
    ov.show_floor = False
    ov.show_axis_x = False
    ov.show_axis_y = False


def stage_cams(scene):
    c = sub_coll(scene, "STAGE", "Cameras")
    return [o for o in c.objects if o.type == 'CAMERA'] if c else []


def stage_panes(window):
    """Role → area in the BB Stage screen: the rightmost 3D view is the working pane, the
    others are camera panes from the top down (CAM0, CAM1, ...)."""
    if window is None or window.screen is None:
        return {}
    v3 = [a for a in window.screen.areas if a.type == 'VIEW_3D']
    if not v3:
        return {}
    work = max(v3, key=lambda a: (a.x + a.width, a.width * a.height))
    roles = {"WORK": work}
    for i, a in enumerate(sorted([a for a in v3 if a != work], key=lambda a: (a.x, -a.y))):
        roles[f"CAM{i}"] = a
    return roles


def pane_role(window, area):
    if window is None or area is None:
        return None
    for role, a in stage_panes(window).items():
        if a == area:
            return role
    return None


def _role_attrs(role):
    if role == "WORK":
        return "work_world", "work_shading", None
    if role == "CAM0":
        return "cam0_world", "cam0_shading", "cam0"
    return "cam1_world", "cam1_shading", "cam1"


def pane_world(scene, role):
    if not role or not is_staging(scene):
        return 'SET'
    return getattr(scene.bb_st, _role_attrs(role)[0])


def pane_world_of(scene, space):
    """Legacy helper (outputs): world of the pane that owns this space."""
    for win in bpy.context.window_manager.windows:
        for role, a in stage_panes(win).items():
            if a.spaces.active == space:
                return pane_world(scene, role)
    return 'SET'


def classify_panes(screen, scene):
    """Legacy helper (outputs): (camera panes, [working pane])."""
    win = next((w for w in bpy.context.window_manager.windows if w.screen == screen), None)
    roles = stage_panes(win) if win else {}
    cams = [roles[r] for r in sorted(roles) if r.startswith("CAM")]
    return cams, ([roles["WORK"]] if "WORK" in roles else [])


def pane_camera(scene, role):
    st = scene.bb_st
    cams = stage_cams(scene)
    if not cams or not role:
        return None
    cattr = _role_attrs(role)[2]
    cam = getattr(st, cattr) if cattr else None
    if cam is not None and cam in cams:
        return cam
    return cams[0] if role == "CAM0" else cams[min(1, len(cams) - 1)]


def _declutter(space, names=True, sidebar=False):
    space.show_region_toolbar = False
    space.show_region_tool_header = False   # active-tool strip (and add-on widgets in it)
    try:
        space.show_region_ui = sidebar
    except Exception:
        pass
    # gizmos on, but only the active tool's handles (move / rotate / scale on what you click)
    space.show_gizmo = True
    for attr, val in (("show_gizmo_navigate", False), ("show_gizmo_context", True), ("show_gizmo_tool", True),
                      ("show_gizmo_object_translate", False), ("show_gizmo_object_rotate", False),
                      ("show_gizmo_object_scale", False), ("show_gizmo_empty_image", False),
                      ("show_gizmo_empty_force_field", False), ("show_gizmo_light_size", False),
                      ("show_gizmo_light_look_at", False), ("show_gizmo_camera_lens", False),
                      ("show_gizmo_camera_dof_distance", False)):
        try:
            setattr(space, attr, val)
        except Exception:
            pass
    ov = space.overlay
    ov.show_floor = False
    ov.show_axis_x = False
    ov.show_axis_y = False
    ov.show_cursor = False
    ov.show_object_origins = False
    ov.show_relationship_lines = False
    ov.show_text = names


def visibility_plan(scene):
    """Which objects belong to which world of this staging (names; computed fresh)."""
    sett, studio, boundary, cams, stage = set(), set(), set(), set(), set()
    for c in layer_colls(scene, "SET"):
        for ob in coll_objects(c):
            if ob.type in SET_TYPES or (ob.type == 'EMPTY' and ob.instance_type == 'COLLECTION'):
                sett.add(ob.name)
    for c in layer_colls(scene, "STUDIO"):
        for ob in coll_objects(c):
            (boundary if ob.get(ROLE_KEY) == "boundary" else studio).add(ob.name)
    for c in layer_colls(scene, "STAGE"):
        for ob in coll_objects(c):
            (cams if ob.type == 'CAMERA' else stage).add(ob.name)
    return dict(set=sett, studio=studio, boundary=boundary, cams=cams, stage=stage)


def desired_names(plan, role, world):
    names = set(plan["stage"])
    if role == "WORK":
        names |= plan["cams"] | plan["boundary"]
    if world in ('STUDIO', 'GHOST'):
        names |= plan["studio"]
    if world in ('SET', 'GHOST'):
        names |= plan["set"]
    return names


def plan_cut(scene, space):
    """Section-cut height for the working pane, or None for no cut."""
    fs = fstate()
    st = scene.bb_st
    g, u = (fs.level1_cut, fs.ceiling_cut) if fs is not None else (5.5, 9.5)
    if st.active_level == 'GROUND':
        return g
    if st.active_level == 'L1':
        return u
    return u if space.region_3d.view_perspective == 'ORTHO' else None


def apply_cut(win, area, z):
    sp = area.spaces.active
    r3d = sp.region_3d
    if z is None:
        if r3d.use_clip_planes:
            r3d.use_clip_planes = False
        return
    want = [(0.0, 0.0, -1.0, float(z)), (0.0, 0.0, 1.0, 1000.0),
            (1.0, 0.0, 0.0, 1e5), (-1.0, 0.0, 0.0, 1e5), (0.0, 1.0, 0.0, 1e5), (0.0, -1.0, 0.0, 1e5)]
    if not r3d.use_clip_planes:
        # Blender only honours Python-set planes after its own clip operator ran once
        region = next((r for r in area.regions if r.type == 'WINDOW'), None)
        if region is None:
            return
        try:
            with bpy.context.temp_override(window=win, screen=win.screen, area=area, region=region):
                bpy.ops.view3d.clip_border(xmin=0, xmax=region.width, ymin=0, ymax=region.height,
                                           wait_for_input=False)
        except Exception as e:
            _SYNC["last_error"] = f"cut: {e}"
            return
    if [tuple(round(v, 4) for v in p) for p in r3d.clip_planes] != [tuple(round(v, 4) for v in p) for p in want]:
        r3d.clip_planes = want


_SYNC = {"pending": False, "last_error": "", "last_ok": 0}


_LAST_STG = {}     # window -> the staging it last showed (scene dropdown and re-enter go back to it)


def _last_staging(win):
    s = bpy.data.scenes.get(_LAST_STG.get(win.as_pointer(), "")) if win is not None else None
    return s if is_staging(s) else None


def request_sync(delay=0.02):
    if _SYNC["pending"]:
        return
    _SYNC["pending"] = True
    try:
        bpy.app.timers.register(_bbst_sync_timer, first_interval=max(0.0, delay))
    except Exception:
        _SYNC["pending"] = False


def _bbst_sync_timer():
    _SYNC["pending"] = False
    try:
        sync_all()
    except Exception as e:
        import traceback
        traceback.print_exc()
        _SYNC["last_error"] = f"sync: {e}"
    return None


def _is_stage_ws(ws):
    return ws is not None and (ws.get("bb_stage") or ws.name == WS_NAME)


def stage_windows():
    wm = bpy.context.window_manager
    return [w for w in wm.windows if _is_stage_ws(w.workspace)] if wm else []


def stage_on():   # noqa: F811 — Stage Mode is derived from the workspace, never stored
    try:
        return bool(stage_windows())
    except Exception:
        return False


def sync_all():
    for win in stage_windows():
        scene = win.scene
        if not is_staging(scene):
            ss = stagings()
            if ss:
                win.scene = _last_staging(win) or ss[0]   # never the bare set: back to the last staging
                request_sync(0.05)
            continue
        sync_window(win, scene)


def _ensure_local_view(win, area, scene):
    sp = area.spaces.active
    if sp.local_view is not None:
        return True
    vl = win.view_layer
    b = boundary_of(scene)
    cand = [b] if b is not None else []
    cand += [o for k in ("STUDIO", "STAGE") for c in layer_colls(scene, k) for o in coll_objects(c)][:50]
    pick = next((o for o in cand if o.visible_get(view_layer=vl) and not o.hide_select), None)
    if pick is None:
        return False
    prev_sel = [o for o in scene.objects if o.select_get(view_layer=vl)]
    prev_act = vl.objects.active
    for o in prev_sel:
        o.select_set(False, view_layer=vl)
    pick.select_set(True, view_layer=vl)
    region = next((r for r in area.regions if r.type == 'WINDOW'), None)
    try:
        if not pick.select_get(view_layer=vl):
            raise RuntimeError(f"'{pick.name}' cannot be selected")
        with bpy.context.temp_override(window=win, screen=win.screen, area=area, region=region):
            bpy.ops.view3d.localview(frame_selected=False)
    except Exception as e:
        _SYNC["last_error"] = f"local view: {e}"
    pick.select_set(False, view_layer=vl)
    for o in prev_sel:
        try:
            o.select_set(True, view_layer=vl)
        except RuntimeError:
            pass
    try:
        vl.objects.active = prev_act
    except Exception:
        pass
    return sp.local_view is not None


def sync_window(win, scene):
    st = scene.bb_st
    roles = stage_panes(win)
    if not roles:
        return
    _LAST_STG[win.as_pointer()] = scene.name
    _SYNC["last_error"] = ""      # this pass reports afresh; cut and local-view errors add to it
    sync_peg_colors(scene)
    plan = visibility_plan(scene)
    objs = list(scene.objects)
    vl = win.view_layer
    errors = []
    for role, area in roles.items():
        sp = area.spaces.active
        if getattr(sp, "use_local_collections", False):
            sp.use_local_collections = False
        if not _ensure_local_view(win, area, scene):
            errors.append(f"{role}: could not isolate (too many local views in this file?)")
            continue
        world = pane_world(scene, role)
        want = desired_names(plan, role, world)
        for ob in objs:
            try:
                ob.local_view_set(sp, ob.name in want)
            except RuntimeError:
                pass
        sh = sp.shading
        if world in ('STUDIO', 'GHOST'):
            if sh.type != 'SOLID':
                sh.type = 'SOLID'
            sh.color_type = 'OBJECT'
        else:
            kind = getattr(st, _role_attrs(role)[1])
            forced = role == "WORK" and kind != 'SOLID' and plan_cut(scene, sp) is not None
            if forced:
                kind = 'SOLID'      # Blender clips only in Solid/Wireframe: a cut plan stays Solid
            try:
                if sh.type != kind:
                    sh.type = kind
            except TypeError:
                sh.type = 'SOLID'
            if sh.type == 'SOLID':
                ct = 'TEXTURE' if forced else 'MATERIAL'
                if sh.color_type != ct:
                    sh.color_type = ct
        if sh.show_xray:
            sh.show_xray = False
        if role.startswith("CAM"):
            cam = pane_camera(scene, role)
            if cam is not None:
                if not sp.use_local_camera:
                    sp.use_local_camera = True
                if sp.camera != cam:
                    sp.camera = cam
                if sp.region_3d.view_perspective != 'CAMERA':
                    sp.region_3d.view_perspective = 'CAMERA'
            if sp.lock_camera and not any(("WALK" in o.bl_idname.upper() or "FLY" in o.bl_idname.upper())
                                          for o in win.modal_operators):
                sp.lock_camera = False   # a finished walk must not leave the pane steering the camera
            if sp.region_3d.use_clip_planes:
                sp.region_3d.use_clip_planes = False
        else:
            if world == 'STUDIO':
                apply_cut(win, area, None)
            else:
                apply_cut(win, area, plan_cut(scene, sp))
    ghost_tint(scene, True)
    apply_passepartout(scene)
    try:
        vl.update()
    except Exception:
        pass
    for role, area in roles.items():
        sp = area.spaces.active
        if sp.local_view is None:
            continue
        want = desired_names(plan, role, pane_world(scene, role))
        bad = 0
        for ob in objs:
            try:
                if not ob.visible_get(view_layer=vl):
                    continue   # hidden by the set itself (monitor icon) — not ours to show
                if ob.visible_get(view_layer=vl, viewport=sp) != (ob.name in want):
                    bad += 1
            except Exception:
                pass
        if bad:
            errors.append(f"{role}: {bad} object(s) did not follow")
    _SYNC["last_error"] = "; ".join(e for e in [_SYNC["last_error"]] + errors if e)
    if errors:
        print("BB Stage sync:", _SYNC["last_error"])
    for a in roles.values():
        a.tag_redraw()


# ------------------------------------------------------------------ pane operators

class BBST_OT_pane_world(bpy.types.Operator):
    """What this pane shows: the grey studio, the finished set, or both (set see-through)"""
    bl_idname = "bbst.pane_world"
    bl_label = "Pane World"
    world: bpy.props.EnumProperty(items=WORLD_ITEMS)

    def execute(self, context):
        role = pane_role(context.window, context.area)
        if not role or not is_staging(context.scene):
            return {'CANCELLED'}
        setattr(context.scene.bb_st, _role_attrs(role)[0], self.world)
        request_sync(0.0)
        return {'FINISHED'}


class BBST_OT_pane_view(bpy.types.Operator):
    """Flip this pane between the locked top-down plan and free 3D orbit"""
    bl_idname = "bbst.pane_view"
    bl_label = "Top-Down / 3D"

    def execute(self, context):
        if context.area is None or context.area.type != 'VIEW_3D':
            return {'CANCELLED'}
        r3d = context.area.spaces.active.region_3d
        if r3d.view_perspective == 'ORTHO':
            r3d.lock_rotation = False
            r3d.view_perspective = 'PERSP'
            r3d.view_rotation = Matrix.Rotation(math.radians(60), 3, 'X').to_quaternion()
        else:
            r3d.view_perspective = 'ORTHO'
            r3d.view_rotation = Quaternion((1, 0, 0, 0))
            r3d.lock_rotation = True
            scene = context.scene
            if is_staging(scene):      # back to the studio plan (an eyeline leaves it 1.5 m from a head)
                st = scene.bb_st
                r3d.view_location = studio_center(scene)
                r3d.view_distance = max(st.studio_w, st.studio_d) * 1.4
        r3d.use_clip_planes = False    # the next sync re-runs the cut from this view (no stale clip box)
        request_sync(0.0)
        return {'FINISHED'}


class BBST_OT_pane_cam(bpy.types.Operator):
    """Look through this camera in this pane"""
    bl_idname = "bbst.pane_cam"
    bl_label = "Pane Camera"
    cam_name: bpy.props.StringProperty()

    def execute(self, context):
        ob = bpy.data.objects.get(self.cam_name)
        role = pane_role(context.window, context.area)
        if not (ob and role and role.startswith("CAM") and is_staging(context.scene)):
            return {'CANCELLED'}
        setattr(context.scene.bb_st, _role_attrs(role)[2], ob)
        request_sync(0.0)
        return {'FINISHED'}


class BBST_OT_pane_lens(bpy.types.Operator):
    """Set this pane's camera lens"""
    bl_idname = "bbst.pane_lens"
    bl_label = "Lens"
    mm: bpy.props.FloatProperty(default=35)

    def execute(self, context):
        cam = pane_camera(context.scene, pane_role(context.window, context.area))
        if cam is None:
            return {'CANCELLED'}
        cam.data.lens = self.mm
        return {'FINISHED'}


LENS_PRESETS = (18, 24, 35, 50, 85)
SHADING_LABELS = {'SOLID': "Solid", 'MATERIAL': "Preview", 'RENDERED': "Render"}


def apply_passepartout(scene):
    """Black outside the camera frame (Settings: Black outside camera)."""
    alpha = 1.0 if scene.bb_st.black_outside else 0.5
    for c in stage_cams(scene):
        if not c.data.show_passepartout:
            c.data.show_passepartout = True
        if abs(c.data.passepartout_alpha - alpha) > 1e-4:
            c.data.passepartout_alpha = alpha


class BBST_OT_lens_step(bpy.types.Operator):
    """Step this camera through the standard lenses (18 · 24 · 35 · 50 · 85)"""
    bl_idname = "bbst.lens_step"
    bl_label = "Lens Step"
    forward: bpy.props.BoolProperty(default=True)

    def execute(self, context):
        cam = pane_camera(context.scene, pane_role(context.window, context.area))
        if cam is None:
            return {'CANCELLED'}
        cur = cam.data.lens
        if self.forward:
            nxt = next((p for p in LENS_PRESETS if p > cur + 0.01), LENS_PRESETS[-1])
        else:
            nxt = next((p for p in reversed(LENS_PRESETS) if p < cur - 0.01), LENS_PRESETS[0])
        cam.data.lens = nxt
        return {'FINISHED'}


class BBST_OT_pane_shading(bpy.types.Operator):
    """How this pane draws the set: Solid, material Preview, or full Render"""
    bl_idname = "bbst.pane_shading"
    bl_label = "Pane Display"
    kind: bpy.props.EnumProperty(items=SHADING_ITEMS)

    def execute(self, context):
        role = pane_role(context.window, context.area)
        if not role or not is_staging(context.scene):
            return {'CANCELLED'}
        setattr(context.scene.bb_st, _role_attrs(role)[1], self.kind)
        request_sync(0.0)
        return {'FINISHED'}


_CAM_ENUM_CACHE = []   # dynamic enum strings must stay referenced


def _cam_enum_items(self, context):
    global _CAM_ENUM_CACHE
    cams = stage_cams(context.scene) if (context and is_staging(context.scene)) else []
    _CAM_ENUM_CACHE = [(c.name, c.name, "") for c in cams] or [('NONE', "No cameras", "")]
    return _CAM_ENUM_CACHE


class BBST_OT_pane_cam_pick(bpy.types.Operator):
    """Which camera this pane looks through"""
    bl_idname = "bbst.pane_cam_pick"
    bl_label = "Camera"
    cam: bpy.props.EnumProperty(items=_cam_enum_items)

    def execute(self, context):
        ob = bpy.data.objects.get(self.cam)
        role = pane_role(context.window, context.area)
        if not (ob and role and role.startswith("CAM") and is_staging(context.scene)):
            return {'CANCELLED'}
        setattr(context.scene.bb_st, _role_attrs(role)[2], ob)
        request_sync(0.0)
        return {'FINISHED'}


class BBST_OT_pane_level(bpy.types.Operator):
    """Which floor the plan shows — everything above it is cut away"""
    bl_idname = "bbst.pane_level"
    bl_label = "Level"
    level: bpy.props.EnumProperty(items=LEVEL_ITEMS)

    def execute(self, context):
        if not is_staging(context.scene):
            return {'CANCELLED'}
        fs = fstate()
        if self.level == 'L1' and fs is not None and not fs.has_upper:
            self.report({'WARNING'}, "This set has one floor (Settings: This set has an upper floor)")
            return {'CANCELLED'}
        context.scene.bb_st.active_level = self.level
        request_sync(0.0)
        return {'FINISHED'}


def _dropdown(lay, units, op, prop, text, icon='NONE', enabled=True):
    sub = lay.row(align=True)
    sub.ui_units_x = units
    sub.enabled = enabled
    sub.operator_menu_enum(op, prop, text=text, icon=icon)


def _draw_world_shading(lay, context, role):
    scene = context.scene
    world = pane_world(scene, role)
    _dropdown(lay, 5.5, "bbst.pane_world", "world",
              dict((k, v) for k, v, _d in WORLD_ITEMS)[world], icon='SCENE_DATA')
    kind = getattr(scene.bb_st, _role_attrs(role)[1]) if role else 'SOLID'
    sp = context.space_data
    cut = role == "WORK" and sp is not None and getattr(sp, "type", "") == 'VIEW_3D' and plan_cut(scene, sp) is not None
    _dropdown(lay, 5.5, "bbst.pane_shading", "kind", "Solid" if cut else SHADING_LABELS.get(kind, "Solid"),
              icon='SHADING_RENDERED', enabled=(world == 'SET' and not cut))


def _in_stage(context):
    win = getattr(context, "window", None)
    return bool(win is not None and _is_stage_ws(win.workspace) and is_staging(context.scene))


def _stage_header_draw(self, context):
    """Owns the 3D view header in Stage Mode; Blender's own header everywhere else."""
    orig = getattr(bpy.types.VIEW3D_HT_header, "_bbst_orig_draw", None)
    try:
        if not _in_stage(context):
            if orig:
                orig(self, context)
            return
        lay = self.layout
        sp = context.space_data
        scene = context.scene
        st = scene.bb_st
        role = pane_role(context.window, context.area)
        if role and role.startswith("CAM"):
            cam = pane_camera(scene, role)
            if cam is None:      # empty state: the way to a camera, not a dead dropdown
                lay.operator("bbst.cam_add", text="Add Camera", icon='ADD')
            else:
                _dropdown(lay, 8, "bbst.pane_cam_pick", "cam", cam.name, icon='VIEW_CAMERA')
                row = lay.row(align=True)
                row.operator("bbst.lens_step", text="", icon='TRIA_LEFT').forward = False
                sub = row.row(align=True)
                sub.ui_units_x = 4
                sub.prop(cam.data, "bbst_lens_mm", text="")     # whole millimetres
                row.operator("bbst.lens_step", text="", icon='TRIA_RIGHT').forward = True
            lay.separator_spacer()
            _draw_world_shading(lay, context, role)
            lay.separator_spacer()
            lay.operator("bbst.walk", text="Walk (F)", icon='VIEW_PAN')
        else:
            top = sp.region_3d.view_perspective == 'ORTHO'
            lay.operator("bbst.pane_view", text="Top-Down" if top else "3D",
                         icon='AXIS_TOP' if top else 'VIEW_PERSPECTIVE')
            _dropdown(lay, 7, "bbst.pane_level", "level",
                      dict((k, v) for k, v, _d in LEVEL_ITEMS)[st.active_level], icon='CON_FLOOR')
            lay.separator_spacer()
            _draw_world_shading(lay, context, role or "WORK")
            lay.separator_spacer()
            if _mode() == 'ARTIST':
                r = lay.row()
                r.alert = st.needs_place
                r.operator("bbst.place_space", text="Place Studio Space", icon='OBJECT_ORIGIN')
        if _SYNC.get("last_error"):
            r = lay.row()
            r.alert = True
            r.operator("bbst.fix_screen", text="Fix", icon='ERROR')
    except Exception as e:   # a raising header blanks the bar: fall back to Blender's own
        print("BB Stage header:", e)
        if orig:
            try:
                orig(self, context)
            except Exception:
                pass


def _stage_topbar_draw(self, context):
    """No menus, no workspace tabs: where you are, Save and the way out. Blender draws this
    class once per top-bar region, so the content is split by region."""
    orig = getattr(bpy.types.TOPBAR_HT_upper_bar, "_bbst_orig_draw", None)
    try:
        if not _in_stage(context):
            if orig:
                orig(self, context)
            return
        lay = self.layout
        if getattr(context.region, "alignment", "") == 'RIGHT':
            lay.operator("wm.save_mainfile", text="Save", icon='FILE_TICK')
            lay.operator("bbst.exit_stage", text="Exit", icon='LOOP_BACK')
        else:
            lay.label(text=f"BB Stage — {staging_label(context.scene)}", icon='VIEW_CAMERA')
    except Exception as e:
        print("BB Stage topbar:", e)
        if orig:
            orig(self, context)


def _stage_status_draw(self, context):
    orig = getattr(bpy.types.STATUSBAR_HT_header, "_bbst_orig_draw", None)
    try:
        if not _in_stage(context):
            if orig:
                orig(self, context)
            return
        lay = self.layout
        lay.template_input_status()
        lay.separator_spacer()
        lay.template_reports_banner()      # operator messages (place the studio, output paths...)
        lay.template_running_jobs()
    except Exception:
        if orig:
            orig(self, context)


_TAKEOVERS = (("VIEW3D_HT_header", "_stage_header_draw"),
              ("TOPBAR_HT_upper_bar", "_stage_topbar_draw"),
              ("STATUSBAR_HT_header", "_stage_status_draw"))


def _take_over_headers():
    """The original draw is kept on the Blender class itself, so a reloaded copy of this
    add-on (embedded text block + installed add-on) never chains onto a stale copy."""
    for cls_name, fn_name in _TAKEOVERS:
        cls = getattr(bpy.types, cls_name, None)
        if cls is None:
            continue
        if not hasattr(cls, "_bbst_orig_draw"):
            cls._bbst_orig_draw = cls.draw
        cls.draw = globals()[fn_name]


def _release_headers():
    for cls_name, _fn in _TAKEOVERS:
        cls = getattr(bpy.types, cls_name, None)
        if cls is not None and hasattr(cls, "_bbst_orig_draw"):
            cls.draw = cls._bbst_orig_draw
            del cls._bbst_orig_draw


def _blenderkit_set(on):
    """Kept for older call sites. BB Stage no longer disables other add-ons (that wrote user
    preferences); BlenderKit's widget lives in the tool header, which Stage Mode hides."""
    return


def _hide_foreign_v3d_panels():
    """In Stage Mode the sidebar holds BB Stage alone. The original poll is parked on the
    panel class itself so any copy of this add-on can restore it."""
    for cls in list(bpy.types.Panel.__subclasses__()):
        try:
            if getattr(cls, "bl_space_type", "") != 'VIEW_3D' or getattr(cls, "bl_region_type", "") != 'UI':
                continue
            if cls.__name__.startswith("BBST") or getattr(cls, "_bbst_hidden", False):
                continue
            if not getattr(cls, "is_registered", False):
                continue
            had_own = "poll" in cls.__dict__
            orig = cls.__dict__.get("poll")
            inherited = None if had_own else getattr(cls, "poll", None)   # poll from a mixin
            bpy.utils.unregister_class(cls)
            cls._bbst_hidden = True
            cls._bbst_had_poll = had_own
            cls._bbst_orig_poll = orig
            cls._bbst_inh_poll = inherited
            cls.poll = classmethod(lambda c, ctx: (not _in_stage(ctx)) and (
                c._bbst_orig_poll.__func__(c, ctx) if c._bbst_orig_poll
                else (c._bbst_inh_poll(ctx) if getattr(c, "_bbst_inh_poll", None) else True)))
            bpy.utils.register_class(cls)
        except Exception:
            continue


def _restore_foreign_v3d_panels():
    for cls in list(bpy.types.Panel.__subclasses__()):
        if not getattr(cls, "_bbst_hidden", False):
            continue
        try:
            reg = getattr(cls, "is_registered", False)
            if reg:
                bpy.utils.unregister_class(cls)
            if cls._bbst_had_poll:
                cls.poll = cls._bbst_orig_poll
            elif "poll" in cls.__dict__:
                del cls.poll
            del cls._bbst_hidden, cls._bbst_had_poll, cls._bbst_orig_poll
            if "_bbst_inh_poll" in cls.__dict__:
                del cls._bbst_inh_poll
            if reg:
                bpy.utils.register_class(cls)
        except Exception:
            continue


def _hide_foreign_prop_panels():
    return


def _restore_foreign_prop_panels():
    """v0.3 hid Properties-editor panels; make sure none stay hidden."""
    _restore_foreign_v3d_panels()


def _flip_header_to_bottom(window, area):
    region = next((r for r in area.regions if r.type == 'HEADER'), None)
    if region is not None and getattr(region, "alignment", 'TOP') == 'TOP':
        try:
            with bpy.context.temp_override(window=window, screen=window.screen, area=area, region=region):
                bpy.ops.screen.region_flip()
        except Exception:
            pass


def free_local_collection_slots():
    """v0.7 used per-viewport local collections (Blender caps them at 16 per file and then
    silently falls back to GLOBAL hiding). Stage Mode no longer uses them: switch them off
    in every screen to free the slots."""
    for scr in bpy.data.screens:
        for a in scr.areas:
            for sp in a.spaces:
                if sp.type == 'VIEW_3D' and getattr(sp, "use_local_collections", False):
                    try:
                        sp.use_local_collections = False
                    except Exception:
                        pass


def local_view_slots_used():
    n = 0
    for scr in bpy.data.screens:
        for a in scr.areas:
            for sp in a.spaces:
                if sp.type == 'VIEW_3D' and sp.local_view is not None:
                    n += 1
    return n


_PREV_WS = {"name": "Layout"}
_BUILD_STATE = {"active": False}


def stage_workspace():
    for ws in bpy.data.workspaces:
        if ws.get("bb_stage"):
            return ws
    ws = bpy.data.workspaces.get(WS_NAME)
    if ws is not None:
        ws["bb_stage"] = 1
    return ws


def _leave_edit_mode(win):
    """Stage Mode blocks Tab: never carry Edit Mode (on a shared set mesh) into it."""
    try:
        ob = win.view_layer.objects.active
        if ob is not None and ob.mode != 'OBJECT':
            area = next((a for a in win.screen.areas if a.type == 'VIEW_3D'), None)
            with bpy.context.temp_override(window=win, screen=win.screen, area=area):
                bpy.ops.object.mode_set(mode='OBJECT')
    except Exception:
        pass


def engage(win, scene):
    """Everything Stage Mode needs once a window shows the BB Stage workspace."""
    _leave_edit_mode(win)
    if is_staging(scene):
        migrate_staging(scene)
        normalize_view_layer(scene)
        cursor_to_studio(scene)
    free_local_collection_slots()
    _hide_foreign_v3d_panels()
    _build_stage_screen(scene.name)


def enter_stage_mode(context, scene):
    win = context.window
    _EXIT["pending"] = False   # this Enter overrides an Exit still pending in this tick
    _leave_edit_mode(win)      # before the scene switch, while the edited object is still active
    if win.scene != scene:
        win.scene = scene
    if not _is_stage_ws(win.workspace):
        _PREV_WS["name"] = win.workspace.name
        fs = fstate()
        if fs is not None:
            fs.prev_workspace = win.workspace.name
    ws = stage_workspace()
    if ws is None:
        before = {w.name for w in bpy.data.workspaces}
        try:
            with context.temp_override(window=win):
                bpy.ops.workspace.duplicate()
        except Exception:
            bpy.ops.workspace.duplicate()
        ws = next((w for w in bpy.data.workspaces if w.name not in before), None)
        if ws is None:
            return False
        ws.name = WS_NAME
        ws["bb_stage"] = 1
    win.workspace = ws          # always: this overrides a switch to Layout still pending from Exit
    engage(win, scene)
    return True


def exit_stage_mode(context):
    win = context.window
    prev = (bpy.data.workspaces.get(_PREV_WS["name"])
            or bpy.data.workspaces.get(getattr(fstate(), "prev_workspace", "") or "")
            or bpy.data.workspaces.get("Layout")
            or next((w for w in bpy.data.workspaces if not _is_stage_ws(w)), None))
    if prev is not None and win is not None:
        win.workspace = prev        # always: overrides an Enter still pending in this tick
    _EXIT["pending"] = True         # the switch lands next event loop; Enter must not trust the workspace yet
    _EXIT["tries"] = 0
    _EXIT["win"] = win.as_pointer() if win is not None else 0
    if not bpy.app.timers.is_registered(_bbst_after_exit):
        bpy.app.timers.register(_bbst_after_exit, first_interval=0.2)


_EXIT = {"tries": 0, "win": 0, "pending": False}


def _bbst_after_exit():
    """The workspace switch lands a moment after Exit: wait for it (up to 3 s), then clean up."""
    if stage_on():
        _EXIT["tries"] += 1
        return 0.2 if _EXIT["tries"] < 15 else None
    _EXIT["pending"] = False
    untint_everything()
    _restore_foreign_v3d_panels()
    ms = master_scene()
    for w in bpy.context.window_manager.windows:
        if w.as_pointer() == _EXIT["win"] and is_staging(w.scene) and ms is not None:
            w.scene = ms        # back on the set scene, not the staging's
    return None


class BBST_OT_enter_stage(bpy.types.Operator):
    """Stage Mode: cameras on the left, the working plan on the right, tools in the sidebar"""
    bl_idname = "bbst.enter_stage"
    bl_label = "Enter Stage Mode"

    easy: bpy.props.BoolProperty(default=False)

    def execute(self, context):
        fs = fstate()
        if fs is None:
            return {'CANCELLED'}
        fs.mode = 'EASY' if self.easy else 'ARTIST'
        if _in_stage(context) and not _EXIT["pending"]:
            apply_mode_tool(context.window)        # switching Easy ⇄ Artist changes the tool
            request_sync(0.0)
            return {'FINISHED'}
        scene = context.scene if is_staging(context.scene) else (_last_staging(context.window) or (stagings() or [None])[0])
        if scene is None:
            self.report({'ERROR'}, "No stagings yet — use New Staging first")
            return {'CANCELLED'}
        if local_view_slots_used() > 12:
            self.report({'WARNING'}, "This file has many isolated views open; if a pane stays empty, save and reopen")
        enter_stage_mode(context, scene)
        return {'FINISHED'}


class BBST_OT_exit_stage(bpy.types.Operator):
    """Back to the normal Blender layout"""
    bl_idname = "bbst.exit_stage"
    bl_label = "Exit Stage Mode"

    def execute(self, context):
        exit_stage_mode(context)
        return {'FINISHED'}


class BBST_OT_fix_screen(bpy.types.Operator):
    """Something looks wrong? Rebuild the panes and re-apply what each one should show"""
    bl_idname = "bbst.fix_screen"
    bl_label = "Fix Screen"

    def execute(self, context):
        if not _in_stage(context):
            return {'CANCELLED'}
        scene = context.scene
        free_local_collection_slots()
        migrate_staging(scene)
        normalize_view_layer(scene)
        _BUILD_STATE["active"] = False
        _build_stage_screen(scene.name)
        _SYNC["last_error"] = ""
        self.report({'INFO'}, "Screen rebuilt")
        return {'FINISHED'}


def _build_stage_screen(scene_name):
    """Shape the BB Stage screen into exactly three 3D views (one change per timer tick:
    closing or splitting areas inline can crash, and area sizes are stale until a redraw),
    then configure the panes and sync."""
    if _BUILD_STATE["active"]:
        _BUILD_STATE["again"] = scene_name
        return
    _BUILD_STATE["active"] = True
    _BUILD_STATE["again"] = None
    state = {"ticks": 0}

    def step():
        try:
            ctx = bpy.context
            win = next((w for w in ctx.window_manager.windows if _is_stage_ws(w.workspace)), None)
            state["ticks"] += 1
            if win is None:
                if state["ticks"] < 40:
                    return 0.05
                _BUILD_STATE["active"] = False
                return None
            screen = win.screen
            if state["ticks"] < 60 and (screen.show_fullscreen or screen.name.endswith("-nonnormal")):
                # a maximised pane cannot be split: go back to the normal screen first
                try:
                    with ctx.temp_override(window=win, screen=screen, area=screen.areas[0]):
                        bpy.ops.screen.back_to_previous()
                except Exception as e:
                    _SYNC["last_error"] = f"layout: {e}"
                return 0.05
            if state["ticks"] < 60:
                for a in screen.areas:     # build in Solid: a Material Preview redraw per tick is slow
                    if a.type == 'VIEW_3D' and a.spaces.active.shading.type not in ('SOLID', 'WIREFRAME'):
                        a.spaces.active.shading.type = 'SOLID'
                victim = next((a for a in screen.areas if a.type != 'VIEW_3D'), None)
                if victim is not None:
                    try:
                        with ctx.temp_override(window=win, screen=screen, area=victim):
                            bpy.ops.screen.area_close()
                    except Exception:
                        victim.ui_type = 'VIEW_3D'
                    return 0.05
                v3 = [a for a in screen.areas if a.type == 'VIEW_3D']
                if len(v3) > 3:
                    smallest = min(v3, key=lambda a: a.width * a.height)
                    try:
                        with ctx.temp_override(window=win, screen=screen, area=smallest):
                            bpy.ops.screen.area_close()
                    except Exception:
                        pass
                    return 0.05
                if len(v3) == 1:
                    with ctx.temp_override(window=win, screen=screen, area=v3[0]):
                        bpy.ops.screen.area_split(direction='VERTICAL', factor=0.40)
                    return 0.05
                if len(v3) == 2:
                    left = min(v3, key=lambda a: a.x)
                    with ctx.temp_override(window=win, screen=screen, area=left):
                        bpy.ops.screen.area_split(direction='HORIZONTAL', factor=0.5)
                    return 0.05
            _configure_stage_panes(scene_name, win)
        except Exception as e:
            import traceback
            traceback.print_exc()
            _SYNC["last_error"] = f"layout: {e}"
        _BUILD_STATE["active"] = False
        again = _BUILD_STATE.get("again")
        if again:
            _BUILD_STATE["again"] = None
            _build_stage_screen(again)
        return None

    bpy.app.timers.register(step, first_interval=0.05)


def apply_mode_tool(win):
    """Easy Mode: the Transform tool, so clicking a character, prop or wall gives handles to
    move, turn and scale it without shortcuts. Artist Mode: the Move tool (shortcuts G/R/S)."""
    work = stage_panes(win).get("WORK")
    if work is None:
        return
    tool = "builtin.transform" if _mode() == 'EASY' else "builtin.move"
    region = next((r for r in work.regions if r.type == 'WINDOW'), None)
    try:
        with bpy.context.temp_override(window=win, screen=win.screen, area=work, region=region):
            bpy.ops.wm.tool_set_by_id(name=tool)
    except Exception:
        pass


def _configure_stage_panes(scene_name, win):
    # the window's own staging wins: a build scheduled earlier must not undo a newer switch
    scene = win.scene if is_staging(win.scene) else (bpy.data.scenes.get(scene_name) or win.scene)
    if win.scene != scene and is_staging(scene):
        win.scene = scene
    roles = stage_panes(win)
    for role, a in roles.items():
        a.show_menus = False
        sp = a.spaces.active
        if getattr(sp, "use_local_collections", False):
            sp.use_local_collections = False
        _declutter(sp, names=(role == "WORK"), sidebar=(role == "WORK"))
        if role.startswith("CAM"):
            sp.lock_camera = False
            _flip_header_to_bottom(win, a)
        else:
            sp.use_local_camera = False
            _set_top_view(sp)
            sp.region_3d.use_clip_planes = False    # the sync re-runs the cut from this top view
            ui = next((r for r in a.regions if r.type == 'UI'), None)
            if ui is not None:
                try:
                    if ui.active_panel_category != "BB Stage":
                        ui.active_panel_category = "BB Stage"   # not Blender's Item tab
                except Exception:
                    pass
            if is_staging(scene):
                st = scene.bb_st
                c = studio_center(scene)
                sp.region_3d.view_location = c
                sp.region_3d.view_distance = max(st.studio_w, st.studio_d) * 1.4
    apply_mode_tool(win)
    if is_staging(scene):
        cursor_to_studio(scene)
    _WATCH[win.as_pointer()] = _window_signature(win)
    request_sync(0.0)


# ------------------------------------------------------------------ watchdog
#
# Whatever the user does — switch scene with Blender's dropdown, undo, duplicate a peg, close
# a pane, change workspace — a cheap twice-a-second check notices that the window no longer
# matches what was last applied and re-applies it.

_WATCH = {}


def _window_signature(win):
    scene = win.scene
    return (scene.name, len(scene.objects), sum(1 for a in win.screen.areas if a.type == 'VIEW_3D'),
            sum(1 for a in win.screen.areas))


def _panes_drifted(win):
    """A pane lost its isolation, or a camera pane no longer looks through its stage camera
    (scene switch picks a set camera, Ctrl+Numpad0, a middle-mouse orbit)."""
    scene = win.scene
    for role, a in stage_panes(win).items():
        sp = a.spaces.active
        if sp.local_view is None:
            return True
        if role.startswith("CAM"):
            cam = pane_camera(scene, role)
            if cam is not None and (sp.camera != cam or not sp.use_local_camera
                                    or sp.region_3d.view_perspective != 'CAMERA'):
                return True
    return False


def _bbst_watchdog():
    try:
        wm = bpy.context.window_manager
        if wm is None:
            return 0.5
        live = set()
        for win in wm.windows:
            if not _is_stage_ws(win.workspace):
                continue
            key = win.as_pointer()
            live.add(key)
            sig = _window_signature(win)
            old = _WATCH.get(key)
            if old == sig:
                # health check: a pane that lost (or never got) its isolation is re-synced
                if not _BUILD_STATE["active"] and is_staging(win.scene) and _panes_drifted(win):
                    request_sync(0.0)
                continue
            _WATCH[key] = sig
            if old is None or old[0] != sig[0] or old[2] != sig[2] or old[3] != sig[3]:
                engage(win, win.scene)          # new window / scene switch / panes changed
            else:
                request_sync(0.0)               # objects added or removed
        for key in list(_WATCH):
            if key not in live:
                del _WATCH[key]
                if not live:
                    untint_everything()
                    _restore_foreign_v3d_panels()
    except Exception as e:
        print("BB Stage watchdog:", e)
    return 0.2 if _WATCH else 0.5      # quicker while a stage window is live


class BBST_OT_walk(bpy.types.Operator):
    """Walk this view (WASD + mouse, click to finish). In a camera pane it moves the camera"""
    bl_idname = "bbst.walk"
    bl_label = "Walk"

    def invoke(self, context, event):
        if not (_in_stage(context) and context.area and context.area.type == 'VIEW_3D'):
            return {'PASS_THROUGH'}
        area = context.area
        region = next((r for r in area.regions if r.type == 'WINDOW'), None)   # the header button runs in HEADER
        try:
            with context.temp_override(area=area, region=region):
                bpy.ops.bb_sv.flythrough('INVOKE_DEFAULT')   # Set Viewer's walk flies the pane camera
            return {'FINISHED'}
        except Exception:
            pass
        sp = area.spaces.active
        was_locked = sp.lock_camera
        if sp.region_3d.view_perspective == 'CAMERA':
            sp.lock_camera = True
        try:
            with context.temp_override(area=area, region=region):
                bpy.ops.view3d.walk('INVOKE_DEFAULT')
        except Exception:
            sp.lock_camera = was_locked
            return {'CANCELLED'}
        return {'FINISHED'}


class BBST_OT_pan(bpy.types.Operator):
    """Plain middle-mouse pans the top-down plan (no Shift needed)"""
    bl_idname = "bbst.pan"
    bl_label = "Pan"

    def invoke(self, context, event):
        if not (_in_stage(context) and context.area and context.area.type == 'VIEW_3D'):
            return {'PASS_THROUGH'}
        if context.area.spaces.active.region_3d.view_perspective != 'ORTHO':
            return {'PASS_THROUGH'}   # 3D keeps Blender's normal orbit
        bpy.ops.view3d.move('INVOKE_DEFAULT')
        return {'FINISHED'}


class BBST_OT_rebuild_shell(bpy.types.Operator):
    """Put the studio floor and the default walls back (replaces any moved wall flats)"""
    bl_idname = "bbst.rebuild_shell"
    bl_label = "Rebuild Floor & Walls"
    bl_options = {'REGISTER', 'UNDO'}

    def execute(self, context):
        if not is_staging(context.scene):
            return {'CANCELLED'}
        build_studio_shell(context.scene)
        request_sync(0.0)
        return {'FINISHED'}


class BBST_OT_block_easy(bpy.types.Operator):
    """Not available in Easy Mode"""
    bl_idname = "bbst.block_easy"
    bl_label = "Not available in Easy Mode"
    bl_options = {'INTERNAL'}

    @classmethod
    def poll(cls, context):
        return _in_stage(context) and _mode() == 'EASY'

    def invoke(self, context, event):
        return {'FINISHED'}


# Easy Mode also keeps Edit Mode shut; Artist Mode allows Tab to edit the studio space's points
BLOCKED_KEYS_EASY = [
    ("3D View", 'VIEW_3D', [('TAB', {})]),
    ("Object Mode", 'EMPTY', [('TAB', {})]),
]


class BBST_OT_block(bpy.types.Operator):
    """Not available in Stage Mode"""
    bl_idname = "bbst.block"
    bl_label = "Not available in Stage Mode"
    bl_options = {'INTERNAL'}

    @classmethod
    def poll(cls, context):
        return _in_stage(context)

    def invoke(self, context, event):
        return {'FINISHED'}


# keys that change Blender state in ways Stage Mode cannot follow (hide, edit mode, add
# menu, layout changes, delete). Everything else reaches Blender as normal.
BLOCKED_KEYS = [
    ("3D View", 'VIEW_3D', [('H', {}), ('H', {"shift": True}), ('H', {"alt": True}), ('H', {"ctrl": True}),
                            ('M', {}), ('M', {"shift": True}), ('TAB', {"ctrl": True}),
                            ('A', {"shift": True}), ('A', {"ctrl": True}), ('X', {}), ('DEL', {}),
                            ('I', {}), ('Q', {"ctrl": True, "alt": True}), ('ACCENT_GRAVE', {}),
                            ('Z', {}), ('Z', {"alt": True}), ('Z', {"shift": True}), ('T', {}),
                            ('NUMPAD_0', {}), ('NUMPAD_1', {}), ('NUMPAD_3', {}), ('NUMPAD_7', {}),
                            ('NUMPAD_5', {}), ('NUMPAD_PERIOD', {}), ('HOME', {}), ('J', {"ctrl": True}),
                            ('P', {"ctrl": True}), ('P', {"alt": True}), ('L', {"ctrl": True}),
                            ('B', {"alt": True}), ('W', {}), ('V', {"ctrl": True}),
                            ('NUMPAD_0', {"ctrl": True}), ('NUMPAD_0', {"ctrl": True, "alt": True})]),
    ("Object Mode", 'EMPTY', [('H', {}), ('H', {"shift": True}), ('H', {"alt": True}), ('M', {}),
                              ('X', {}), ('DEL', {}), ('A', {"ctrl": True}),
                              ('J', {"ctrl": True}), ('P', {"ctrl": True}), ('I', {}),
                              ('A', {"shift": True}), ('RIGHTMOUSE', {}),
                              ('G', {"alt": True}), ('R', {"alt": True}), ('D', {"alt": True})]),
    ("3D View Generic", 'VIEW_3D', [('N', {})]),
    ("Region Context Menu", 'EMPTY', [('RIGHTMOUSE', {})]),
    ("Screen Editing", 'EMPTY', [('RIGHTMOUSE', {})]),
    ("Screen", 'EMPTY', [('SPACE', {"ctrl": True}), ('SPACE', {"ctrl": True, "alt": True}),
                         ('PAGE_UP', {"ctrl": True}), ('PAGE_DOWN', {"ctrl": True}),
                         ('F3', {}), ('F4', {}), ('F11', {})]),
    ("Window", 'EMPTY', [('F3', {}), ('N', {"ctrl": True}), ('O', {"ctrl": True})]),
]


# ------------------------------------------------------------------ levels: section cut
#
# A level is a height, not a collection: the working pane cuts the set horizontally at the
# level's cut height (an architectural plan), so even merged meshes that span floors are
# handled, and the set's own collections are never touched. Heights are per set file.

_UPPER_NAME = re.compile(r"\b(loft|mezzanine|mezz|upper|first floor|level ?1)\b", re.I)


def _named_upper_floor(ground):
    """A loft is too small for the area vote (Jai's: 8.6 m2): trust the set's own collection
    names (Loft, Mezzanine, Upper floor...) and take the height of their biggest flat top face."""
    import numpy as np
    m = master_scene()
    if m is None:
        return None
    best = None
    for c in m.collection.children_recursive:
        if c.get(LAYER_KEY) or not _UPPER_NAME.search(c.name):
            continue
        for ob in c.objects:
            if ob.type != 'MESH' or ob.data is None or not len(ob.data.polygons):
                continue
            me = ob.data
            n = len(me.polygons)
            nor = np.empty(n * 3, dtype=np.float32)
            cen = np.empty(n * 3, dtype=np.float32)
            ar = np.empty(n, dtype=np.float32)
            me.polygons.foreach_get("normal", nor)
            me.polygons.foreach_get("center", cen)
            me.polygons.foreach_get("area", ar)
            mw = np.array(ob.matrix_world, dtype=np.float64)
            r3 = mw[:3, :3]
            nw = nor.reshape(-1, 3) @ r3.T
            ln = np.linalg.norm(nw, axis=1)
            ln[ln == 0] = 1
            cz = (cen.reshape(-1, 3) @ r3.T + mw[:3, 3])[:, 2]
            ok = (nw[:, 2] / ln > 0.9) & (cz >= ground + 1.8)
            if not np.any(ok):
                continue
            i = int(np.argmax(np.where(ok, ar, -1.0)))
            a = float(ar[i]) * abs(np.linalg.det(r3)) ** (2 / 3)
            if best is None or a > best[1]:
                best = (float(cz[i]), a, ob, i)
    return (round(best[0], 2), best[2], best[3]) if (best is not None and best[1] >= 1.0) else None


def _lowest_above(scene, ob, pi, z0):
    """Lowest set surface more than 1 m above a loft face (rays up from its centre and towards
    its corners): a loft sits right under its roof, too close for the ceiling vote."""
    poly = ob.data.polygons[pi]
    mw = ob.matrix_world
    cen = mw @ poly.center
    samples = [cen] + [cen.lerp(mw @ ob.data.vertices[v].co, 0.8) for v in list(poly.vertices)[:8]]
    low = None
    with set_only(scene) as dg:
        for p in samples:
            o = Vector((p.x, p.y, z0 + 0.05))
            for _ in range(24):
                hit, loc, _n, _i, _ob, _m = scene.ray_cast(dg, o, Vector((0.0, 0.0, 1.0)))
                if not hit:
                    break
                if loc.z > z0 + 1.0:
                    low = loc.z if low is None else min(low, loc.z)
                    break
                o = loc + Vector((0.0, 0.0, 0.002))
    return low


def detect_floors(scene):
    """Floor surfaces from the set's big upward-facing faces → suggested cut heights.
    Returns (ground_floor_z, upper_floor_z or None, ground_cut, upper_cut)."""
    import numpy as np
    seen, zs, areas = set(), [], []
    down_z, down_a = [], []
    vl = scene.view_layers[0]      # this scene's own view layer, whatever the context is
    for c in layer_colls(scene, "SET") or [master_scene().collection]:
        for ob in coll_objects(c):
            if ob.type != 'MESH' or ob.data is None or not ob.visible_get(view_layer=vl):
                continue
            key = (ob.data.name, tuple(round(v, 3) for row in ob.matrix_world for v in row))
            if key in seen:
                continue
            seen.add(key)
            me = ob.data
            n = len(me.polygons)
            if n == 0:
                continue
            nor = np.empty(n * 3, dtype=np.float32)
            cen = np.empty(n * 3, dtype=np.float32)
            area = np.empty(n, dtype=np.float32)
            me.polygons.foreach_get("normal", nor)
            me.polygons.foreach_get("center", cen)
            me.polygons.foreach_get("area", area)
            m = np.array(ob.matrix_world, dtype=np.float64)
            r3 = m[:3, :3]
            nw = (nor.reshape(-1, 3) @ r3.T)
            ln = np.linalg.norm(nw, axis=1)
            ln[ln == 0] = 1
            nz = nw[:, 2] / ln
            cw = cen.reshape(-1, 3) @ r3.T + m[:3, 3]
            scale = abs(np.linalg.det(r3)) ** (2 / 3)
            up = nz > 0.9
            dn = nz < -0.9
            zs.append(cw[up, 2])
            areas.append(area[up] * scale)
            down_z.append(cw[dn, 2])
            down_a.append(area[dn] * scale)
    if not zs:
        return 0.0, None, 5.5, 9.5
    z = np.concatenate(zs)
    a = np.concatenate(areas)
    if z.size == 0:
        return 0.0, None, 5.5, 9.5
    bins = np.round(z / 0.1).astype(np.int64)
    acc = {}
    for b, w in zip(bins.tolist(), a.tolist()):
        acc[b] = acc.get(b, 0.0) + w
    big = sorted((b * 0.1, w) for b, w in acc.items() if w >= 12.0)
    if not big:
        return 0.0, None, 5.5, 9.5
    # ground = the biggest surface in the lowest 2.5 m of floor-like area
    lowest = big[0][0]
    ground = max((p for p in big if p[0] <= lowest + 2.5), key=lambda p: p[1])[0]
    upper = next((p[0] for p in big if p[0] >= ground + 2.0 and p[1] >= 25.0), None)
    named = None
    if upper is None:
        named = _named_upper_floor(ground)    # a loft is too small for the area vote
        if named is not None:
            upper = named[0]
    dz = np.concatenate(down_z) if down_z else np.array([])
    da = np.concatenate(down_a) if down_a else np.array([])

    def ceiling_above(level_z):
        sel = (dz > level_z + 1.8) & (da > 0.5)
        if not np.any(sel):
            return None
        heights = np.round(dz[sel] / 0.1) * 0.1
        tot = {}
        for h, w in zip(heights.tolist(), da[sel].tolist()):
            tot[h] = tot.get(h, 0.0) + w
        for h in sorted(tot):
            if tot[h] >= 8.0:
                return h
        return None

    # a plan is cut a little above head height (pegs stay whole), and always under the
    # next floor or roof, so nothing above can cover the plan
    if upper is not None:
        ground_cut = min(ground + 2.2, upper - 0.25)
        ceil = ceiling_above(upper)
        upper_cut = min(upper + 2.2, ceil - 0.05) if ceil is not None else upper + 2.2
        if named is not None:            # a loft: cut under the roof right above it
            roof = _lowest_above(scene, named[1], named[2], upper)
            if roof is not None:
                upper_cut = min(upper_cut, roof - 0.05)
        upper_cut = max(upper_cut, upper + 0.25)
    else:
        ceil = ceiling_above(ground)
        ground_cut = min(ground + 2.2, ceil - 0.05) if ceil is not None else ground + 2.2
        upper_cut = ground_cut
    ground_cut = max(ground_cut, ground + 0.25)
    return round(ground, 2), (round(upper, 2) if upper is not None else None), round(ground_cut, 2), round(upper_cut, 2)


class BBST_OT_detect_floors(bpy.types.Operator):
    """Find this set's floors and suggest where to cut the plan for each level"""
    bl_idname = "bbst.detect_floors"
    bl_label = "Detect Floors"

    def execute(self, context):
        fs = fstate()
        scene = context.scene if is_staging(context.scene) else master_scene()
        g, u, gc, uc = store_floors(fs, scene)
        for s in stagings():
            refresh_floor(s)
        request_sync(0.0)
        msg = f"Ground floor at {g:.2f} m" + (f", upper floor at {u:.2f} m" if u is not None else ", single level")
        self.report({'INFO'}, msg + f" · plan cuts {gc:.2f} / {uc:.2f} m")
        return {'FINISHED'}


class BBST_OT_mark_ceilings(bpy.types.Operator):
    """Kept for older files: levels are now a section cut, so this only re-detects floors"""
    bl_idname = "bbst.mark_ceilings"
    bl_label = "Detect Floors"

    def execute(self, context):
        return bpy.ops.bbst.detect_floors()


class BBST_OT_place_space(bpy.types.Operator):
    """Drag the studio space over the set where this scene plays; click to drop, Esc to cancel"""
    bl_idname = "bbst.place_space"
    bl_label = "Place Studio Space"
    bl_options = {'REGISTER', 'UNDO'}

    def invoke(self, context, event):
        scene = context.scene
        self.bound = boundary_of(scene) if is_staging(scene) else None
        if self.bound is None:
            self.report({'ERROR'}, "This staging has no studio space")
            return {'CANCELLED'}
        roles = stage_panes(context.window)
        self.area = roles.get("WORK") or view3d_area(context)
        if self.area is None:
            return {'CANCELLED'}
        self.region = next(r for r in self.area.regions if r.type == 'WINDOW')
        self.start = self.bound.location.copy()
        context.window.cursor_modal_set('SCROLL_XY')
        context.workspace.status_text_set("Move the mouse over the plan · click to drop the studio space · Esc cancels")
        context.window_manager.modal_handler_add(self)
        return {'RUNNING_MODAL'}

    def _finish(self, context, ok):
        context.window.cursor_modal_restore()
        context.workspace.status_text_set(None)
        scene = context.scene
        if ok and is_staging(scene):
            scene.bb_st.needs_place = False
            d = self.bound.location - self.start      # what stands on the studio floor moves with it,
            carry_with_studio(scene, Vector((d.x, d.y, 0.0)))     # on every placement (z already did)
            refresh_floor(scene)
            cursor_to_studio(scene)
        else:
            try:
                self.bound.location = self.start
            except ReferenceError:
                pass
        request_sync(0.0)
        return {'FINISHED'} if ok else {'CANCELLED'}

    def modal(self, context, event):
        from bpy_extras import view3d_utils
        try:
            self.bound.name
        except ReferenceError:
            context.window.cursor_modal_restore()
            context.workspace.status_text_set(None)
            return {'CANCELLED'}
        if event.type == 'MOUSEMOVE':
            r = self.region
            co = (event.mouse_x - r.x, event.mouse_y - r.y)
            if 0 <= co[0] <= r.width and 0 <= co[1] <= r.height:
                rv3d = self.area.spaces.active.region_3d
                loc = view3d_utils.region_2d_to_location_3d(r, rv3d, co, self.bound.location)
                self.bound.location.x, self.bound.location.y = loc.x, loc.y
        elif event.type == 'LEFTMOUSE' and event.value == 'RELEASE':
            return self._finish(context, True)
        elif event.type in ('RIGHTMOUSE', 'ESC'):
            return self._finish(context, False)
        return {'RUNNING_MODAL'}


def chars_outside_studio(scene):
    """Characters (and stage cameras) outside the studio working space, at the current frame."""
    st = scene.bb_st
    bound = None
    for c in layer_colls(scene, "STUDIO"):
        for ob in c.objects:
            if ob.get(ROLE_KEY) == "boundary":
                bound = ob
                break
    if bound is None:
        return []
    cx, cy = bound.location.x, bound.location.y
    hw, hd = st.studio_w / 2, st.studio_d / 2
    out = []
    for ob in stage_objects(scene, roles=("char", "cam")):
        p = ob.matrix_world.translation
        if abs(p.x - cx) > hw or abs(p.y - cy) > hd or (ob.get(ROLE_KEY) == "cam" and p.z - st.floor_z > st.studio_h):
            out.append(ob.name)
    cams = sub_coll(scene, "STAGE", "Cameras")
    for ob in (cams.objects if cams else []):
        if ob.type == 'CAMERA' and ob.name not in out:
            p = ob.matrix_world.translation
            if abs(p.x - cx) > hw or abs(p.y - cy) > hd or p.z - st.floor_z > st.studio_h:
                out.append(ob.name)
    return out


class BBST_OT_playblast(bpy.types.Operator):
    """Viewport-render the beats range through a camera to an MP4 in the Stage folder"""
    bl_idname = "bbst.playblast"
    bl_label = "Playblast"
    cam_name: bpy.props.StringProperty()
    use_cuts: bpy.props.BoolProperty(name="Follow beat camera cuts", default=False)

    def execute(self, context):
        scene = context.scene
        cam = bpy.data.objects.get(self.cam_name) or scene.camera
        if cam is None:
            self.report({'ERROR'}, "No camera")
            return {'CANCELLED'}
        # a camera pane, never the plan: the plan pane carries the ghost world, the cut and labels
        roles = stage_panes(context.window)
        cam_panes = [roles[k] for k in ("CAM0", "CAM1") if k in roles]
        area = (next((a for a in cam_panes if a.spaces.active.use_local_camera
                      and a.spaces.active.camera == cam), None)
                or (cam_panes[0] if cam_panes else None) or view3d_area(context))
        if area is None:
            self.report({'ERROR'}, "No 3D view to render from")
            return {'CANCELLED'}
        st = scene.bb_st if is_staging(scene) else None
        if st is not None:
            i = beat_at_frame(scene)
            if i is not None and st.beats[i].dirty:
                save_beat(scene, i)      # playback re-reads the keys and would wipe unsaved moves
        space = area.spaces.active
        rv3d = space.region_3d
        r = scene.render
        im = r.image_settings
        saved = (r.filepath, im.media_type, im.file_format, scene.camera, space.camera, space.use_local_camera)
        saved_view = (rv3d.view_perspective, rv3d.view_rotation.copy(), rv3d.view_location.copy(), rv3d.view_distance)
        saved_im = {k: getattr(im, k) for k in ("color_mode", "color_depth", "quality", "compression")}
        saved_ff = {k: getattr(r.ffmpeg, k) for k in ("format", "codec", "constant_rate_factor", "ffmpeg_preset", "gopsize")}
        saved_frames = (scene.frame_start, scene.frame_end, scene.frame_current)
        label = "Edit" if self.use_cuts else cam.name
        out = os.path.join(stage_dir(scene), f"Playblast {label}.mp4")
        saved_binds = [(mk, mk.camera) for mk in scene.timeline_markers if mk.camera]
        try:
            if not self.use_cuts:
                for mk, _c in saved_binds:
                    mk.camera = None   # a bound beat camera would hijack a per-camera playblast
            scene.camera = cam
            if self.use_cuts or space.camera != cam:
                space.use_local_camera = False   # follow scene.camera (for the Edit: the beat cuts)
            rv3d.view_perspective = 'CAMERA'
            if st is not None and st.beats:      # the beats, not the whole scene range
                scene.frame_start = st.beats[0].frame
                scene.frame_end = max(beat_out(st.beats[-1]), st.beats[0].frame + 1)
            r.filepath = out
            im.media_type = 'VIDEO'   # Blender 5.x: video formats live behind media_type
            im.file_format = 'FFMPEG'
            r.ffmpeg.format = 'MPEG4'
            r.ffmpeg.codec = 'H264'
            with context.temp_override(window=context.window, area=area, region=next(rg for rg in area.regions if rg.type == 'WINDOW')):
                bpy.ops.render.opengl(animation=True, view_context=True)
        finally:
            for mk, c in saved_binds:
                mk.camera = c
            r.filepath, mt, fmt, scene.camera, space.camera, space.use_local_camera = saved
            im.media_type = mt
            im.file_format = fmt
            for k, v in saved_im.items():
                try:
                    setattr(im, k, v)
                except Exception:
                    pass
            for k, v in saved_ff.items():
                try:
                    setattr(r.ffmpeg, k, v)
                except Exception:
                    pass
            rv3d.view_perspective, rv3d.view_rotation, rv3d.view_location, rv3d.view_distance = saved_view
            scene.frame_start, scene.frame_end = saved_frames[0], saved_frames[1]
            scene.frame_set(saved_frames[2])
        self.report({'INFO'}, f"Playblast saved: {out}")
        return {'FINISHED'}


class BBST_OT_export_pack(bpy.types.Operator):
    """Write the staging pack: beat sheet, build inventory, floor tape map data, ban list, camera JSON"""
    bl_idname = "bbst.export_pack"
    bl_label = "Export Staging Pack"

    def execute(self, context):
        scene = context.scene
        st = scene.bb_st
        d = stage_dir(scene)
        label = staging_label(scene)
        f_rate = fps(scene)

        # beat sheet
        lines = [f"# Beat sheet — {label}", ""]
        total = (beat_out(st.beats[-1]) - st.beats[0].frame) / f_rate if len(st.beats) > 1 else 0
        lines.append(f"Beats: {len(st.beats)} · total {total:.1f} s (Seedance window 4–30 s)")
        lines.append("")
        chars = stage_objects(scene, roles=("char",))
        bound = boundary_of(scene)
        ox, oy = (bound.location.x, bound.location.y) if bound is not None else (0.0, 0.0)
        lines.append("Positions in metres from the studio-space centre (X right, Y up on the plan).")
        lines.append("")
        for i, b in enumerate(st.beats):
            t = (b.frame - st.beats[0].frame) / f_rate
            cam = next((m.camera.name for m in scene.timeline_markers if m.frame == b.frame and m.camera), "—")
            lines.append(f"## B{i + 1} {b.label}  (t={t:.1f}s, frame {b.frame}, cam {cam}, move {b.move_s:.1f}s, hold {b.hold_s:.1f}s)")
            if b.note:
                lines.append(b.note)
            for c in chars:     # read the keys: a frame jump would wipe unsaved blocking
                xy = [c.location.x, c.location.y]
                ad = c.animation_data
                for fc in (channelbag_fcurves(ad.action) if ad and ad.action else []):
                    if fc.data_path == "location" and fc.array_index in (0, 1):
                        xy[fc.array_index] = fc.evaluate(b.frame)
                lines.append(f"- {c.name}: ({xy[0] - ox:+.2f}, {xy[1] - oy:+.2f})")
            lines.append("")
        open(os.path.join(d, "Beat Sheet.md"), "w", encoding="utf-8").write("\n".join(lines))

        # build inventory + floor tape
        inv, tape = {}, [f"# Floor tape map — {label}", "", "Distances in metres from the studio-space centre (X right, Y up on the plan).", ""]
        for c in layer_colls(scene, "STUDIO"):
            for ob in c.objects:
                if ob.get(ROLE_KEY) == "boundary":
                    continue
                kind = ob.get("bb_st_kind", "Piece")
                dims = ob.dimensions
                key = f"{kind} {dims.x:.2f}×{dims.y:.2f}×{dims.z:.2f} m"
                inv[key] = inv.get(key, 0) + 1
                loc = ob.location
                rot = math.degrees(ob.rotation_euler.z)
                tape.append(f"- {ob.name}: centre ({loc.x - ox:+.2f}, {loc.y - oy:+.2f}), rotation {rot:.0f}°, footprint {dims.x:.2f}×{dims.y:.2f} m")
        inv_lines = [f"# Build inventory — {label}", ""] + [f"- {k} × {v}" for k, v in sorted(inv.items())]
        open(os.path.join(d, "Build Inventory.md"), "w", encoding="utf-8").write("\n".join(inv_lines))
        open(os.path.join(d, "Floor Tape Map.md"), "w", encoding="utf-8").write("\n".join(tape))

        # ban list
        bans = [ob.name for ob in stage_objects(scene, roles=("prop",)) if ob.get(STANDIN_KEY)]
        open(os.path.join(d, "Stand-in Ban List.md"), "w", encoding="utf-8").write(
            "# Placeholder stand-ins — ban by name in every prompt\n\n" + "\n".join(f"- {b}" for b in bans) + "\n")

        # camera JSON
        cams_c = sub_coll(scene, "STAGE", "Cameras")
        cj = []
        for ob in (cams_c.objects if cams_c else []):
            if ob.type != 'CAMERA':
                continue
            cj.append({"name": ob.name, "lens": ob.data.lens,
                       "location": list(ob.matrix_world.translation),
                       "rotation_euler": list(ob.rotation_euler),
                       "sensor_width": ob.data.sensor_width})
        open(os.path.join(d, "Cameras.json"), "w", encoding="utf-8").write(json.dumps(cj, indent=1))

        self.report({'INFO'}, f"Staging pack written to {d}")
        return {'FINISHED'}


def build_beat_trails(scene):
    """Temporary trail curves + beat dots per character, from the beat keys. Returns the objects."""
    st = scene.bb_st
    stage = layer_colls(scene, "STAGE")
    made = []
    if not (st.beats and stage):
        return made
    frames = [b.frame for b in st.beats]
    for ob in stage_objects(scene, roles=("char",)):
        ad = ob.animation_data
        if not (ad and ad.action):
            continue
        xy = {f: [ob.location.x, ob.location.y] for f in frames}
        for fc in channelbag_fcurves(ad.action):
            if fc.data_path == "location" and fc.array_index in (0, 1):
                for f in frames:
                    xy[f][fc.array_index] = fc.evaluate(f)
        pts = [Vector((xy[f][0], xy[f][1], st.floor_z + 0.05)) for f in frames]
        cu = bpy.data.curves.new(f"TRAIL {ob.name}", 'CURVE')
        cu.dimensions = '3D'
        cu.bevel_depth = 0.035
        sp = cu.splines.new('POLY')
        sp.points.add(len(pts) - 1)
        for p, v in zip(sp.points, pts):
            p.co = (v.x, v.y, v.z, 1)
        tr = bpy.data.objects.new(f"TRAIL {ob.name}", cu)
        tr.color = ob.color
        stage[0].objects.link(tr)
        made.append(tr)
        for k, v in enumerate(pts):   # a flat dot on every beat
            bm = bmesh.new()
            bmesh.ops.create_cone(bm, cap_ends=True, segments=12, radius1=1, radius2=1, depth=1,
                                  matrix=Matrix.Translation(v) @ Matrix.Diagonal((0.11, 0.11, 0.008)).to_4x4())
            me = bpy.data.meshes.new(f"DOT {ob.name} B{k+1}")
            bm.to_mesh(me)
            bm.free()
            dot = bpy.data.objects.new(me.name, me)
            dot.color = ob.color
            stage[0].objects.link(dot)
            made.append(dot)
    return made


class BBST_OT_top_map(bpy.types.Operator):
    """Save a top-view blocking map PNG with character trails"""
    bl_idname = "bbst.top_map"
    bl_label = "Top Map"

    def execute(self, context):
        scene = context.scene
        area = stage_panes(context.window).get("WORK") or view3d_area(context)
        if area is None or not is_staging(scene):
            self.report({'ERROR'}, "Open a staging in Stage Mode first")
            return {'CANCELLED'}
        trails = build_beat_trails(scene)
        space = area.spaces.active
        r3d = space.region_3d
        if space.local_view is not None:
            for ob in trails:
                try:
                    ob.local_view_set(space, True)
                except RuntimeError:
                    pass
        saved_view = (r3d.view_perspective, r3d.view_rotation.copy(), r3d.view_location.copy(), r3d.view_distance)
        saved_lock = r3d.lock_rotation
        _set_top_view(space)
        st = scene.bb_st
        r3d.view_location = studio_center(scene)          # frame the studio, not the whole site
        r3d.view_distance = max(st.studio_w, st.studio_d) * 1.3
        r = scene.render
        saved = (r.filepath, r.image_settings.media_type, r.image_settings.file_format)
        out = os.path.join(stage_dir(scene), "Top Map.png")
        try:
            r.filepath = out
            r.image_settings.media_type = 'IMAGE'
            r.image_settings.file_format = 'PNG'
            with context.temp_override(window=context.window, area=area, region=next(rg for rg in area.regions if rg.type == 'WINDOW')):
                bpy.ops.render.opengl(animation=False, view_context=True, write_still=True)
        finally:
            r.filepath, mt, fmt = saved
            r.image_settings.media_type = mt
            r.image_settings.file_format = fmt
            r3d.view_perspective, r3d.view_rotation, r3d.view_location, r3d.view_distance = saved_view
            r3d.lock_rotation = saved_lock
            for ob in trails:
                data = ob.data
                bpy.data.objects.remove(ob)
                if isinstance(data, bpy.types.Curve):
                    bpy.data.curves.remove(data)
                else:
                    bpy.data.meshes.remove(data)
        self.report({'INFO'}, f"Top map saved: {out}")
        return {'FINISHED'}


# ------------------------------------------------------------------ panels

# Everything lives in ONE panel with icon tabs (like the Properties editor's tab rail),
# so only one section is in view at a time (Aman, 4 Oct 2026).

def _mode():
    fs = fstate()
    return fs.mode if fs is not None else 'ARTIST'


def draw_scenes(lay, context):
    scene = context.scene
    artist = _mode() == 'ARTIST'
    for s in stagings():
        r = lay.row(align=True)
        r.operator("bbst.goto_scene", text=staging_label(s), icon='VIEW_CAMERA',
                   depress=(s == scene)).scene_name = s.name
        if artist:
            r.operator("bbst.delete_staging", text="", icon='X').scene_name = s.name
    if artist:
        lay.operator("bbst.new_staging", icon='ADD')


def draw_studio(lay, context):
    st = context.scene.bb_st
    r = lay.row()
    r.scale_y = 1.4
    r.alert = st.needs_place
    r.operator("bbst.place_space", icon='OBJECT_ORIGIN')
    if st.needs_place:
        lay.label(text="Drag the studio space to where this scene plays", icon='INFO')
    col = lay.column(align=True)
    col.label(text="Add to the studio:")
    grid = col.grid_flow(columns=3, align=True)
    for key, (label, *_rest) in KIT_PIECES.items():
        grid.operator("bbst.add_kit", text=label).piece = key
    col = lay.column(align=True)
    col.scale_y = 1.2
    col.operator("bbst.pick_standin", text="Grey Box from Set Object", icon='EYEDROPPER')
    col.operator("bbst.pick_match", text="Match Piece to Set Object", icon='SNAP_FACE')
    outside = chars_outside_studio(context.scene)
    if outside:
        lay.label(text="Outside the studio: " + ", ".join(outside[:4]), icon='ERROR')


def draw_cast(lay, context):
    scene = context.scene
    st = scene.bb_st
    chars = sub_coll(scene, "STAGE", "Characters")
    props_c = sub_coll(scene, "STAGE", "Props")
    if chars is not None:
        row = lay.row(align=True)
        row.prop(st, "new_char_name", text="", placeholder="Character name")
        row.operator("bbst.add_char", text="", icon='ADD')
        lay.template_list("BBST_UL_objects", "chars", chars, "objects", st, "char_index", rows=3)
        if not len(chars.objects):
            lay.label(text="Type a name and press + to add a character", icon='INFO')
        row = lay.row(align=True)
        row.operator("bbst.turn", text="Turn Left", icon='LOOP_BACK').deg = 45
        row.operator("bbst.turn", text="Turn Right", icon='LOOP_FORWARDS').deg = -45
    if props_c is not None:
        lay.operator("bbst.add_prop", icon='MESH_CUBE')
        if len(props_c.objects):
            lay.template_list("BBST_UL_objects", "props", props_c, "objects", st, "prop_index", rows=2)


def draw_beats(lay, context):
    scene = context.scene
    st = scene.bb_st
    n = len(st.beats)
    idx = min(max(st.beat_index, 0), n - 1) if n else 0
    row = lay.row(align=True)
    row.scale_y = 1.3
    row.operator("bbst.beat_add", icon='ADD')
    sub = row.row(align=True)
    sub.enabled = n > 0
    sub.operator("bbst.beat_save", icon='STRIP_COLOR_02' if (n > 0 and st.beats[idx].dirty) else 'KEYINGSET')
    grid = lay.grid_flow(row_major=True, columns=5, even_columns=True, align=True)
    grid.scale_y = 1.3
    grid.operator("bbst.beat_goto", text="", icon='REW').index = 0
    grid.operator("bbst.step_beat", text="", icon='PREV_KEYFRAME').forward = False
    playing = context.screen.is_animation_playing if context.screen else False
    grid.operator("bbst.play", text="", icon='PAUSE' if playing else 'PLAY')
    grid.operator("bbst.step_beat", text="", icon='NEXT_KEYFRAME').forward = True
    grid.operator("bbst.beat_goto", text="", icon='FF').index = max(0, n - 1)
    if n:
        hdr = lay.row(align=True)
        hdr.label(text="      Beat")
        cols = hdr.row(align=True)
        cols.ui_units_x = 7.2
        cols.alignment = 'RIGHT'
        cols.label(text="Move s")
        cols.label(text="Hold s")
    lay.template_list("BBST_UL_beats", "", st, "beats", st, "beat_index", rows=4)
    if n:
        b = st.beats[idx]
        lay.prop(b, "note", text="", placeholder="What happens on this beat")
        row = lay.row(align=True)
        row.operator("bbst.beat_delete", icon='X')
        row.operator("bbst.fit_range", icon='PREVIEW_RANGE')
        if n > 1:
            total = (beat_out(st.beats[-1]) - st.beats[0].frame) / fps(scene)
            warn = "" if 4 <= total <= 30 else "  (outside Seedance 4–30 s)"
            lay.label(text=f"Total: {total:.1f} s{warn}", icon='TIME')
            top = beat_top_speed(scene, idx)
            if top and top[1] > 0.05:
                lay.label(text=f"Fastest to next beat: {top[0]} {top[1]:.1f} m/s",
                          icon='ERROR' if top[1] > 1.6 else 'CHECKMARK')
    else:
        lay.label(text="Place everyone, then Add Beat", icon='INFO')


def draw_cams(lay, context):
    scene = context.scene
    artist = _mode() == 'ARTIST'
    lay.operator("bbst.cam_add", icon='OUTLINER_OB_CAMERA')
    for ob in stage_cams(scene):
        row = lay.row(align=True)
        row.prop(ob, "name", text="", emboss=True)
        sub = row.row(align=True)
        sub.ui_units_x = 3
        sub.prop(ob.data, "bbst_lens_mm", text="")     # whole millimetres, like the pane header
        row.operator("bbst.cam_bind", text="", icon='MARKER_HLT').cam_name = ob.name
        if artist:
            row.operator("bbst.playblast", text="", icon='RENDER_ANIMATION').cam_name = ob.name
        op = row.operator("bbst.obj_action", text="", icon='X')
        op.obj_name = ob.name
        op.action = 'DELETE'
    if artist:
        lay.prop(scene.bb_st, "key_cameras")


def draw_outputs(lay, context):
    lay.operator("bbst.export_pack", icon='EXPORT')
    lay.operator("bbst.top_map", icon='AXIS_TOP')
    if any(mk.camera for mk in context.scene.timeline_markers):
        op = lay.operator("bbst.playblast", text="Playblast Edit (beat cuts)", icon='SEQUENCE')
        op.cam_name = ""
        op.use_cuts = True


def draw_settings(lay, context):
    st = context.scene.bb_st
    fs = fstate()
    col = lay.column(align=True)
    col.label(text="Studio working space:")
    col.prop(st, "studio_w")
    col.prop(st, "studio_d")
    col.prop(st, "studio_h")
    col = lay.column(align=True)
    col.label(text="Studio floor & walls:")
    col.prop(st, "wall_count")
    col.prop(st, "wall_width")
    col.prop(st, "wall_height")
    col.operator("bbst.rebuild_shell", icon='FILE_REFRESH')
    col = lay.column(align=True)
    col.label(text="Floors of this set:")
    if fs is not None:
        col.prop(fs, "level1_cut", text="Ground floor plan cut (m)")
        col.prop(fs, "ceiling_cut", text="Upper floor plan cut (m)")
    if fs is not None:
        col.prop(fs, "has_upper")
    col.operator("bbst.detect_floors", icon='VIEWZOOM')
    col = lay.column(align=True)
    col.prop(st, "play_level")
    col.prop(st, "floor_z")
    lay.prop(st, "beat_spacing")
    lay.prop(st, "black_outside")
    if fs is not None:
        lay.prop(fs, "mode")
    lay.operator("bbst.fix_screen", icon='FILE_REFRESH')


class BBST_OT_turn(bpy.types.Operator):
    """Turn the selected characters"""
    bl_idname = "bbst.turn"
    bl_label = "Turn"
    bl_options = {'REGISTER', 'UNDO'}
    deg: bpy.props.FloatProperty(default=45)

    def execute(self, context):
        done = 0
        for ob in context.selected_objects:
            if ob.get(ROLE_KEY) in ("char", "prop"):
                ob.rotation_euler.z += math.radians(self.deg)
                done += 1
        if not done:
            self.report({'INFO'}, "Click a character first")
        return {'FINISHED'}


class _NPanel:
    bl_space_type = 'VIEW_3D'
    bl_region_type = 'UI'
    bl_category = "BB Stage"


class BBST_PT_entry(_NPanel, bpy.types.Panel):
    """Outside Stage Mode the sidebar shows only the way in, like BB Set Viewer."""
    bl_label = "BB Stage"
    bl_order = 0

    def draw(self, context):
        col = self.layout.column(align=True)
        col.scale_y = 1.5
        if fstate() is None:
            return
        if not _in_stage(context):
            if stagings():
                col.operator("bbst.enter_stage", text="Enter Artist Mode", icon='FULLSCREEN_ENTER').easy = False
                col.operator("bbst.enter_stage", text="Enter Easy Mode", icon='VIEW_CAMERA').easy = True
            else:
                col.operator("bbst.new_staging", text="New Staging…", icon='ADD')
        else:
            if _mode() == 'ARTIST':
                col.operator("bbst.enter_stage", text="Switch to Easy Mode", icon='VIEW_CAMERA').easy = True
            else:
                col.operator("bbst.enter_stage", text="Switch to Artist Mode", icon='FULLSCREEN_ENTER').easy = False
            col.operator("bbst.exit_stage", text="Exit to Blender", icon='LOOP_BACK')


class _StagePanel(_NPanel):
    artist_only = False

    @classmethod
    def poll(cls, context):
        if not _in_stage(context):
            return False
        return _mode() == 'ARTIST' or not cls.artist_only


class BBST_PT_scenes(_StagePanel, bpy.types.Panel):
    bl_label = "Stagings"
    bl_order = 1

    def draw(self, context):
        draw_scenes(self.layout, context)


class BBST_PT_studio(_StagePanel, bpy.types.Panel):
    bl_label = "Studio Build"
    bl_order = 2
    artist_only = True

    def draw(self, context):
        draw_studio(self.layout, context)


class BBST_PT_cast(_StagePanel, bpy.types.Panel):
    bl_label = "Characters & Props"
    bl_order = 3

    def draw(self, context):
        draw_cast(self.layout, context)


class BBST_PT_beats(_StagePanel, bpy.types.Panel):
    bl_label = "Beats"
    bl_order = 4

    def draw(self, context):
        draw_beats(self.layout, context)


class BBST_PT_cams(_StagePanel, bpy.types.Panel):
    bl_label = "Cameras"
    bl_order = 5

    def draw(self, context):
        draw_cams(self.layout, context)


class BBST_PT_outputs(_StagePanel, bpy.types.Panel):
    bl_label = "Outputs"
    bl_order = 6
    bl_options = {'DEFAULT_CLOSED'}
    artist_only = True

    def draw(self, context):
        draw_outputs(self.layout, context)


class BBST_PT_settings(_StagePanel, bpy.types.Panel):
    bl_label = "Settings"
    bl_order = 7
    bl_options = {'DEFAULT_CLOSED'}
    artist_only = True

    def draw(self, context):
        draw_settings(self.layout, context)


# ------------------------------------------------------------------ handlers

@persistent
def _bbst_on_load(*_args):
    _WATCH.clear()
    _LAST_STG.clear()
    _SYNC["pending"] = False
    _BUILD_STATE["active"] = False
    bpy.app.timers.register(_bbst_after_load, first_interval=0.3)


_REREG = {"n": 0}


def _retire_stale_copies():
    """Older BB Stage copies embedded in the .blend as auto-run text blocks re-register their own
    classes when the file opens (Blender runs them before load_post). Switch them off and say
    whether this module has to register itself again."""
    stale = False
    for t in bpy.data.texts:
        if not (t.name.startswith("bb_stage") and t.use_module):
            continue
        m = re.search(r'"version":\s*\((\d+),\s*(\d+),\s*(\d+)\)', t.as_string())
        if m and tuple(int(g) for g in m.groups()) < tuple(bl_info["version"]):
            t.use_module = False       # never runs again, and saves no longer carry it as a script
            stale = True
    live = getattr(getattr(getattr(bpy.types, "BBST_OT_enter_stage", None), "execute", None), "__code__", None)
    foreign = live is not None and live.co_filename != BBST_OT_enter_stage.execute.__code__.co_filename
    return stale or foreign


def _reclaim():
    """Register this copy again: unregister the classes another copy put under our names
    (register() alone fails on them), then ours, then register."""
    ours = {c.__name__: c for c in CLASSES}
    for base in (bpy.types.Operator, bpy.types.Panel, bpy.types.UIList, bpy.types.PropertyGroup):
        stack = list(base.__subclasses__())
        while stack:
            k = stack.pop()
            stack.extend(k.__subclasses__())
            if k.__name__ in ours and ours[k.__name__] is not k and getattr(k, "is_registered", False):
                try:
                    bpy.utils.unregister_class(k)
                except Exception:
                    pass
    # classes only an older copy has (v0.7: BBST_OT_standin, BBST_OT_match_to_set) go too
    for name in [n for n in dir(bpy.types) if n.startswith("BBST_") and n not in ours]:
        try:
            bpy.utils.unregister_class(getattr(bpy.types, name))
        except Exception:
            pass
    for cls in reversed(CLASSES):
        try:
            if getattr(cls, "is_registered", False):
                bpy.utils.unregister_class(cls)
        except Exception:
            pass
    register()


def _bbst_after_load():
    try:
        if _retire_stale_copies() and _REREG["n"] < 2:
            _REREG["n"] += 1
            print("BB Stage: an older embedded copy took over on load; registering", bl_info["version"])
            _reclaim()          # takes the classes back; register() schedules this again
            return None
        for s in stagings():
            migrate_staging(s)
            if s.bb_st.stage_mode:
                s.bb_st.stage_mode = False     # v0.7 stored Stage Mode per scene
        free_local_collection_slots()
        _cleanup_legacy_panel_hides()
        if stage_windows():
            for w in stage_windows():
                _WATCH.pop(w.as_pointer(), None)
                engage(w, w.scene)
        else:
            untint_everything()
            _restore_foreign_v3d_panels()
    except Exception as e:
        print("BB Stage after load:", e)
    return None


@persistent
def _bbst_save_pre(*_args):
    untint_everything()        # the set is saved with its own colours, never the ghost tint


@persistent
def _bbst_save_post(*_args):
    if stage_on():
        request_sync(0.05)


@persistent
def _bbst_undo(*_args):
    # no _WATCH.clear(): that made every undo rebuild the screen and reset the plan view; the
    # watchdog still notices scene/pane changes, and the sync re-applies visibility
    if stage_on():
        request_sync(0.05)
    else:
        untint_everything()     # an undo step recorded in Stage Mode brings the ghost tint back


def _cleanup_legacy_panel_hides():
    """v0.7 parked other add-ons' panels with poll=lambda: False and kept the list in memory
    only; restore any left in this session."""
    for cls in list(bpy.types.Panel.__subclasses__()):
        try:
            p = cls.__dict__.get("poll")
            f = getattr(p, "__func__", None)
            code = getattr(f, "__code__", None)
            if (code is not None and code.co_name == "<lambda>" and "bb_stage" in code.co_filename
                    and not getattr(cls, "_bbst_hidden", False)):
                reg = getattr(cls, "is_registered", False)
                if reg:
                    bpy.utils.unregister_class(cls)
                del cls.poll
                if reg:
                    bpy.utils.register_class(cls)
        except Exception:
            continue


# ------------------------------------------------------------------ register

PANEL_CLASSES = [
    BBST_PT_entry, BBST_PT_scenes, BBST_PT_studio, BBST_PT_cast,
    BBST_PT_beats, BBST_PT_cams, BBST_PT_outputs, BBST_PT_settings,
]

CLASSES = [
    BBST_Beat, BBST_Props,
    BBST_OT_new_staging, BBST_OT_goto_scene, BBST_OT_delete_staging,
    BBST_OT_add_kit,
    BBST_OT_pick_standin, BBST_OT_pick_match,
    BBST_OT_add_char, BBST_OT_add_prop, BBST_OT_obj_action, BBST_UL_objects, BBST_OT_turn,
    BBST_OT_beat_add, BBST_OT_beat_save, BBST_OT_beat_goto, BBST_OT_beat_delete,
    BBST_OT_play, BBST_OT_from_start, BBST_OT_step_beat,
    BBST_OT_fit_range, BBST_UL_beats,
    BBST_OT_cam_add, BBST_OT_cam_look, BBST_OT_cam_bind,
    BBST_OT_pane_world, BBST_OT_pane_view, BBST_OT_pane_cam, BBST_OT_pane_lens,
    BBST_OT_lens_step, BBST_OT_pane_shading, BBST_OT_pan, BBST_OT_block, BBST_OT_block_easy,
    BBST_OT_mark_ceilings, BBST_OT_detect_floors, BBST_OT_fix_screen, BBST_OT_rebuild_shell,
    BBST_OT_pane_cam_pick, BBST_OT_pane_level,
    BBST_OT_enter_stage, BBST_OT_exit_stage, BBST_OT_place_space, BBST_OT_walk,
    BBST_OT_playblast, BBST_OT_export_pack, BBST_OT_top_map,
] + PANEL_CLASSES

PROP_CLONES = []

_HANDLERS = (("load_post", "_bbst_on_load"), ("save_pre", "_bbst_save_pre"),
             ("save_post", "_bbst_save_post"), ("undo_post", "_bbst_undo"),
             ("redo_post", "_bbst_undo"), ("depsgraph_update_post", "_bbst_on_depsgraph"))
_TIMERS_KEY = "bbst_timers"


def _remove_named_handlers():
    names = {n for _l, n in _HANDLERS} | {"_on_depsgraph"}
    for lst_name, _n in _HANDLERS:
        lst = getattr(bpy.app.handlers, lst_name)
        for h in list(lst):
            if getattr(h, "__name__", "") in names:
                lst.remove(h)


def _remove_keymaps():
    kc = bpy.context.window_manager.keyconfigs.addon if bpy.context.window_manager else None
    if not kc:
        return
    for km in kc.keymaps:
        for kmi in list(km.keymap_items):
            if kmi.idname.startswith("bbst."):
                km.keymap_items.remove(kmi)


def _add_keymaps():
    kc = bpy.context.window_manager.keyconfigs.addon if bpy.context.window_manager else None
    if not kc:
        return
    km = kc.keymaps.new(name="3D View", space_type='VIEW_3D')
    km.keymap_items.new("bbst.walk", 'F', 'PRESS')
    km.keymap_items.new("bbst.pan", 'MIDDLEMOUSE', 'PRESS')
    for name, space, keys in BLOCKED_KEYS:
        km = kc.keymaps.new(name=name, space_type=space)
        for key, mods in keys:
            km.keymap_items.new("bbst.block", key, 'PRESS', **mods)
    for name, space, keys in BLOCKED_KEYS_EASY:
        km = kc.keymaps.new(name=name, space_type=space)
        for key, mods in keys:
            km.keymap_items.new("bbst.block_easy", key, 'PRESS', **mods)


def _stop_timers():
    ns = bpy.app.driver_namespace
    for f in ns.get(_TIMERS_KEY, []):
        try:
            if bpy.app.timers.is_registered(f):
                bpy.app.timers.unregister(f)
        except Exception:
            pass
    ns[_TIMERS_KEY] = []


def register():
    for cls in CLASSES:
        try:
            bpy.utils.register_class(cls)
        except ValueError:
            bpy.utils.unregister_class(getattr(bpy.types, cls.__name__))
            bpy.utils.register_class(cls)
    bpy.types.Scene.bb_st = bpy.props.PointerProperty(type=BBST_Props)
    bpy.types.Camera.bbst_lens_mm = bpy.props.IntProperty(
        name="Lens (mm)", min=8, max=300, description="Focal length in whole millimetres",
        get=lambda s: int(round(s.lens)), set=lambda s, v: setattr(s, "lens", float(min(300, max(8, v)))))
    _take_over_headers()
    _remove_named_handlers()
    for lst_name, fn_name in _HANDLERS:
        getattr(bpy.app.handlers, lst_name).append(globals()[fn_name])
    _remove_keymaps()
    _add_keymaps()
    _stop_timers()
    bpy.app.timers.register(_bbst_watchdog, first_interval=1.0, persistent=True)
    bpy.app.driver_namespace[_TIMERS_KEY] = [_bbst_watchdog]
    bpy.app.timers.register(_bbst_after_load, first_interval=0.5)


def unregister():
    _stop_timers()
    _remove_keymaps()
    _remove_named_handlers()
    _release_headers()
    _restore_foreign_v3d_panels()
    try:
        untint_everything()
    except Exception:
        pass
    for cls in reversed(CLASSES):
        try:
            bpy.utils.unregister_class(cls)
        except RuntimeError:
            pass
    if hasattr(bpy.types.Scene, "bb_st"):
        del bpy.types.Scene.bb_st
    if hasattr(bpy.types.Camera, "bbst_lens_mm"):
        del bpy.types.Camera.bbst_lens_mm


if __name__ == "__main__":
    try:
        unregister()
    except Exception:
        pass
    register()
