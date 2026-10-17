"""BB Stage — staging & blocking previz for Beta Builder sets (View3D > Sidebar > BB Stage).

Two worlds, one plan: the finished 3D set (SET) and the grey-studio blockout (STUDIO), with the
staged action (STAGE: character pegs, props, cameras, beats) on top. Each studio setup lives in its
own scene ("STG <label>") inside the set's .blend; the master set scene stays untouched.

Modes: EASY (direction team — characters, beats, cameras) / ARTIST (everything: staging builder,
studio kit, stand-ins, outputs, settings). Separate from BB Set Viewer for now (Aman, 4 Oct 2026).

0.16 (11 Oct 2026, "the blockout was feeling very mechanical"): Natural moves (everybody takes the time
their own move needs, sets off and settles apart from the others, walkers turn to where they go; one
move can be timed by hand in Beats › Timing), Life in the holds, a retime that carries every key and
marker of the staging (cuts, lens, crowd cues, hand-made keys), and per camera Handheld, Travels with
a character, and Zoom on the beats.

0.17 (12 Oct 2026, the Gossip Maze POV): a camera can sit in a character's Eyes — his gaze is posed on
the beats like any other pose — and Step off at a beat you choose, letting go over a second or so and
flying to wherever you parked it on the next beat, in one unbroken shot.

0.19 (15 Oct 2026, the beat model made robust): the orange "unsaved" badge lights for every staged object,
in every session (the handlers survive File > Open), and goes out again when a scrub or a jump drops the move;
a move made between two beats is flagged too. Save Beat writes only what you changed, into the beat under the
playhead; every control that re-reads the keys (and Ctrl+S) saves an unsaved move first. New beats hold a
second (Settings › Default hold time). A retime that shrinks a move or a hold keeps the cuts and hand-made keys
inside it and gives them back when the time comes back. Markers you make yourself are never touched.

0.19 sidebar (15 Oct 2026, "make the ui cleaner and modular"): one header with the staging dropdown, the Switchboard
(which features this staging shows), Settings (what is set once) and four mode tabs, Block · Camera · Studio · Output
(Easy Mode: Block and Camera). Each feature is a module in MODULES with its own panel; in Camera mode people and
props can't be clicked in the panes, so framing a shot never nudges them.

0.19.1 (15 Oct 2026, evening, Aman's notes on the studio): Make Studio Contact Prop turns a set chair or table (or a
staging prop) into a real prop that stands in the studio on the shoot day, listed with its size in the Studio tab and
in the staging pack; Add Wall and Add Door Flat sit at the top of the Studio tab; a new camera is Static unless its
Add Camera dialog ticks "Animated on the beats"; sitting down and getting up keep the feet on the floor.
"""

import json
import math
import os
import re
from contextlib import contextmanager

import bpy
import bmesh
from bpy.app.handlers import persistent
from mathutils import Euler, Matrix, Quaternion, Vector

bl_info = {
    "name": "BB Stage",
    "author": "Beta Builder",
    "version": (0, 19, 1),
    "blender": (5, 0, 0),
    "location": "View3D > Sidebar > BB Stage",
    "category": "3D View",
}
# Blender drops or replaces bl_info on extension modules after import: keep our own copy for runtime use
VERSION = tuple(bl_info["version"])

STG_PREFIX = "STG "
LAYER_KEY = "bb_st_layer"          # on collections: SET / STUDIO / STAGE
ROLE_KEY = "bb_st_role"            # on objects: char / prop / studio / boundary / cam
SOURCE_KEY = "bb_st_source"        # stand-in: name of the set object it stands in for
STANDIN_KEY = "bb_st_standin"      # prop flag: placeholder that must never appear in outputs
DT_BACKUP_KEY = "bb_st_dt0"        # ghost mode: original display_type backup
LOCK_KEY = "bb_st_locked"
CAM_KEY = "bb_st_keyed"            # camera: moves on the beats (0.17 and earlier; kept for old files)
STATIC_KEY = "bb_st_static"        # camera: Static — it takes no part in the beats and carries no keys

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
SUB_KEY = "bb_st_sub"              # on STAGE sub-collections: Characters / Props / Cameras
TINT_KEY = "bb_st_c0"              # ghost tint: the object's own colour, restored before saving
DATA_VERSION = 11             # 11 (0.19): beat markers owned by uid, the default hold, stale badges cleared
EYE_HEIGHT = 1.6
HUMAN_MAX_SPEED = 4.0          # m/s between beats: a sprint; above it the beat panel turns red (Aman, 10 Oct 2026)
PEG_MESH_VERSION = 4           # 2: no base disc (Aman, 10 Oct 2026: the disc made characters look bigger)
                               # 3: human proportions, a width, hip and knee joints (Aman, 15 Oct 2026)
                               # 4: the 0.18 post again, with a Height, a Width and the same joints (Aman,
                               #    15 Oct 2026: "The new character pegs looks weird. Make the body uniform like before")
_QUIET = {"floor": False, "beats": False,     # floor: True while an upgrade sets play_level
          "dims": False, "carry": False,      # dims: a resize sets width and depth together
          "saving": False}                    # saving: save_beat is running (no auto-save inside it)
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
    """File-level state (Easy/Artist, handles, Edit Studio) lives on the first set scene, so
    every staging reads the same values. Floors and plan cuts are per set scene: floor_state."""
    m = master_scene()
    return getattr(m, "bb_st", None) if m is not None else None


# A file can hold several set scenes: a house, its gully, an interior, an exterior (Aman,
# 5 Oct 2026). Each staging plays in one of them and links that scene's collections; the
# ones offered for staging are ticked in Stagings › Set scenes (none ticked: all of them).

def set_scenes(offered=True):
    sets = [s for s in bpy.data.scenes if not is_staging(s)]
    if not offered:
        return sets
    ticked = [s for s in sets if getattr(s, "bb_st", None) is not None and s.bb_st.stageable]
    return ticked or sets


def _infer_set_scene(staging):
    """Older stagings did not record their set scene: the one whose collections they link."""
    roots = layer_colls(staging, "SET")
    if not roots:
        return None
    kids = {c.name for c in roots[0].children}
    obs = {o.name for o in roots[0].objects}
    best = None
    for sc in set_scenes(offered=False):
        score = (len(kids & {c.name for c in sc.collection.children})
                 + len(obs & {o.name for o in sc.collection.objects}))
        if score and (best is None or score > best[0]):
            best = (score, sc)
    return best[1] if best else None


def set_scene_of(scene):
    """The set scene a staging plays in (a set scene is its own)."""
    if scene is None or not is_staging(scene):
        return scene
    src = scene.bb_st.set_scene
    if src is not None and bpy.data.scenes.get(src.name) == src and not is_staging(src):
        return src
    return _infer_set_scene(scene) or master_scene()


def floor_state(scene):
    """Floor heights and plan cuts of the set scene this staging plays in."""
    src = set_scene_of(scene)
    return getattr(src, "bb_st", None) if src is not None else None


def stagings_of(set_scene):
    return [s for s in stagings() if set_scene_of(s) == set_scene]


def set_instancers(scene):
    """Collection instances in the set: a house placed in a lane from its own scene."""
    roots = layer_colls(scene, "SET") if is_staging(scene) else [scene.collection]
    return [o for c in roots for o in coll_objects(c)
            if o.type == 'EMPTY' and o.instance_type == 'COLLECTION' and o.instance_collection is not None]


def instanced_objects(scene):
    """Every object a set shows through its collection instances (nested ones too)."""
    seen, out, stack = set(), [], [e.instance_collection for e in set_instancers(scene)]
    while stack:
        c = stack.pop()
        if c.name in seen:
            continue
        seen.add(c.name)
        for o in coll_objects(c):
            out.append(o)
            if o.instance_type == 'COLLECTION' and o.instance_collection is not None:
                stack.append(o.instance_collection)
    return out


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
    if st.data_version == 0 and _made_by_current_version(st):
        # built by a script (or a scene renamed "STG …") that never stamped a version: it is today's staging,
        # not a pre-0.9 one — its cameras must not turn Static nor its Floors switch on (0.19 fix)
        st.data_version = DATA_VERSION
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
    if st.set_scene is None or bpy.data.scenes.get(st.set_scene.name) != st.set_scene:
        src = _infer_set_scene(scene) or master_scene()
        if src is not None and src != scene:
            st.set_scene = src
    for c in layer_colls(scene, "SET"):
        if not c.hide_select:
            c.hide_select = True
    upgrade_beats(scene)
    ensure_beat_uids(scene)
    for cam in stage_cams(scene):
        if cam.show_name:
            cam.show_name = False       # the plan draws its own camera tags (camera labels)
        if st.key_cameras and not cam.get(CAM_KEY):
            cam[CAM_KEY] = True         # the old "Key cameras on beats" switch, per camera now
    if st.key_cameras:
        st.key_cameras = False
    if not st.shell_built and boundary_of(scene) is not None and layer_colls(scene, "STUDIO"):
        build_studio_shell(scene)
    for c in layer_colls(scene, "STUDIO"):
        for ob in coll_objects(c):
            if is_studio_floor(ob) and not all(ob.lock_location):
                lock_floor(ob)
    if st.data_version < 9:
        st["use_floors"] = True         # stagings made before the switch were built on floors
    if st.data_version < 10:
        # cameras are keyed by default from 0.18. A camera that was deliberately left out of the beats
        # before stays out: it is marked Static, so an old staging plays exactly as it did.
        for cam in stage_cams(scene):
            if not cam.get(CAM_KEY) and STATIC_KEY not in cam:
                cam[STATIC_KEY] = True
    if st.data_version < 8:
        # Plays on came with version 8: only a staging older than that takes it from the working level. It ran on
        # every version bump before 0.19 and dropped upper-floor stagings to the ground floor (audit r1 bug 6)
        _QUIET["floor"] = True          # an upgrade must not re-detect the floor and move things
        try:
            st.play_level = st.active_level
        finally:
            _QUIET["floor"] = False
    # 0.19 migrations, in order: one call per stream, each one checks st.data_version itself (or is flags only)
    # and is safe to run again. The version is stamped once, after all of them (integration, 15 Oct 2026).
    _migrate_v11_core(scene)    # s1: beat markers claimed by beat id, stale orange badges dropped
    _migrate_v11_s2(scene)      # s2: Track To last, pre-release owner pointers dropped, camera names noted
    _migrate_v11_s3(scene)      # s3: links characters to the cast library (checks data_version < 11 itself)
    _migrate_v11_s4_setedit(scene)  # s4: set-edit records true to the file, Edit Set off (flags only, every load)
    if st.data_version < DATA_VERSION:
        st.data_version = DATA_VERSION


def _made_by_current_version(st):
    """A staging without a data version that was nevertheless made by 0.11 or later: no beats yet, or every beat
    already has its lasting id (pre-0.9 stagings, the only ones that really have no version, have none)."""
    return not len(st.beats) or all(b.uid > 0 for b in st.beats)


def _migrate_v11_core(scene):
    """0.19: the beat markers become the add-on's own (claimed by beat id, so markers you name "B7" are left
    alone), and an orange badge saved in the file is dropped (loading re-reads the keys: the move is gone)."""
    st = scene.bb_st
    if st.data_version >= 11:
        return
    if not st.beat_marks:
        claim_beat_markers(scene)
    for b in st.beats:
        if b.dirty:
            b.dirty = False


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
    """The staging's output folder. The label goes through safe_folder_name: "Sc 102: Arrival" was a NotADirectoryError
    and "Jai/Shefali" a nested folder (B12, audit r3, 15 Oct 2026)."""
    base = os.path.dirname(bpy.data.filepath) or os.path.expanduser("~")
    d = os.path.join(base, "Stage", safe_folder_name(staging_label(scene)))
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


STOCK_MATS = ("BB Stage Grey", "BB Stage Studio White")     # what a new prop or kit piece is made with


def _ours_material(mat):
    """A material BB Stage made (a peg's own colour, the stock grey of a new prop block): the sync may recolour or
    replace it. Anything else (a hand-made body, an imported prop model) keeps its materials (audit r1, bug 4)."""
    return mat is None or mat.name.startswith("BB Peg") or mat.name.split(".")[0] in STOCK_MATS


def peg_material(ob):
    """Per-peg material so the colour shows in material-shaded panes and renders too. It takes the first slot
    only: the other slots are never cleared."""
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
    if len(ob.data.materials):
        ob.data.materials[0] = mat
    else:
        ob.data.materials.append(mat)
    return mat


def _rgba_differs(a, b, tol=1e-4):
    """Colours are float32 in Blender: never compare them to Python floats with ==."""
    return any(abs(x - y) > tol for x, y in zip(a, b))


def _peg_mat(ob):
    return ob.data.materials[0] if (ob.type == 'MESH' and len(ob.data.materials)) else None


def peg_colors_stale(scene):
    for ob in stage_objects(scene, roles=("char", "prop")):
        if ob.type != 'MESH' or ob.get(SETPIECE_KEY):
            continue                    # a piece taken from the set keeps the set's mesh and materials (s4)
        mat = _peg_mat(ob)
        if not _ours_material(mat):
            continue
        if mat is None or mat.users > 1 or _rgba_differs(mat.diffuse_color, ob.color):
            return True
    return False


def sync_peg_colors(scene):
    """Every peg and stock prop owns a material carrying its colour (camera panes draw material colour). A
    Shift+D copy shares its original's material until this gives it its own. Only what BB Stage made is
    touched: a character with a hand-made body keeps its mesh, and a prop or body with its own materials keeps
    them (audit r1, bug 4: a car lost its paint and glass to one 'BB Peg' material). Pegs of every older design,
    the untagged pre-0.15 ones included, are rebuilt to the current one with their head where it was drawn."""
    for ob in stage_objects(scene, roles=("char", "prop")):
        if ob.type != 'MESH' or ob.data is None or ob.get(SETPIECE_KEY):
            continue                    # a piece taken from the set keeps the set's mesh and materials (s4)
        tag = ob.data.get("bbst_peg")
        mat = _peg_mat(ob)
        ours = _ours_material(mat)
        if ob.data.users > 1 and (tag is not None or ours):
            ob.data = ob.data.copy()        # a linked copy of a peg or a stock block gets its own mesh (and colour)
        if ob.get(ROLE_KEY) == "char" and ob.mode == 'OBJECT':
            if old_peg(ob):
                refresh_peg_mesh(ob)        # an older peg design: rebuilt at the height it was drawn at
            elif tag is not None:
                ensure_peg_pose(ob)
            for h in ob.children:
                if h.get(ROLE_KEY) == EYES_ROLE:
                    ensure_eyes_posture(h)      # a camera in his eyes sits and lies down with him (0.19)
        if not ours:
            continue
        if mat is None or mat.users > 1 or not mat.name.startswith("BB Peg"):
            peg_material(ob)                # writes the colour too
            continue
        if _rgba_differs(mat.diffuse_color, ob.color):
            mat.diffuse_color = tuple(ob.color)
        bsdf = next((n for n in mat.node_tree.nodes if n.type == 'BSDF_PRINCIPLED'), None) if mat.use_nodes else None
        if bsdf and _rgba_differs(bsdf.inputs['Base Color'].default_value, ob.color):
            bsdf.inputs['Base Color'].default_value = tuple(ob.color)


# ------------------------------------------------------------------ the peg (0.19 s7: the 0.18 post, a height, a width, two joints)
#
# Aman, 15 Oct 2026 (afternoon), after seeing 0.19's human-proportioned peg: "The new character pegs looks weird.
# Make the body uniform like before. I just want controls to adjust the overall height and width of the model".
# So the peg is the 0.18 one again, exactly: one round post tapering from the floor to the shoulders (0.85 of its
# foot radius at the top), a ball head sitting just above it and the nose cone pointing where the character faces.
# Each character has two shape controls and no others:
# * Height (m): floor to the top of the head, the whole model scales with it (as in 0.18).
# * Width (m): the model side to side at its widest (the head, by a hair). It scales the whole model sideways,
#   head and nose included, about its vertical axis, so the post stays round. Left alone it is the 0.18 peg's
#   own width for that height (0.274 m at 1.75 m), and the peg is the 0.18 peg to the vertex.
# The 0.18 code drew a peg of Height p with its head top at 0.9575 p (post 0.80 p + head 2.1 x 0.075 p). Since
# 0.19 the Height is the drawn height itself, so a 0.18 peg keeps its head line (its 1.75 reads 1.68) and is
# rebuilt to exactly the vertices 0.18 drew.
#
# The joints: the post is cut at the knee and the hip into three round pieces (shin, thigh, body), and a ball as
# wide as the post sits on each cut, hidden inside it while standing. A geometry-nodes modifier ("BB Pose", one
# shared node group) turns the leg forward at the hip and the shin back at the knee, tips the whole body back to
# lie down and lowers it onto a seat or a bed. Every piece turns about a pivot on the post's axis, so the ball
# fills the outside of the bend exactly (a rounded elbow, never a gap or a pinch) and the cut ends stay inside
# the ball. Its five inputs are driven by five custom properties on the peg (bbst_hip, bbst_knee, bbst_tilt,
# bbst_seat, bbst_rest): those are what the beats key, next to location and rotation, so the peg stays ONE object
# that is selected, moved, keyed, Shift+D-copied and saved like before, and its origin stays on the floor.

OLD_PEG_TOP = 0.9575    # the 0.18 peg drew its head top at 0.9575 x its Height parameter p (post 0.80 + head 2.1 x 0.075)
POST_R = 0.13 / 1.75    # the post's radius at the floor, per p (0.13 m for the 0.18 peg of Height 1.75)
POST_TAPER = 0.85       # ... and at its top, as a part of that
POST_H = 0.80           # the post's top (the shoulders), per p
HEAD_R = 0.075          # the head's radius, per p; its centre sits 1.1 radii above the post
HEAD_C = POST_H + 1.1 * HEAD_R          # 0.8825 p
PEG_W = 2.0 * HEAD_R / OLD_PEG_TOP      # the default Width per metre of Height: 0.274 m at 1.75 m (the head is widest)
HIP_AT = 0.52           # the hip joint, a part of the Height (as in 0.19)
KNEE_AT = 1.0 / 3.0     # the knee joint (a Sit fits the legs so the feet rest on the floor: sit_joints)
WIDTH_019 = PEG_W * 1.75 / 0.34         # a 0.19 Width (the shoulder line, 0.34 m at 1.75 m) -> this Width (x 0.806)
WIDTH_V = 2             # the meaning of a stored Width: 2 = this one; none = 0.19's shoulder line (bbst_wv / width_v)
# 0.19's built-in cast widths (shoulder lines). Its cast upgrade put them on every linked character, guesses nobody
# chose (s7 review: the Dubey file's 77 pegs of one height came out in 6 widths); read back, they are the default
WIDTH_019_BUILTIN = {"jai": 0.35, "shefali": 0.31, "shemda": 0.31, "shaan_daar": 0.43, "riya": 0.31,
                     "namrata": 0.30, "dwijal": 0.34, "mr_dubey": 0.36, "kailash": 0.37, "ajit": 0.34, "zarine": 0.31,
                     "aunty": 0.33, "student": 0.31, "gamer_boy": 0.29, "gamer_teen": 0.31, "footballer": 0.31,
                     "extra": 0.34, "child": 0.25}
POSE_MOD = "BB Pose"
POSE_GROUP = "BB Peg Pose"
POSE_GROUP_V = 2        # bump when the node tree changes: pegs pick up the new group on their next sync
                        # 2 (s7 review): a seat lifts the hip by the thigh's radius, a bed by the head's
POSE_CHANNELS = (       # (custom property on the peg = the keyed channel, node group input, standing value)
    ("bbst_hip", "Hip", 0.0),           # radians: the thigh comes forward (90° sitting)
    ("bbst_knee", "Knee", 0.0),         # radians: the shin folds back (90° sitting)
    ("bbst_tilt", "Lie back", 0.0),     # radians: the whole body tips back about the hip (90° lying on the back)
    ("bbst_seat", "Seat height", 0.45),  # metres above the floor: the seat or bed it rests on
    ("bbst_rest", "Resting", 0.0),      # 0 on its feet, 1 resting on the seat or bed
)
POSE_PATHS = {f'["{p}"]': p for p, _l, _v in POSE_CHANNELS}
POSE_KEYS = tuple((path, 0) for path in POSE_PATHS)
POSE_NEUTRAL = {p: v for p, _l, v in POSE_CHANNELS}
REST_KEY = ('["bbst_rest"]', 0)
SIT_AT = 0.45           # a chair seat
LIE_AT = 0.0            # the floor (a bed is about 0.55)
POSE_SECS = 1.2         # Natural moves: how long sitting down, lying down or getting up takes


def default_width(height):
    """A character's Width when nobody set one: the 0.18 peg's own, in proportion to the height (0.274 m at
    1.75 m)."""
    return PEG_W * max(0.5, float(height))


def width_from_019(width, height, cid=None, unset=None):
    """A Width 0.19 wrote (the shoulder line of its human-shaped peg) as this peg's Width. 0.19's own default for
    the height, a built-in cast guess its cast upgrade imposed (WIDTH_019_BUILTIN) and an entry's never-written
    default (unset) were nobody's choice: they come back as the default, so the body is uniform again (Aman,
    15 Oct 2026). A width somebody typed keeps its build (x 0.806)."""
    h = max(0.5, float(height))
    try:
        w = float(width or 0.0)
    except Exception:
        w = 0.0
    if w <= 0.0 or abs(w - round(0.34 * h / 1.75, 3)) < 6e-4:
        return default_width(h)
    if (cid in WIDTH_019_BUILTIN and abs(w - WIDTH_019_BUILTIN[cid]) < 6e-4) or (unset is not None and abs(w - unset) < 1e-5):
        return default_width(h)
    return w * WIDTH_019


def peg_dims(height=1.75, width=None):
    """The peg's key heights and sizes for this Height (floor to the top of the head) and Width (side to side).
    p is the 0.18 Height parameter that draws the same peg; s the sideways scale (1 at the default width)."""
    h = max(0.5, float(height))
    p = h / OLD_PEG_TOP
    w0 = PEG_W * h
    w = float(width) if width else w0
    s = w / w0
    r0, top = POST_R * p, POST_H * p
    r_at = lambda z: r0 * (1.0 - (1.0 - POST_TAPER) * z / top)
    hip, knee = HIP_AT * h, KNEE_AT * h
    head_r = HEAD_R * p
    return dict(h=h, w=w, s=s, p=p, r0=r0, top=top, r_top=r_at(top), hip=hip, knee=knee,
                r_hip=r_at(hip), r_knee=r_at(knee), head_r=head_r, head_c=HEAD_C * p,
                nose_tip=(s + 0.89) * head_r,   # the 0.18 nose cone (1.08 head radii long) on the front of the head:
                                                # Width moves it out with the head, never makes it longer
                rest_off=head_r * s,            # the hip pivot above a bed: lying, the head (the widest part) rests
                sit_off=r_at(knee) * s)         # ... and above a seat: sitting, the thigh does (its knee end)


def peg_parts(height=1.75, width=None):
    """The peg, part by part, as primitives anybody can rebuild (BB Crowd draws its crowd with the 0.18 peg):
    CONE = a round frustum on Z (radius r0 at z0, r1 at z1), BALL = a sphere (radius r at c), SPHERE = the head
    (radii r), NOSE = the 0.18 nose cone on +Y. Everything is the 0.18 peg's shape scaled sideways by s. part: 0
    rides with the body, 1 is the thigh (turns at the hip), 2 the shin (turns at the knee and the hip). The balls
    sit on the cuts at the knee and the hip, as wide as the post there and hidden inside it while standing."""
    d = peg_dims(height, width)
    s, top, hip, knee = d["s"], d["top"], d["hip"], d["knee"]
    r = lambda z: d["r0"] * (1.0 - (1.0 - POST_TAPER) * z / top) * s
    hr, hc = d["head_r"], d["head_c"]
    return [
        dict(name="Shin", part=2, kind='CONE', seg=16, z0=0.0, z1=knee, r0=r(0.0), r1=r(knee)),
        dict(name="Knee", part=1, kind='BALL', seg=16, rings=8, c=(0.0, 0.0, knee), r=min(r(knee), knee)),
        dict(name="Thigh", part=1, kind='CONE', seg=16, z0=knee, z1=hip, r0=r(knee), r1=r(hip)),
        dict(name="Hip", part=0, kind='BALL', seg=16, rings=8, c=(0.0, 0.0, hip), r=min(r(hip), top - hip)),
        dict(name="Body", part=0, kind='CONE', seg=16, z0=hip, z1=top, r0=r(hip), r1=r(top)),
        dict(name="Head", part=0, kind='SPHERE', seg=12, rings=8, c=(0.0, 0.0, hc), r=(hr * s, hr * s, hr)),
        dict(name="Nose", part=0, kind='NOSE', seg=10, c=(0.0, (s + 0.35) * hr, hc), r=0.45 * hr, length=1.08 * hr,
             s=s),       # 0.18's nose (centred 1.35 head radii out), on the front of a wider or narrower head
    ]


def peg_bmesh(height=1.75, width=None):
    """The peg as a bmesh, built from peg_parts with the very bmesh primitives the 0.18 peg used (the same vertex
    angles: the balls' 16 sides line up with the post's). Every vertex carries its part in the int layer
    'bbst_part', read off the vertices each primitive returns (a sphere frees pole vertices that the next
    primitive reuses, so "the vertices added last" is not a piece). No base disc since 0.15 (it read as the
    character's footprint and made everyone look bigger)."""
    bm = bmesh.new()
    layer = bm.verts.layers.int.new("bbst_part")
    for p in peg_parts(height, width):
        if p["kind"] == 'CONE':
            made = bmesh.ops.create_cone(bm, cap_ends=True, segments=p["seg"], radius1=p["r0"], radius2=p["r1"],
                                         depth=p["z1"] - p["z0"],
                                         matrix=Matrix.Translation((0.0, 0.0, (p["z0"] + p["z1"]) / 2)))
        elif p["kind"] == 'BALL':
            made = bmesh.ops.create_uvsphere(bm, u_segments=p["seg"], v_segments=p["rings"], radius=p["r"],
                                             matrix=Matrix.Translation(p["c"]))
        elif p["kind"] == 'SPHERE':
            mat = Matrix.Translation(p["c"]) @ Matrix.Diagonal((*p["r"], 1.0))
            made = bmesh.ops.create_uvsphere(bm, u_segments=p["seg"], v_segments=p["rings"], radius=1.0, matrix=mat)
        else:   # the nose: the 0.18 cone along +Y, as wide as the Width makes it, as long as 0.18's (s7 review:
                # a wide peg's nose reached past the Eyes-of camera)
            mat = (Matrix.Translation(p["c"]) @ Matrix.Diagonal((p["s"], 1.0, 1.0, 1.0))
                   @ Matrix.Rotation(-math.pi / 2, 4, 'X')
                   @ Matrix.Diagonal((p["r"], p["r"], p["length"] / 1.2, 1.0)))
            made = bmesh.ops.create_cone(bm, cap_ends=True, segments=p["seg"], radius1=1.0, radius2=0.0, depth=1.2,
                                         matrix=mat)
        for v in made["verts"]:
            if v.is_valid:
                v[layer] = p["part"]
    return bm


def _set_attr(me, name, kind, values):
    a = me.attributes.get(name)
    if a is not None and (a.data_type != kind or a.domain != 'POINT'):
        me.attributes.remove(a)
        a = None
    if a is None:
        a = me.attributes.new(name, kind, 'POINT')
    a.data.foreach_set("vector" if kind == 'FLOAT_VECTOR' else "value", values)


def write_peg_mesh(me, height=1.75, width=None):
    """Write the current peg design into a mesh: geometry, the part of every vertex, the joint pivots, the tag."""
    d = peg_dims(height, width)
    bm = peg_bmesh(d["h"], d["w"])
    bm.to_mesh(me)
    bm.free()
    n = len(me.vertices)
    part = [0] * n
    me.attributes["bbst_part"].data.foreach_get("value", part)
    _set_attr(me, "bbst_shin", 'BOOLEAN', [p == 2 for p in part])
    _set_attr(me, "bbst_leg", 'BOOLEAN', [p >= 1 for p in part])
    _set_attr(me, "bbst_hip_p", 'FLOAT_VECTOR', [0.0, 0.0, d["hip"]] * n)
    _set_attr(me, "bbst_knee_p", 'FLOAT_VECTOR', [0.0, 0.0, d["knee"]] * n)
    _set_attr(me, "bbst_off", 'FLOAT', [d["rest_off"]] * n)
    _set_attr(me, "bbst_off_sit", 'FLOAT', [d["sit_off"]] * n)
    me["bbst_peg"] = PEG_MESH_VERSION
    me.update()


def old_peg(ob):
    """A peg made before 0.19 that the next sync rebuilds: a character mesh with an older bbst_peg tag, or a
    pre-0.15 peg that has no tag at all (the Daaruwala v0.9 staging: a base disc, 175 vertices, BB Stage's own
    'BB Peg' material, standing on its origin). A hand-made body is none of these and is never rebuilt. The 0.19
    human-shaped pegs (tag 3) are older too: s7 brings every peg back to the uniform post."""
    if ob is None or ob.type != 'MESH' or ob.data is None or ob.get(ROLE_KEY) != "char":
        return False
    tag = ob.data.get("bbst_peg")
    if tag is not None:
        return tag != PEG_MESH_VERSION
    mat = _peg_mat(ob)
    me = ob.data
    if mat is None or not (mat.name.startswith("BB Peg") or mat.name.split(".")[0] == "BB Stage Peg"):
        return False
    if not 0 < len(me.vertices) <= 200 or len(me.materials) > 1:
        return False
    zs = [v.co.z for v in me.vertices]
    return abs(min(zs)) < 1e-3 and 0.3 < max(zs) < 3.0


def _peg_tag(ob):
    try:
        tag = ob.data.get("bbst_peg") if (ob.type == 'MESH' and ob.data is not None) else None
        return None if tag is None else int(tag)
    except Exception:
        return None


def peg_height_of(ob):
    """Floor to the top of the head, as the peg is drawn. Pegs before 0.19 (tags 1-2) drew their head 4 % short of
    the Height they carried (1.75 drew 1.676): for them this is the height they are drawn at, so a rebuild keeps
    the head line every shot was framed on (review of 15 Oct: nothing may move in Peddar Road or Gossip Maze).
    The 0.19 pegs (tag 3) and these (tag 4) carry the drawn height itself."""
    h = ob.get("bbst_height")
    tag = _peg_tag(ob)
    old = tag is not None and tag < 3
    if h:
        return round(float(h) * OLD_PEG_TOP, 4) if old else float(h)
    try:
        top = max(v.co.z for v in ob.data.vertices)
        return top if top > 0.3 else 1.75
    except Exception:
        return 1.75


def peg_width_of(ob):
    """The character's Width: side to side at the widest, in metres. A Width 0.19 wrote (no bbst_wv mark) meant
    the shoulder line of the human-shaped peg (0.34 m at 1.75 m): 0.19's default and the cast guesses its upgrade
    imposed read as the default, anything else as the same build of this peg (x 0.806, width_from_019). Pegs
    before 0.19 had no Width: the default for their height."""
    w = ob.get("bbst_width")
    if not w:
        return default_width(peg_height_of(ob))
    if ob.get(WIDTH_V_KEY) == WIDTH_V:
        return float(w)
    return width_from_019(w, peg_height_of(ob), ob.get(CAST_KEY) or None)


def peg_build_of(ob):
    """The character's build: his Width as a part of the default for his height (1 = the standard peg). A new
    Height keeps it, so the whole model scales and the head stays a ball (s7 review)."""
    return peg_width_of(ob) / default_width(peg_height_of(ob))


WIDTH_V_KEY = "bbst_wv"             # on a character: the meaning of its bbst_width (WIDTH_V); none = 0.19's


def _store_size(ob, height, width):
    ob["bbst_height"] = float(height)
    ob["bbst_width"] = float(width)
    ob[WIDTH_V_KEY] = WIDTH_V


def rebuild_peg(ob, height, width):
    """Write the current peg design into this character's own mesh at this height and width (keeps the object,
    its colour, its keys and its pose)."""
    if ob.type != 'MESH' or ob.data is None:
        return
    if ob.data.users > 1:
        ob.data = ob.data.copy()
    write_peg_mesh(ob.data, height, width)
    _store_size(ob, height, width)
    ensure_peg_pose(ob)


def refresh_peg_mesh(ob):
    """Rebuild a peg's mesh in place to the current design at its own height and width."""
    rebuild_peg(ob, peg_height_of(ob), peg_width_of(ob))


def rebuildable(ob):
    """A peg BB Stage may rebuild: the current design or an older one, never a hand-made body."""
    return (ob is not None and ob.type == 'MESH' and ob.data is not None and ob.get(ROLE_KEY) == "char"
            and ob.mode == 'OBJECT' and (ob.data.get("bbst_peg") is not None or old_peg(ob)))


def follow_height(ob, h0, h1):
    """A character's height changed from h0 to h1: whatever sits on his head moves with it. The 'Eyes of' helper
    (a child of the peg, keyed on every beat) goes up or down by the same amount, on every key, so a camera in his
    eyes stays in his eyes (review of 15 Oct)."""
    dz = float(h1) - float(h0)
    if abs(dz) < 1e-5 or ob is None:
        return 0
    n = 0
    for h in [o for o in ob.children if o.get(ROLE_KEY) == "eyes"]:
        h.location.z += dz
        for fc in id_fcurves(h):
            if fc.data_path == "location" and fc.array_index == 2:
                for k in fc.keyframe_points:
                    k.co.y += dz
                    k.handle_left.y += dz
                    k.handle_right.y += dz
                fc.update()
        ensure_eyes_posture(h)          # the posture drivers are built for the eyes' height and the hip's
        n += 1
    return n


def set_char_size(ob, height, width=None):
    """A character takes this height and width: a peg is rebuilt (a hand-made body keeps its mesh) and his eyes
    follow the new head height. True when something changed. Width None keeps his build: the overall Height
    scales the whole model, sideways too (Aman, 15 Oct 2026: "controls to adjust the overall height and width of
    the model"; s7 review: a Height typed alone stretched the peg and turned the head into an egg)."""
    if ob is None or ob.get(ROLE_KEY) != "char":
        return False
    h0, w0 = peg_height_of(ob), peg_width_of(ob)
    height = float(height)
    width = float(width) if width else w0 / default_width(h0) * default_width(height)
    if abs(h0 - height) < 1e-4 and abs(w0 - width) < 1e-4 and not old_peg(ob):
        return False
    if rebuildable(ob):
        rebuild_peg(ob, height, width)
    else:
        _store_size(ob, height, width)
    follow_height(ob, h0, height)
    return True


def build_peg_object(name, height=1.75, color=(0.8, 0.2, 0.2, 1.0), width=None):
    w = float(width) if width else default_width(height)
    me = bpy.data.meshes.new(name)
    write_peg_mesh(me, height, w)
    ob = bpy.data.objects.new(name, me)
    _store_size(ob, height, w)
    ob.color = color
    ob[ROLE_KEY] = "char"
    ob.show_name = True
    ob.lock_location[2] = True
    ob.lock_rotation[0] = True
    ob.lock_rotation[1] = True
    peg_material(ob)
    ensure_peg_pose(ob)
    return ob


def peg_pose_group():
    """The one node group every peg's BB Pose modifier uses: knee, then hip, then lie back and rest, each a turn
    about the X axis through a pivot the peg's mesh carries (bbst_knee_p, bbst_hip_p)."""
    ng = bpy.data.node_groups.get(POSE_GROUP)
    if ng is not None and ng.get("bbst_v") == POSE_GROUP_V and len(ng.nodes):
        return ng
    if ng is not None:
        ng.name = POSE_GROUP + " (old)"       # the pegs move over to the new one on their next sync
    ng = bpy.data.node_groups.new(POSE_GROUP, 'GeometryNodeTree')
    ng["bbst_v"] = POSE_GROUP_V
    itf = ng.interface
    itf.new_socket("Geometry", in_out='INPUT', socket_type='NodeSocketGeometry')
    itf.new_socket("Geometry", in_out='OUTPUT', socket_type='NodeSocketGeometry')
    for prop, label, v in POSE_CHANNELS:
        sk = itf.new_socket(label, in_out='INPUT', socket_type='NodeSocketFloat')
        sk.default_value = v
    nodes, links = ng.nodes, ng.links
    gi, go = nodes.new('NodeGroupInput'), nodes.new('NodeGroupOutput')

    def attr(name, kind):
        n = nodes.new('GeometryNodeInputNamedAttribute')
        n.data_type = kind
        n.inputs["Name"].default_value = name
        return n.outputs["Attribute"]

    def math_(op, a, b):
        n = nodes.new('ShaderNodeMath')
        n.operation = op
        for k, v in enumerate((a, b)):
            if isinstance(v, (int, float)):
                n.inputs[k].default_value = v
            else:
                links.new(v, n.inputs[k])
        return n.outputs[0]

    def turn(vec, centre, angle):
        n = nodes.new('ShaderNodeVectorRotate')
        n.rotation_type = 'X_AXIS'
        links.new(vec, n.inputs["Vector"])
        links.new(centre, n.inputs["Center"])
        links.new(angle, n.inputs["Angle"])
        return n.outputs["Vector"]

    def set_pos(geo, sel, pos_):
        n = nodes.new('GeometryNodeSetPosition')
        links.new(geo, n.inputs["Geometry"])
        if sel is not None:
            links.new(sel, n.inputs["Selection"])
        links.new(pos_, n.inputs["Position"])
        return n.outputs["Geometry"]

    pos = nodes.new('GeometryNodeInputPosition').outputs["Position"]
    hip_p, knee_p = attr("bbst_hip_p", 'FLOAT_VECTOR'), attr("bbst_knee_p", 'FLOAT_VECTOR')
    g = set_pos(gi.outputs["Geometry"], attr("bbst_shin", 'BOOLEAN'),
                turn(pos, knee_p, math_('MULTIPLY', gi.outputs["Knee"], -1.0)))       # the shin folds back
    g = set_pos(g, attr("bbst_leg", 'BOOLEAN'), turn(pos, hip_p, gi.outputs["Hip"]))   # the leg comes forward
    sep = nodes.new('ShaderNodeSeparateXYZ')
    links.new(hip_p, sep.inputs[0])
    # the hip joint above the seat: by the thigh's radius sitting up, by the head's lying back (rest_offset)
    off_sit = attr("bbst_off_sit", 'FLOAT')
    lean = math_('ABSOLUTE', math_('SINE', gi.outputs["Lie back"], 0.0), 0.0)
    off = math_('ADD', off_sit, math_('MULTIPLY', math_('SUBTRACT', attr("bbst_off", 'FLOAT'), off_sit), lean))
    target = math_('ADD', gi.outputs["Seat height"], off)
    dz = math_('MULTIPLY', math_('SUBTRACT', target, sep.outputs["Z"]), gi.outputs["Resting"])
    lift = nodes.new('ShaderNodeCombineXYZ')
    links.new(dz, lift.inputs["Z"])
    add = nodes.new('ShaderNodeVectorMath')
    add.operation = 'ADD'
    links.new(turn(pos, hip_p, gi.outputs["Lie back"]), add.inputs[0])
    links.new(lift.outputs["Vector"], add.inputs[1])
    g = set_pos(g, None, add.outputs["Vector"])                                        # lie back, sit down
    links.new(g, go.inputs["Geometry"])
    for k, n in enumerate(nodes):
        n.location = (200.0 * k, 0.0)
    return ng


def _pose_driver_path(mod, ident):
    if hasattr(mod, "properties"):          # Blender 5.2: the inputs live on modifier.properties.inputs
        return f'modifiers["{mod.name}"].properties.inputs.{ident}.value'
    return f'modifiers["{mod.name}"]["{ident}"]'


def ensure_peg_pose(ob):
    """Give a peg (current design) its joints: the five pose properties, the BB Pose modifier and the drivers that
    feed it. Cheap when everything is in place; repairs whatever is missing or points at another object."""
    if ob is None or ob.type != 'MESH' or ob.data is None or ob.get(ROLE_KEY) != "char":
        return False
    if ob.data.get("bbst_peg") != PEG_MESH_VERSION:
        return False
    for prop, label, v in POSE_CHANNELS:
        if prop not in ob:
            ob[prop] = v
            try:
                ui = ob.id_properties_ui(prop)
                if prop in ("bbst_hip", "bbst_knee", "bbst_tilt"):
                    ui.update(subtype='ANGLE', min=-math.pi, max=math.pi, soft_min=-math.radians(30),
                              soft_max=math.radians(150), description=f"{label}: keyed on the beats")
                elif prop == "bbst_seat":
                    ui.update(subtype='DISTANCE', min=0.0, max=5.0, description="Seat or bed height: keyed on the beats")
                else:
                    ui.update(subtype='FACTOR', min=0.0, max=1.0, description="0 on its feet, 1 resting: keyed on the beats")
            except Exception:
                pass
    ng = peg_pose_group()
    mod = ob.modifiers.get(POSE_MOD)
    if mod is not None and mod.type != 'NODES':
        ob.modifiers.remove(mod)
        mod = None
    if mod is None:
        mod = ob.modifiers.new(POSE_MOD, 'NODES')
        mod.show_in_editmode = False
    if mod.node_group != ng:
        mod.node_group = ng
    idents = {it.name: it.identifier for it in ng.interface.items_tree
              if getattr(it, "in_out", None) == 'INPUT' and getattr(it, "socket_type", "") == 'NodeSocketFloat'}
    have = {fc.data_path: fc for fc in (ob.animation_data.drivers if ob.animation_data else [])}
    for prop, label, _v in POSE_CHANNELS:
        ident = idents.get(label)
        if ident is None:
            continue
        path = _pose_driver_path(mod, ident)
        fc = have.get(path)
        try:
            var = fc.driver.variables[0] if (fc is not None and len(fc.driver.variables) == 1) else None
            ok = (var is not None and fc.driver.type == 'SUM' and var.type == 'SINGLE_PROP'
                  and var.targets[0].id == ob and var.targets[0].data_path == f'["{prop}"]')
        except Exception:
            ok = False
        if ok:
            continue
        if fc is not None:
            ob.driver_remove(path)
        fc = ob.driver_add(path)
        fc.driver.type = 'SUM'
        var = fc.driver.variables.new()
        var.name = prop
        var.type = 'SINGLE_PROP'
        var.targets[0].id_type = 'OBJECT'
        var.targets[0].id = ob
        var.targets[0].data_path = f'["{prop}"]'
    return True


def is_peg(ob):
    return (ob is not None and ob.type == 'MESH' and ob.data is not None and ob.get(ROLE_KEY) == "char"
            and ob.data.get("bbst_peg") == PEG_MESH_VERSION)


SIT_KNEES_UP = math.radians(60.0)  # the most a Sit raises the knees; lower seats stretch the legs out instead


def sit_joints(height, width, seat):
    """(hip, knee) of a Sit on this seat, fitted to this character's legs so the feet rest on the floor (s7
    review: the shin grows with the Height and the seat does not, so a 2.13 m Shaan Daar sank 9 cm into the floor
    and a narrow peg 3 cm). The thigh rests on the seat; when the shin is longer than the knee is high, the knees
    come up (hip and knee bend alike, the shin stays upright and the foot flat on the floor), as a tall man sits
    on a low chair; on a very low seat or the floor the legs stretch out forward instead. A shin too short to
    reach hangs straight down (a child on a chair: 90° and 90°, as 0.19's preset)."""
    d = peg_dims(height, width)
    zp = max(0.0, float(seat)) + d["sit_off"]           # the hip joint on the seat
    L, thigh = d["knee"], d["hip"] - d["knee"]          # the shin (joint to sole) and the thigh (joint to joint)
    need = L - zp                                       # how far the knee must rise for an upright shin to stand
    right = math.radians(90.0)
    if need <= 0.0:
        return right, right
    if need <= thigh * math.sin(SIT_KNEES_UP):
        b = math.asin(need / thigh)
        return right + b, right + b
    r = d["r0"] * d["s"]                                # legs out: the shin leans forward until the front of
    R, a = math.hypot(L, r), math.atan2(r, L)           # its sole touches the floor (knee 0 on the floor itself)
    phi = a + math.acos(min(1.0, zp / R))
    return right, right - min(phi, right + math.radians(5.0))      # on the floor: a hair past straight


def rest_offset(sit_off, lie_off, tilt):
    """How far above the seat or bed the hip joint rests (BB Pose does the same): the thigh's radius sitting up,
    the head's lying back, in between as the body leans (s7 review: a seated peg floated on the head's radius)."""
    return sit_off + (lie_off - sit_off) * abs(math.sin(tilt))


def pose_values(kind, at=None, ob=None):
    """The pose properties of a preset. Stand leaves the seat height alone, so getting up does not slide it. A
    Sit fits hip and knee to this character's legs and the seat (sit_joints) when the character is given; else
    90° and 90°."""
    if kind == 'SIT':
        seat = SIT_AT if at is None else float(at)
        hip = knee = math.radians(90.0)
        if ob is not None and is_peg(ob):
            hip, knee = sit_joints(peg_height_of(ob), peg_width_of(ob), seat)
        return dict(bbst_hip=hip, bbst_knee=knee, bbst_tilt=0.0, bbst_seat=seat, bbst_rest=1.0)
    if kind == 'LIE':
        return dict(bbst_hip=0.0, bbst_knee=0.0, bbst_tilt=math.radians(90.0),
                    bbst_seat=LIE_AT if at is None else float(at), bbst_rest=1.0)
    return dict(bbst_hip=0.0, bbst_knee=0.0, bbst_tilt=0.0, bbst_rest=0.0)


def pose_kind(ob):
    """STAND / SIT / LIE / CUSTOM from the pose the character holds right now."""
    if ob is None or ob.get(ROLE_KEY) != "char":
        return 'STAND'
    v = {p: float(ob.get(p, d)) for p, d in POSE_NEUTRAL.items()}
    for kind, who in (('STAND', None), ('SIT', ob), ('SIT', None), ('LIE', None)):      # a Sit: fitted, or 90° (0.19)
        want = pose_values(kind, v["bbst_seat"], who)
        if all(abs(v[p] - x) < 1e-3 for p, x in want.items()):
            return kind
    return 'CUSTOM'


# Where the joints put the head (0.19 integration, 15 Oct 2026): a camera that looks at somebody aims at his
# head at his own height, and a camera in his eyes sits and lies down with him. The math is the BB Pose node
# group's for the torso (part 0): a turn about X through the hip pivot by "Lie back", then the lift onto the seat.

AIM_AT = HEAD_C / OLD_PEG_TOP     # a tracked character is aimed at the centre of his head: 0.92 of his height
                                  # (s7: the 0.18 head is back. 0.18 aimed everybody at 1.55 m, AIM_HEAD: its 1.75
                                  # peg's head centre was 1.544, a 1.30 m child's 25 cm lower)


def pose_at(ob, frame=None):
    """A character's pose channels on a frame, read from its keys (no playhead moves); its values now without
    a frame or a key."""
    out = {}
    for p, d in POSE_NEUTRAL.items():
        fc = _curve(ob, f'["{p}"]') if frame is not None else None
        try:
            out[p] = float(fc.evaluate(frame)) if fc is not None else float(ob.get(p, d))
        except Exception:
            out[p] = float(d)
    return out


def posed_point(ob, local, pose=None):
    """A point of a standing peg's torso or head (local coordinates) where its BB Pose joints put it. A
    character without joints (a hand-made body, a peg of an older design) keeps it."""
    v = Vector(local)
    if not is_peg(ob):
        return v
    pose = pose if pose is not None else pose_at(ob)
    d = peg_dims(peg_height_of(ob), peg_width_of(ob))
    hip, t = d["hip"], pose["bbst_tilt"]
    lift = (pose["bbst_seat"] + rest_offset(d["sit_off"], d["rest_off"], t) - hip) * pose["bbst_rest"]
    c, s = math.cos(t), math.sin(t)
    y, z = v.y, v.z - hip
    return Vector((v.x, y * c - z * s, y * s + z * c + hip + lift))


def look_offset(tgt, frame):
    """Where a camera tracking this object aims, as an offset from its origin in world axes (the aim's Copy
    Location adds it): a character's head at his own height, standing, sitting or lying (s3 review: a 1.30 m
    child was aimed 25 cm over his head); anything else its origin."""
    if tgt is None or tgt.get(ROLE_KEY) != "char":
        return Vector((0.0, 0.0, 0.0))
    p = posed_point(tgt, (0.0, 0.0, AIM_AT * peg_height_of(tgt)), pose_at(tgt, frame))
    return Euler(keyed_rotation_at(tgt, frame)).to_matrix() @ p


def ensure_pose_curves(scene, ob):
    """A character's pose joins the beats the first time it changes. Until then it stood on every beat, so the
    pose curves start out standing, keyed where the layout keys a channel that never moves (the first and the
    last beat); the change itself is then an unsaved edit on this beat, saved by Save Beat like a move."""
    if not is_peg(ob) or not is_staging(scene):
        return False
    st = scene.bb_st
    have = {fc.data_path for fc in id_fcurves(ob)}
    missing = [path for path in POSE_PATHS if path not in have]
    if not missing or not len(st.beats):
        return False
    if not any(k[0] in _BLOCK_PATHS for k in block_channels(ob)):
        return False                        # never keyed at all: Save Beat keys everything at once
    frames = sorted({st.beats[0].frame, beat_out(st.beats[0]), st.beats[-1].frame, beat_out(st.beats[-1])})
    now = {POSE_PATHS[path]: ob.get(POSE_PATHS[path], POSE_NEUTRAL[POSE_PATHS[path]]) for path in missing}
    for path in missing:
        prop = POSE_PATHS[path]
        ob[prop] = POSE_NEUTRAL[prop]
        for f in frames:
            ob.keyframe_insert(path, frame=f, group="BB Stage")
    for prop, v in now.items():
        ob[prop] = v
    return True


def mark_unsaved_pose(scene, ob):
    """A pose set from the panel turns the beat at the playhead orange, like a move does. Merged 0.19: it goes
    through s1's unsaved state (_TOUCHED), so the badge, Save Beat's "only what moved" and the save-first rules
    see a sit or a lie the way they see a drag; between two beats it is "Moved between two beats"."""
    if not is_staging(scene) or not len(scene.bb_st.beats):
        return
    if off_key_channels(ob, scene.frame_current):
        _TOUCHED.setdefault(_sid(scene), set()).add(_sid(ob))
        _apply_unsaved(scene)


def set_pose(scene, ob, values):
    """Pose a character now (an unsaved change on this beat until Save Beat)."""
    if not is_peg(ob):
        return False
    ensure_peg_pose(ob)
    if is_staging(scene):
        ensure_pose_curves(scene, ob)
    changed = False
    for prop, v in values.items():
        if abs(float(ob.get(prop, POSE_NEUTRAL.get(prop, 0.0))) - float(v)) > 1e-7:
            ob[prop] = float(v)
            changed = True
    if changed:
        ob.update_tag(refresh={'OBJECT', 'DATA'})
        mark_unsaved_pose(scene, ob)
    return changed


# Feet on the floor while sitting down, lying down and getting up (0.19.1; s7 review #4, still open in 0.19.0). The
# beats key the five pose channels and the move eases them together over the same stretch. The body comes down in
# step with Resting, but the legs fold up only with the cosine of the hip: half way down a sitter's feet were about
# 10 cm under the floor. The fix is in the timing, not in BB Pose: once a move is keyed, Resting is held back wherever
# it would push the legs through the floor, with a few in-between keys typed as generated (every Save Beat derives
# them again). The beat poses, the joints' own keys and the node group stay as they were, and everything that reads
# the channels (Looks at, Eyes of, posed_point) follows by itself.

_LEG_CACHE = {}                 # mesh session id: (its size key, the leg geometry)
PLANT_EPS = 0.002               # metres under the floor that count


def _leg_geometry(ob):
    """What BB Pose turns of this peg's legs, read from its own mesh: the leg vertices (y, z), which of them are the
    shin, the hip and knee pivots and the contact offsets. None for anything that is not a current peg."""
    import numpy as np
    if not is_peg(ob):
        return None
    me = ob.data
    n = len(me.vertices)
    key = (n, me.get("bbst_peg"), round(float(ob.get("bbst_height", 0.0)), 5), round(float(ob.get("bbst_width", 0.0)), 5))
    got = _LEG_CACHE.get(me.session_uid)
    if got is not None and got[0] == key:
        return got[1]
    try:
        at = me.attributes
        co = np.empty(n * 3, dtype=np.float32)
        me.vertices.foreach_get("co", co)
        co = co.reshape(n, 3).astype(np.float64)
        leg = np.zeros(n, dtype=bool)
        at["bbst_leg"].data.foreach_get("value", leg)
        shin = np.zeros(n, dtype=bool)
        at["bbst_shin"].data.foreach_get("value", shin)
        g = dict(y=co[leg, 1], z=co[leg, 2], shin=shin[leg], hz=float(at["bbst_hip_p"].data[0].vector.z),
                 kz=float(at["bbst_knee_p"].data[0].vector.z), off_sit=float(at["bbst_off_sit"].data[0].value),
                 off_lie=float(at["bbst_off"].data[0].value))
    except Exception:
        return None
    if not len(g["z"]):
        return None
    _LEG_CACHE[me.session_uid] = (key, g)
    return g


def legs_low(g, hip, knee, tilt):
    """The lowest point of the legs (object space, before the body is lowered onto a seat) for these joints: BB
    Pose's turns, each about X through its pivot (the shin back at the knee, the leg forward at the hip, all of it
    back about the hip)."""
    y, z = g["y"].copy(), g["z"].copy()
    s = g["shin"]
    kz, hz = g["kz"], g["hz"]
    c, sn = math.cos(-knee), math.sin(-knee)
    ys, zs = y[s], z[s] - kz
    y[s], z[s] = ys * c - zs * sn, kz + ys * sn + zs * c
    for ang in (hip, tilt):
        c, sn = math.cos(ang), math.sin(ang)
        zz = z - hz
        y, z = y * c - zz * sn, hz + y * sn + zz * c
    return float(z.min())


def legs_clearance(g, pose):
    """How far above the floor the lowest point of the legs is in this pose (negative: under it), and the most
    Resting can be without going under (None when Resting does not lower the body)."""
    low = legs_low(g, pose["bbst_hip"], pose["bbst_knee"], pose["bbst_tilt"])
    t = pose["bbst_tilt"]
    target = pose["bbst_seat"] + g["off_sit"] + (g["off_lie"] - g["off_sit"]) * abs(math.sin(t))
    drop = g["hz"] - target                       # how far Resting = 1 lowers the hip
    return low - drop * pose["bbst_rest"], (low / drop if drop > 1e-6 else None)


def plant_feet(ob, layout):
    """Hold this peg's Resting back wherever the move would put its legs under the floor (see above). layout: the
    beats' (arrive, leave) frames. Returns the number of keys it added."""
    g = _leg_geometry(ob)
    fc = _curve(ob, '["bbst_rest"]') if g is not None else None
    if fc is None or len(fc.keyframe_points) < 2:
        return 0
    curves = {p: _curve(ob, f'["{p}"]') for p in POSE_NEUTRAL}

    def pose(f):
        return {p: (float(c.evaluate(f)) if c is not None else float(ob.get(p, POSE_NEUTRAL[p])))
                for p, c in curves.items()}

    added = 0
    for i in range(1, len(layout)):
        s, e = int(layout[i - 1][1]), int(layout[i][0])
        if e - s < 2 or abs(fc.evaluate(s) - fc.evaluate(e)) < 1e-3:
            continue                                # nobody sits down, lies down or gets up in this move
        want = {}
        for f in range(s + 1, e):
            p = pose(f)
            gap, top = legs_clearance(g, p)
            if gap < -PLANT_EPS and top is not None:
                want[f] = max(0.0, min(p["bbst_rest"], top))
        if not want:
            continue
        lo, hi = min(want), max(want)
        have = [k.co.x for k in fc.keyframe_points]
        look = {"ty": GEN_KEY, "ht": ('AUTO_CLAMPED', 'AUTO_CLAMPED')}
        for pass_ in range(2):                      # every other frame, then single frames wherever it still dips
            frames = (sorted(set(range(lo, hi + 1, 2)) | {hi}) if pass_ == 0 else
                      [f for f in range(lo, hi + 1) if legs_clearance(g, pose(f))[0] < -PLANT_EPS])
            new = []
            for f in frames:
                if not s < f < e or any(abs(x - f) < 0.5 for x in have):
                    continue
                p = pose(f)
                gap, top = legs_clearance(g, p)
                v = max(0.0, min(p["bbst_rest"], top)) if (gap < -PLANT_EPS * 0.5 and top is not None) else p["bbst_rest"]
                new.append((f, v, look))
            if not new:
                continue
            _add_keys(fc, new)                      # exactly there: insert() merges keys within 0.01 frame
            have += [p[0] for p in new]
            added += len(new)
            _smooth_inside(fc, s, e)
    return added


def _smooth_inside(fc, s, e):
    """Smooth handles through the keys inside a move (auto clamped: flat at the ends of the move, where the value
    stops); the keys on the move's own ends keep theirs, only no longer reaching past their new neighbours."""
    pts = sorted(fc.keyframe_points, key=lambda k: k.co.x)
    for kp in pts:
        if s < kp.co.x < e and kp.type == GEN_KEY:        # a key made by hand keeps its handles
            kp.handle_left_type = kp.handle_right_type = 'AUTO_CLAMPED'
    for j, kp in enumerate(pts):
        if not (abs(kp.co.x - s) < 0.5 or abs(kp.co.x - e) < 0.5) or kp.handle_left_type == 'AUTO_CLAMPED':
            continue
        if j and kp.co.x - kp.handle_left.x > (kp.co.x - pts[j - 1].co.x) / 3.0 + 1e-6:
            t = (kp.co.x - pts[j - 1].co.x) / 3.0 / max(1e-6, kp.co.x - kp.handle_left.x)
            kp.handle_left = (kp.co.x - (kp.co.x - kp.handle_left.x) * t, kp.co.y + (kp.handle_left.y - kp.co.y) * t)
        if j < len(pts) - 1 and kp.handle_right.x - kp.co.x > (pts[j + 1].co.x - kp.co.x) / 3.0 + 1e-6:
            t = (pts[j + 1].co.x - kp.co.x) / 3.0 / max(1e-6, kp.handle_right.x - kp.co.x)
            kp.handle_right = (kp.co.x + (kp.handle_right.x - kp.co.x) * t, kp.co.y + (kp.handle_right.y - kp.co.y) * t)
    _settle_curve(fc)


def reset_pose_to_keys(ob, frame):
    """Back to the pose the beats hold on this frame. True when something changed."""
    moved = False
    for fc in id_fcurves(ob):
        prop = POSE_PATHS.get(fc.data_path)
        if prop is None:
            continue
        v = fc.evaluate(frame)
        if abs(float(ob.get(prop, v)) - v) > 1e-6:
            ob[prop] = v
            moved = True
    if moved:
        ob.update_tag(refresh={'OBJECT', 'DATA'})
    return moved


def build_boundary_object(label, w, d, h, reuse=None):
    """Wire box marking the studio working space. reuse: this staging's own studio space, reshaped in place. Without
    it the box is always a NEW object: one that merely carries the name "Studio Space · <label>" can belong to another
    staging (B11, audit r3: after a rename, New Staging with the old name took that staging's space and moved it)."""
    name = f"Studio Space · {label}"
    if reuse is not None and reuse.type == 'MESH' and reuse.data is not None and reuse.data.users == 1:
        me = reuse.data
    else:
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
    if reuse is not None and reuse.type == 'MESH':
        ob = reuse
        if ob.data != me:
            ob.data = me            # it shared its mesh with another staging's space: it gets its own
    else:
        ob = bpy.data.objects.new(unique_object_name(name), me)
    ob[ROLE_KEY] = "boundary"
    ob.display_type = 'WIRE'
    ob.hide_render = True
    ob.color = (0.2, 0.8, 0.9, 1.0)
    return ob


# ------------------------------------------------------------------ view layer + ghost

def normalize_view_layer(scene):
    """Stage Mode owns visibility through per-pane local view, so the staging's view layer
    itself must show everything: un-exclude, un-hide (outliner eye) and un-H every object of
    the staging. Repairs files damaged by v0.7 (global isolate) and by careless hiding. The set edits'
    wrappers are this staging's own exclusions (0.19): exclude_set_edits keeps them."""
    if not is_staging(scene):
        return
    roots = [c for k in ("SET", "STUDIO", "STAGE") for c in layer_colls(scene, k)]
    for vl in scene.view_layers:
        for root in roots:
            lc = find_layer_collection(vl.layer_collection, root)
            stack = [lc] if lc is not None else []
            while stack:
                x = stack.pop()
                if x.exclude and x.collection.get(SETEDIT_KEY) is None:
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
    exclude_set_edits(scene)


def ghost_tint(scene, on):
    """Fade the SET to translucent grey via object-colour alpha. Only panes in solid shading
    with OBJECT colour show it, so camera panes stay clean. Undone before every save."""
    obs = [ob for coll in layer_colls(scene, "SET") for ob in coll_objects(coll)] + instanced_objects(scene)
    for ob in obs:
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


def _shell_update(self, context):
    scene = self.id_data if isinstance(getattr(self, "id_data", None), bpy.types.Scene) else context.scene
    if is_staging(scene) and not _QUIET["floor"]:
        build_studio_shell(scene)
        request_sync(0.0)


def _studio_dims_update(self, context):
    scene = self.id_data if isinstance(getattr(self, "id_data", None), bpy.types.Scene) else context.scene
    if is_staging(scene) and not _QUIET["dims"]:
        rebuild_studio(scene)


def resize_studio(scene, w, d, cx, cy, shell=True):
    """New width/depth and centre in one step (a resize handle keeps the opposite side put).
    What stands in the studio stays where it is: this is not a move. shell=False (while a
    handle is dragged) reshapes only the wire box; the floor and walls follow on release."""
    st = scene.bb_st
    b = boundary_of(scene)
    if b is None:
        return
    _QUIET["dims"] = True
    try:
        st.studio_w = min(60.0, max(2.0, w))
        st.studio_d = min(60.0, max(2.0, d))
    finally:
        _QUIET["dims"] = False
    b.location.x, b.location.y = cx, cy
    st.bound_xy = (cx, cy)
    st.bound_xy_set = True
    rebuild_studio(scene, shell)


def rebuild_studio(scene, shell=True):
    st = scene.bb_st
    studio = layer_colls(scene, "STUDIO")
    if not studio:
        return
    old = boundary_of(scene)
    loc = old.location.copy() if old is not None else None
    rot_z = old.rotation_euler.z if old is not None else 0.0
    own = old if (old is not None and studio_owns(scene, old)) else None
    label = staging_label(scene)
    new = build_boundary_object(label, st.studio_w, st.studio_d, st.studio_h, reuse=own)
    if old is not None and old != new:
        # the space was another staging's too (B4, B11): it stays theirs, this staging takes its own
        for c in layer_colls(scene, "STUDIO"):
            for cc in [c] + list(c.children_recursive):
                if cc.objects.get(old.name) == old:
                    cc.objects.unlink(old)
    want = f"Studio Space · {label}"
    if new.name != want and bpy.data.objects.get(want) is None and not shared_with(scene):
        new.name = want                 # a renamed staging's space follows its name, when the name is free
    if studio[0].objects.get(new.name) is None:
        studio[0].objects.link(new)
    if loc is not None:
        new.location = loc
    new.rotation_euler.z = rot_z
    st.boundary = new
    if shell:
        build_studio_shell(scene)
        request_sync()


# ------------------------------------------------------------------ beats

def fps(scene):
    return scene.render.fps / scene.render.fps_base


# Beat markers (0.19): the add-on owns exactly the markers it made, one per beat, recorded by beat id in
# st.beat_marks ({uid: [name, frame]}). Until 0.18 any marker called B + digits was taken for a beat marker and
# deleted when it matched no beat (audit r1 bug 10: a marker of yours called "B7" or "B12 insert" vanished), and
# Insert Beat handed a beat's marker — and the camera cut on it — to the beat that took its number.

def _beat_marks(st):
    """{beat uid: (marker name, frame)} of the markers the add-on owns; None when this staging was never synced
    by 0.19 (its beat markers are found by their B<n> names, once)."""
    if not st.beat_marks:
        return None
    try:
        return {int(k): (str(v[0]), int(v[1])) for k, v in json.loads(st.beat_marks).items()}
    except Exception:
        return {}


def _store_beat_marks(st, marks):
    text = json.dumps({str(k): [n, int(f)] for k, (n, f) in sorted(marks.items())}, ensure_ascii=False)
    if st.beat_marks != text:
        st.beat_marks = text


def _legacy_beat_marker(scene, i, frame, taken=()):
    """A beat marker as 0.18 and earlier found it: named B<i+1> or "B<i+1> label", the one on its beat first."""
    name = f"B{i + 1}"
    hits = [m for m in scene.timeline_markers if (m.name == name or m.name.startswith(name + " "))
            and m.as_pointer() not in taken]
    return next((m for m in hits if m.frame == frame), hits[0] if hits else None)


def _owned_marker(scene, rec, taken=()):
    """The marker of this record: same name on the same frame; else (dragged in the timeline) the one by that name."""
    name, frame = rec
    hits = [m for m in scene.timeline_markers if m.name == name and m.as_pointer() not in taken]
    return next((m for m in hits if m.frame == frame), hits[0] if hits else None)


def beat_marker(scene, i):
    """The marker of beat i (None when it has none)."""
    st = scene.bb_st
    if not (0 <= i < len(st.beats)):
        return None
    b = st.beats[i]
    marks = _beat_marks(st)
    if marks is None:
        return _legacy_beat_marker(scene, i, b.frame)
    rec = marks.get(b.uid)
    return _owned_marker(scene, rec) if rec is not None else None


def claim_beat_markers(scene):
    """Record the beat markers of a staging made before 0.19 as the add-on's own (nothing is moved or renamed)."""
    st = scene.bb_st
    marks, taken = {}, set()
    for i, b in enumerate(st.beats):
        m = _legacy_beat_marker(scene, i, b.frame, taken)
        if m is not None:
            taken.add(m.as_pointer())
            marks[b.uid] = (m.name, m.frame)
    _store_beat_marks(st, marks)


def _retire_beat_marker(scene, m):
    """The beat of this marker is gone. A camera cut bound to it stays, as a cut marker of its own (audit r4 M4:
    Delete Beat used to delete the cut too); otherwise the marker goes."""
    if m.camera is not None:
        m.name = f"{CUT_PREFIX}{m.camera.name}"
    else:
        scene.timeline_markers.remove(m)


def sync_markers(scene):
    """One marker per beat, named B<n> and its label, on its beat. Only the markers the add-on made are touched:
    a marker of yours is never renamed, moved or deleted, whatever it is called (Aman's 0.19 brief)."""
    st = scene.bb_st
    old = _beat_marks(st)
    legacy = old is None
    old = old or {}
    marks, taken = {}, set()
    for i, b in enumerate(st.beats):
        name = f"B{i + 1}" + (f" {b.label}" if b.label else "")
        rec = old.get(b.uid)
        m = None
        if rec is not None:
            m = _owned_marker(scene, rec, taken)
            if m is None:                        # renamed by hand in the timeline, still on its beat
                m = next((x for x in scene.timeline_markers if x.as_pointer() not in taken and x.frame == rec[1]
                          and x.name.split(" ", 1)[0] == rec[0].split(" ", 1)[0]), None)
        elif legacy:
            m = _legacy_beat_marker(scene, i, b.frame, taken)
        if m is None:
            m = scene.timeline_markers.new(name, frame=b.frame)
        if m.name != name:
            m.name = name
        if m.frame != b.frame:
            m.frame = b.frame
        taken.add(m.as_pointer())
        marks[b.uid] = (m.name, m.frame)        # the name Blender kept (it cuts long labels)
    for uid, rec in old.items():
        if uid not in marks:                    # a deleted beat: its marker goes (a cut on it stays)
            m = _owned_marker(scene, rec, taken)
            if m is not None:
                _retire_beat_marker(scene, m)
    _store_beat_marks(st, marks)


def keyed_objects(scene):
    """Everything the beats key: characters, props, the aim and eyes helpers, and every camera except the
    ones switched to Static. Cameras are keyed by default (Aman, 13 Oct 2026: "make the camera keyframeable
    by default and not by pushing a button") — a camera that never moves costs one key, because a pose is
    only keyed where it changes."""
    obs = stage_objects(scene, roles=("char", "prop", EYES_ROLE, AIM_ROLE))
    obs += [c for c in stage_cams(scene) if cam_moves(c)]
    return obs


def cam_moves(ob):
    return bool(ob is not None and not ob.get(STATIC_KEY))


def cam_travels(cam):
    """True when the camera's own beat keys really go somewhere (not one pose held on every beat)."""
    for fc in id_fcurves(cam):
        if fc.data_path in _BLOCK_PATHS and len(fc.keyframe_points) > 1:
            ys = [k.co.y for k in fc.keyframe_points]
            if max(ys) - min(ys) > 1e-4:
                return True
    return any(r.owner == cam for s in stagings() for r in s.bb_st.paths) if cam is not None else False


def set_cam_moves(scene, cam, on):
    """On: the camera takes part in the beats, keyed where it moves (the default). Off — Static: its beat
    keys and paths go and it stays where it is now, untouched by anything.

    0.19: On re-keys this camera only (it holds one pose on every beat, so nobody's timing changes). It used to
    re-key the whole staging, which threw away whatever somebody had dragged on the beat and not saved."""
    st = scene.bb_st
    if on:
        if STATIC_KEY in cam:
            del cam[STATIC_KEY]
        cam[CAM_KEY] = True                  # 0.17 and earlier read this; harmless to keep writing it
        if not block_channels(cam) and len(st.beats):
            f0 = st.beats[_clamped_beat(st)].frame
            cam.keyframe_insert("location", frame=f0, group="BB Stage")
            cam.keyframe_insert("rotation_euler", frame=f0, group="BB Stage")
        if len(st.beats) and not _QUIET["beats"]:
            relayout_only(scene, [cam])
        return
    cam[STATIC_KEY] = True
    for k in reversed(range(len(st.paths))):
        if st.paths[k].owner == cam:
            remove_path(scene, k)
    loc, rot = cam.location.copy(), cam.rotation_euler.copy()
    _drop_fcurves(cam, {"location", "rotation_euler"})
    cam.location, cam.rotation_euler = loc, rot
    set_zoom(scene, cam, False)
    for k in reversed(range(len(st.moves))):
        if st.moves[k].owner == cam:
            st.moves.remove(k)
    if MOVE_KEY in cam:
        del cam[MOVE_KEY]
    if CAM_KEY in cam:
        del cam[CAM_KEY]


def beat_out(b):
    return max(b.frame, b.frame_out)


def id_fcurves(idb):
    """The F-curves that animate this data-block: its own slot of its action (an object and its camera
    data can share one action since Blender 4.4)."""
    ad = getattr(idb, "animation_data", None)
    act = ad.action if ad is not None else None
    if act is None:
        return []
    handle = getattr(getattr(ad, "action_slot", None), "handle", None)
    out = []
    for layer in act.layers:
        for strip in layer.strips:
            for cb in strip.channelbags:
                if handle is None or getattr(cb, "slot_handle", handle) == handle:
                    out.extend(cb.fcurves)
    return out


_BLOCK_PATHS = ("location", "rotation_euler")
LENS_CH = ("lens", 0)              # a zooming camera: its lens is part of the beat pose
MOVE_KEY = "bb_st_moves"           # on keyed objects: {beat uid: [first, last frame]} it really moves in (Natural moves)
try:
    _KEY_TYPES = {i.identifier for i in bpy.types.Keyframe.bl_rna.properties["type"].enum_items}
except Exception:
    _KEY_TYPES = set()
GEN_KEY = 'GENERATED' if 'GENERATED' in _KEY_TYPES else 'BREAKDOWN'     # the in-between keys the layout derives
_CARRY = {}                         # sample_beat_poses → write_beat_layout: where the beats were, the hand-made keys


def lens_fcurve(cam):
    """The lens curve of a camera that zooms on the beats (None: its lens is one fixed value)."""
    if cam is None or cam.type != 'CAMERA' or cam.data is None:
        return None
    return next((fc for fc in id_fcurves(cam.data) if fc.data_path == "lens"), None)


def block_channels(ob):
    """{(path, index): F-curve} of everything a beat poses on this object: where it stands, how it is
    turned, for a character that sits or lies its pose (0.19: hip, knee, lie back, seat height, resting)
    and, for a camera that zooms, its lens."""
    out = {}
    for fc in id_fcurves(ob):
        if fc.data_path in _BLOCK_PATHS or fc.data_path in POSE_PATHS:
            out[(fc.data_path, fc.array_index)] = fc
    fc = lens_fcurve(ob)
    if fc is not None:
        out[LENS_CH] = fc
    return out


def current_pose(ob, chans):
    """Where this object is standing right now, on the channels the beats hold."""
    out = {}
    for key in chans:
        path, idx = key
        if key == LENS_CH:
            out[key] = float(ob.data.lens)
        elif path in POSE_PATHS:
            prop = POSE_PATHS[path]
            out[key] = float(ob.get(prop, POSE_NEUTRAL[prop]))
        else:
            out[key] = float(getattr(ob, path)[idx])
    return out


UNSAVED_EPS = 1e-4         # further than this off its keys and an object counts as moved


def off_key_channels(ob, frame):
    """The channels on which this object stands off its keys at this frame (an unsaved move): {(path, index): its
    value now}. Only a channel that has keys can be off them: one with no keys stands wherever it was put on every
    beat, and no jump, scrub or save can take that away — so something never keyed (an aim point made by a script
    or by Looks at after the last save, a character just added) is no unsaved move (adversarial review of 0.19:
    every Gossip Maze beat lit orange with nothing moved, and the next click keyed the aims behind your back).
    A turn of a whole number of turns is the same pose and is no move."""
    chans = block_channels(ob)
    out = {}
    if not chans:
        return out
    cur = current_pose(ob, chans)
    for key, fc in chans.items():
        d = cur[key] - fc.evaluate(frame)
        if key[0] == "rotation_euler":
            d = _wrap(d)
        if abs(d) > UNSAVED_EPS:
            out[key] = cur[key]
    return out


def _off_keys(ob, frame):
    """True when this object no longer stands where its beat keys put it on this frame (an unsaved move)."""
    return bool(off_key_channels(ob, frame))


def _sid(idb):
    """A data-block's id for this session: it stays the same through a rename (the Cast list's name field, a camera
    renamed with its helpers), where a name would lose track of an unsaved move (adversarial review of 0.19).
    A depsgraph update hands over the evaluated copy, whose own session id is 0: the original's is the one."""
    return idb.original.session_uid


# The unsaved state of a staging (0.19). _TOUCHED holds, per staging, the keyed objects that stand off their keys
# at the playhead; the depsgraph handler keeps it up to date for what the user moves, and settle_unsaved() works
# it out from scratch after a frame change, a save or a load. The flags shown in the panel follow from it: the
# beat under the playhead is orange (dirty) when anything is off its keys there, and a staging whose playhead is
# between two beats says so (unsaved_between) — a move made there used to be lost without a word.
_TOUCHED = {}               # staging's session id: {session ids of the objects off their keys}


def _apply_unsaved(scene):
    st = scene.bb_st
    live = {_sid(ob) for ob in keyed_objects(scene)}
    touched = _TOUCHED.get(_sid(scene), set()) & live
    _TOUCHED[_sid(scene)] = touched
    i = beat_at_frame(scene) if len(st.beats) else None
    for j, b in enumerate(st.beats):
        want = bool(touched) and j == i
        if b.dirty != want:
            b.dirty = want
    between = bool(touched) and i is None and len(st.beats) > 0
    if st.unsaved_between != between:
        st.unsaved_between = between


def settle_unsaved(scene):
    """Work out again which keyed objects stand off their keys at the playhead, and set the badges from that."""
    if not is_staging(scene):
        return
    f = scene.frame_current
    _TOUCHED[_sid(scene)] = {_sid(ob) for ob in keyed_objects(scene) if _off_keys(ob, f)}
    _apply_unsaved(scene)


def forget_unsaved(scene):
    """No unsaved move any more (a file was just loaded: the keys were read over whatever the file held)."""
    _TOUCHED.pop(_sid(scene), None)
    st = scene.bb_st
    for b in st.beats:
        if b.dirty:
            b.dirty = False
    if st.unsaved_between:
        st.unsaved_between = False


def has_unsaved(scene):
    st = scene.bb_st
    return bool(_TOUCHED.get(_sid(scene))) or st.unsaved_between or any(b.dirty for b in st.beats)


def save_unsaved(scene):
    """Something is about to re-read the keys (a jump, a retime, a camera cut, a rebuild, Play, a file save): an
    unsaved move on the beat under the playhead goes into that beat first, never thrown away (Aman's rule since
    0.15; audit r4 H1 found six controls that dropped it). Only the objects that were moved are written. Between
    two beats nothing is written — there is no beat to put it in; the Beats panel says so, and a file save keeps it
    in the file instead (stash_between). Returns True when it saved."""
    if _QUIET["saving"] or not is_staging(scene) or not len(scene.bb_st.beats):
        return False
    st = scene.bb_st
    i = beat_at_frame(scene)
    touched = _TOUCHED.get(_sid(scene))
    if i is None or not (touched or st.beats[i].dirty):
        return False
    save_beat(scene, i, only=set(touched) if touched else None)
    return True


BETWEEN_KEY = "bb_st_between"     # on a staging scene: a move made between two beats, kept by a file save (JSON)


def stash_between(scene):
    """Ctrl+S with a move made between two beats: there is no beat to save it into, and the file would hold the
    objects off their keys, which opening it reads over — the move went without a word (adversarial review of 0.19).
    It goes into the file instead, as it stands, and opening the file puts it back (unstash_between), still marked
    "Moved between two beats". Only the staging in a window: one you are not looking at is read again from its keys
    when you go to it anyway."""
    st = scene.bb_st
    keep = {}
    if (len(st.beats) and beat_at_frame(scene) is None and _TOUCHED.get(_sid(scene))
            and scene in {w.scene for w in bpy.context.window_manager.windows}):
        f = scene.frame_current
        for ob in keyed_objects(scene):
            if _sid(ob) in _TOUCHED[_sid(scene)]:
                off = off_key_channels(ob, f)
                if off:
                    keep[ob.name] = {f"{p}|{k}": v for (p, k), v in off.items()}
    if keep:
        scene[BETWEEN_KEY] = json.dumps({"frame": scene.frame_current, "poses": keep}, ensure_ascii=False)
        print(f"BB Stage: {scene.name}: a move made between two beats is kept in the file (no beat holds it yet)")
    elif BETWEEN_KEY in scene:
        del scene[BETWEEN_KEY]


def unstash_between(scene):
    """After a load: put a move that a save kept between two beats back where it was (see stash_between)."""
    text = scene.get(BETWEEN_KEY)
    if text is None:
        return 0
    del scene[BETWEEN_KEY]
    try:
        rec = json.loads(text)
    except Exception:
        return 0
    if (int(rec.get("frame", -1)) != scene.frame_current or not len(scene.bb_st.beats)
            or beat_at_frame(scene) is not None):
        return 0                        # the playhead or the beats moved since (an older add-on saved over it)
    n = 0
    for name, chans in rec.get("poses", {}).items():
        ob = bpy.data.objects.get(name)
        if ob is None or ob not in keyed_objects(scene):
            continue
        for key, v in chans.items():
            path, k = key.split("|")
            if (path, int(k)) == LENS_CH:
                if ob.type == 'CAMERA' and ob.data is not None:
                    ob.data.lens = float(v)
            elif path in _BLOCK_PATHS:
                getattr(ob, path)[int(k)] = float(v)
            elif path in POSE_PATHS:
                ob[POSE_PATHS[path]] = float(v)
        n += 1
    settle_unsaved(scene)
    return n


def pin_beat_keys(scene, fc):
    """Before code edits ONE beat's key on this curve: give every beat that has no key here one at the value it
    holds now. Since 0.18 a hold carries no key inside it, so a key changed on one beat bent the curve back through
    every key-less hold before it (fuzz bug C: Add Path's arrival heading turned a prop 67° across three holds,
    a lens set on B3 changed B2). The next rebuild takes the extra keys away again where nothing moves."""
    if fc is None:
        return
    st = scene.bb_st
    have = sorted(kp.co.x for kp in fc.keyframe_points)
    want = sorted({float(f) for b in st.beats for f in (b.frame, beat_out(b))})
    pts = [(f, fc.evaluate(f)) for f in want if not _on_mark(f, have)]
    _add_keys(fc, pts)


def _snap_to_keys(scene):
    """Everybody onto the keys at the playhead — what Blender does on its next update anyway; doing it now keeps
    the rotations' numbers (unwound the short way round) and the badges right without waiting for a redraw."""
    f = scene.frame_current
    for ob in keyed_objects(scene):
        chans = block_channels(ob)
        for key, fc in chans.items():
            v = fc.evaluate(f)
            if key == LENS_CH:
                if abs(ob.data.lens - v) > 1e-6:
                    ob.data.lens = v
                continue
            if key[0] in POSE_PATHS:            # a character's pose (s3): a custom property, not an attribute
                prop = POSE_PATHS[key[0]]
                if abs(float(ob.get(prop, v)) - v) > 1e-6:
                    ob[prop] = v
                continue
            prop = getattr(ob, key[0])
            if abs(prop[key[1]] - v) > 1e-6:
                prop[key[1]] = v


def save_beat(scene, index, only=None, every=False):
    """Save what changed onto this beat. An object counts as changed when it no longer stands where its keys put
    it at the playhead, so a Save writes only the objects you moved — never everybody's in-between pose when the
    playhead is between beats (Aman, 15 Oct 2026; audit G / r1 bug 1). only: the session ids of the objects to look
    at (an auto-save writes what was touched); every: take everybody's pose as it stands (Insert Beat).
    What a moved object writes is the pose you see. On the beat under the playhead that is the channels you moved
    (the others already hold it, and a hand key bending the hold stays out of them). Into another beat — Save Beat
    between two beats goes into the highlighted one, Add Beat into a new one — it is the object's whole pose as it
    stands: moving one channel and taking the rest from that other beat made a pose nobody placed, sometimes moved
    against the drag (adversarial review of 0.19).
    A pose that changed carries on through the beats that were holding the old one, so moving something inside a
    hold moves the whole hold — instead of the old behaviour, where the next beat still held the old pose and
    pulled it straight back (Aman, 13 Oct 2026). Returns how many objects changed."""
    st = scene.bb_st
    b = st.beats[index]
    _QUIET["saving"] = True
    try:
        sync_peg_colors(scene)
        now = scene.frame_current
        here = beat_at_frame(scene) == index        # the beat you are looking at
        obs = keyed_objects(scene)
        changed = {}                                # name: the channels to write (None: all of them)
        for ob in obs:
            if only is not None and _sid(ob) not in only:
                continue
            off = off_key_channels(ob, now)
            if every or (off and not here):
                changed[ob.name] = None
            elif off:
                changed[ob.name] = set(off)
        frames = sorted({b.frame, beat_out(b)})
        for ob in obs:                              # anything not keyed yet gets its curves here, where it stands
            have = block_channels(ob)
            if only is not None and _sid(ob) not in only and not have:
                continue                            # an auto-save keys nothing you did not touch (a script's aim)
            posed = is_peg(ob) and any(abs(float(ob.get(p, v)) - v) > 1e-7 for p, v in POSE_NEUTRAL.items())
            if posed and any(k[0] in _BLOCK_PATHS for k in have):
                ensure_pose_curves(scene, ob)       # its first pose: it stood on the beats before (s3, 0.19)
            fresh = not have
            for path in _BLOCK_PATHS:               # every channel: a camera given Zoom first had only its lens
                for k in range(3):
                    if (path, k) not in have:
                        for f in frames:
                            ob.keyframe_insert(path, index=k, frame=f, group="BB Stage")
            if posed and fresh:                     # a new character holds the pose it has now, like its place
                for path in POSE_PATHS:
                    for f in frames:
                        ob.keyframe_insert(path, frame=f, group="BB Stage")
        poses = sample_beat_poses(scene)            # what the beats hold at this moment, before the save
        n = len(st.beats)
        for ob in obs:
            if ob.name not in changed:
                continue
            rows = poses.get(ob.name)
            chans = block_channels(ob)
            if rows is None or not chans:
                continue
            keys = changed[ob.name]
            stops = fill_stops(scene, ob)       # an aim point never fills into beats where it means something else
            for key, v in current_pose(ob, chans).items():
                if keys is not None and key not in keys:
                    continue
                old = rows[index].get(key)
                if old is not None:
                    d = _wrap(v - old) if key[0] == "rotation_euler" else v - old
                    if abs(d) <= KEY_EPS:
                        continue
                rows[index][key] = v
                for j in range(index + 1, n):       # the rest of the hold comes along
                    if old is None or abs(rows[j].get(key, old) - old) > KEY_EPS or j in stops:
                        break
                    rows[j][key] = v
        write_beat_layout(scene, poses)
        if st.alive > 0.0:
            apply_alive(scene)              # a character added since the last save comes alive too
        apply_eyes(scene)                   # a POV camera keeps the pose its eyes have on this beat
        _snap_to_keys(scene)
    finally:
        _QUIET["saving"] = False
    b.dirty = False
    settle_unsaved(scene)
    return len(changed)


def beat_layout(scene, start=None):
    """(arrive, leave) frames for every beat from its Move and Hold times."""
    st = scene.bb_st
    f = fps(scene)
    out = []
    if start is None:       # a staging that starts on frame 0 stays there (audit r1 bug 17: `start or 1`)
        t = st.beats[0].frame if len(st.beats) else 1
    else:
        t = start
    for i, b in enumerate(st.beats):
        if i:
            t = out[-1][1] + max(1, round(b.move_s * f))    # a 0 s move is a cut on the next frame
        out.append((t, t + max(0, round(b.hold_s * f))))
    return out


def _beat_values(st, fc):
    """What this curve holds on every beat. A beat with no key of its own on the curve sits inside a hold (0.18
    keys only where things move): when the keyed beats either side of it hold the same value, that value is its
    pose — the curve itself may bend there round a key made by hand between beats, and reading the bend would bake
    it into the beat on the next save (audit r1 bug 2)."""
    beats = list(st.beats)
    xs = sorted(kp.co.x for kp in fc.keyframe_points)
    vals = [fc.evaluate(b.frame) for b in beats]
    keyed = [i for i, b in enumerate(beats) if _on_mark(b.frame, xs) or _on_mark(beat_out(b), xs)]
    if len(keyed) < 2 or len(keyed) == len(beats):
        return vals
    import bisect
    for i in range(len(beats)):
        j = bisect.bisect_left(keyed, i)
        if j < len(keyed) and keyed[j] == i:
            continue
        if 0 < j < len(keyed) and abs(vals[keyed[j - 1]] - vals[keyed[j]]) <= KEY_EPS:
            vals[i] = vals[keyed[j - 1]]
    return vals


def sample_beat_poses(scene):
    """Every keyed object's pose on every beat: {object name: [{(path, index): value}, ...]}. It also
    notes, for the layout that follows, where the beats are now and which keys somebody made by hand
    between them, so a retime can take those along."""
    st = scene.bb_st
    poses, hand = {}, {}
    marks = sorted({int(f) for b in st.beats for f in (b.frame, beat_out(b))})
    for ob in keyed_objects(scene):
        chans = block_channels(ob)
        if not chans:
            continue                # never keyed: it stands where it is on every beat until a Save Beat keys it
        if len(st.beats) and not all((p, k) in chans for p in _BLOCK_PATHS for k in range(3)):
            for p in _BLOCK_PATHS:  # partly keyed (a camera given Zoom first had only its lens): the rest is keyed
                for k in range(3):  # where it stands, so the beats hold a whole pose (fuzz bug M)
                    if (p, k) not in chans:
                        ob.keyframe_insert(p, index=k, frame=st.beats[0].frame, group="BB Stage")
            chans = block_channels(ob)
        poses[ob.name] = rows = [{} for _b in st.beats]
        for key, fc in chans.items():
            for i, v in enumerate(_beat_values(st, fc)):
                rows[i][key] = v
        for key, fc in chans.items():
            # a key off the beat frames is hand-made — sub-frame ones too (a retime keeps keys where they fall)
            mine = [(kp.co.x, kp.co.y, _key_look(kp)) for kp in fc.keyframe_points
                    if kp.type != GEN_KEY and not _on_mark(kp.co.x, marks)]
            if mine:
                hand[(ob.name, key)] = mine
    _CARRY.clear()
    _CARRY.update(scene=scene.name, old={b.uid: (b.frame, beat_out(b)) for b in st.beats}, hand=hand)
    return poses


# ------------------------------------------------------------------ a retime carries everything (0.16)
#
# Until 0.15 a change of a Move or Hold time re-timed the blocking and the beat markers only: camera cuts,
# lens and scale keys, crowd cues and whatever else was timed against the beats stayed behind. Now every
# key and marker of the staging rides along: what sat on a beat stays on that beat, what sat between two
# beats keeps its place between them.

MARK_EPS = 1e-3            # frames: a key this close to a beat frame is that beat's own key
HELD_KEY = "bb_st_held"    # on a data-block: keys parked while the hold they sat in has no time (JSON)


def _on_mark(x, marks):
    """True when frame x sits on one of the beat frames (marks: sorted)."""
    import bisect
    j = bisect.bisect_left(marks, x - MARK_EPS)
    return j < len(marks) and abs(marks[j] - x) <= MARK_EPS


class _Retime:
    """Takes a frame of the old beat layout to the new one. What sat on a beat stays on that beat (its arrival, when
    it now holds); what sat inside a move or a hold keeps its fraction of it, to the sub-frame. Until 0.18 every key
    and marker was rounded to a whole frame and keys that met were merged, so a span shrunk and grown back lost
    its cuts, hand keys and baked keys, and small steps drifted (audit r1 bug 3, Aman's 0.19 brief: a retime must
    never destroy them). A move always keeps at least a frame; a hold can shrink to nothing, and then held() names
    that hold and the fraction, so the caller parks what sat inside and puts it back when the hold has time again."""

    def __init__(self, anchors, new):
        self.a = anchors                    # [(uid, old arrive, old leave, new arrive, new leave)], in order
        self.oa = [a[1] for a in anchors]
        self.new = new                      # the whole new layout {uid: (arrive, leave)}

    def _locate(self, x):
        import bisect
        A = self.a
        if x < A[0][1]:
            return 'before', 0, 0.0
        if x > A[-1][2]:
            return 'after', len(A) - 1, 0.0
        k = max(0, bisect.bisect_right(self.oa, x) - 1)
        _uid, oa, ol, _na, _nl = A[k]
        if x <= ol:
            return 'hold', k, (0.0 if ol <= oa else (x - oa) / (ol - oa))
        return 'move', k, (x - ol) / (A[k + 1][1] - ol)

    def __call__(self, x):
        kind, k, t = self._locate(x)
        A = self.a
        if kind == 'before':
            return x + (A[0][3] - A[0][1])
        if kind == 'after':
            return x + (A[-1][4] - A[-1][2])
        _uid, _oa, _ol, na, nl = A[k]
        if kind == 'hold':
            return na + t * (nl - na)
        return nl + t * (A[k + 1][3] - nl)

    def held(self, x, moves=False):
        """Where x sat when the span it sat in has no room for it any more: (beat uid, fraction, kind, old length);
        else None. 'hold': inside a hold that now has no time, or on its last frame — that frame is the arrival now,
        so a key there landed on the arrival key and a cut on the arrival, and neither found its way back when the
        hold did (adversarial review of 0.19). 'move' (moves=True, for keys): strictly inside a move squeezed to
        its one-frame minimum (a 0 s move is a cut): keys baked every frame there met within a hundredth of a
        frame, which Blender merges. The uid of a move is the beat it leads into."""
        kind, k, t = self._locate(x)
        A = self.a
        if kind == 'hold':
            if t > 1e-9 and A[k][4] <= A[k][3] and A[k][2] > A[k][1]:
                return A[k][0], t, 'hold', A[k][2] - A[k][1]
        elif kind == 'move' and moves and 1e-9 < t < 1.0 - 1e-9:
            old, new = A[k + 1][1] - A[k][2], A[k + 1][3] - A[k][4]
            if new <= 1.0 + 1e-9 and old > new + 1e-9:
                return A[k + 1][0], t, 'move', old
        return None


def time_map(old, new):
    """A function that takes a frame of the old beat layout to the new one (a _Retime), or None when nothing moved.
    old, new: {beat uid: (arrive, leave)}."""
    anchors = []
    for uid, (oa, ol) in sorted(((u, ad) for u, ad in old.items() if u in new), key=lambda t: (t[1][0], t[1][1])):
        na, nl = new[uid]
        if anchors and (na <= anchors[-1][4] or oa <= anchors[-1][2]):
            continue                # a beat that changed its place in the order (Insert Beat) is no anchor
        anchors.append((uid, oa, ol, na, nl))
    if not anchors or all(oa == na and ol == nl for _u, oa, ol, na, nl in anchors):
        return None
    return _Retime(anchors, dict(new))


def _held(idb):
    try:
        return {str(k): [list(x) for x in v] for k, v in json.loads(idb.get(HELD_KEY, "{}")).items()}
    except Exception:
        return {}


def _store_held(idb, held):
    held = {k: v for k, v in held.items() if v}
    if held:
        text = json.dumps(held)
        if idb.get(HELD_KEY) != text:
            idb[HELD_KEY] = text
    elif HELD_KEY in idb:
        del idb[HELD_KEY]


_AUTO_HANDLES = ('AUTO', 'AUTO_CLAMPED', 'VECTOR')     # handles Blender works out itself


def _key_look(kp):
    """What a key is besides where it is — its interpolation, handles, easing and type — when that is not the
    default a re-added key gets (Bezier, auto-clamped, a plain keyframe): None, or a small dict. A parked or
    re-timed key comes back as it was (a baked rig's linear keys stay linear)."""
    look = {}
    if kp.interpolation != 'BEZIER':
        look["i"] = kp.interpolation
    if kp.easing != 'AUTO':
        look["e"] = kp.easing
    if kp.type != 'KEYFRAME':
        look["ty"] = kp.type
    lt, rt = kp.handle_left_type, kp.handle_right_type
    if (lt, rt) != ('AUTO_CLAMPED', 'AUTO_CLAMPED'):
        look["ht"] = [lt, rt]
        if lt not in _AUTO_HANDLES or rt not in _AUTO_HANDLES:
            x, y = kp.co
            look["h"] = [kp.handle_left.x - x, kp.handle_left.y - y, kp.handle_right.x - x, kp.handle_right.y - y]
    return look or None


def _park_rec(h, y, look):
    """A parked key: [uid, fraction, value] (0.19 first form, a hold), or with a fourth item {look, "m": 1 for a
    move, "sp": the span's length then, which scales its free handles when it comes back}."""
    uid, t, kind, span = h
    look = dict(look or {})
    if kind == 'move':
        look["m"] = 1
    if "h" in look:
        look["sp"] = float(span)
    return [int(uid), float(t), float(y)] + ([look] if look else [])


def _unpark(entries, layout):
    """Parked keys whose span has room again: [(frame, value, look)], and the ones still parked. A hold has room
    when it has time; a move when it has more than its one frame (the move into beat uid: from the beat before it
    in the new layout). A key whose beat was deleted stays parked (nothing is thrown away; it simply never plays)."""
    back, keep = [], []
    order = None
    for e in entries:
        uid, t, y = int(e[0]), float(e[1]), float(e[2])
        look = dict(e[3]) if len(e) > 3 and isinstance(e[3], dict) else {}
        ad = layout.get(uid)
        span = None
        if ad is not None and not look.get("m"):
            if ad[1] > ad[0]:
                span = (ad[0], ad[1])
        elif ad is not None:
            if order is None:
                order = sorted(layout.values())
            before = [d for a, d in order if a < ad[0]]
            if before and ad[0] - before[-1] > 1.0 + 1e-9:
                span = (before[-1], ad[0])
        if span is None:
            keep.append(e if len(e) > 3 else [uid, t, y])
            continue
        s0, s1 = span
        if "h" in look:
            k = (s1 - s0) / float(look.get("sp") or (s1 - s0))
            hl = look["h"]
            look["h"] = [hl[0] * k, hl[1], hl[2] * k, hl[3]]
        back.append((s0 + t * (s1 - s0), y, look or None))
    return back, keep


def _settle_curve(fc):
    """Sort a curve's keys and work its auto handles out again — what FCurve.update() does, without the merge:
    update() (Blender 5.2) also merges keys closer than a hundredth of a frame, keeping the later one, and a
    retime squeezes keys that close together (adversarial review of 0.19: 64,647 baked rig keys gone)."""
    fc.keyframe_points.sort()
    fc.keyframe_points.handles_recalc()


def _split_handles_at(fc, x):
    """What keyframe_points.insert does to the two neighbours of a key it adds between them (Blender's
    subdivide_nonauto_handles): the Bezier is split there, so the curve keeps its shape on both sides, and the
    neighbours' handles are cut to the split. 0.18 re-added hand keys with insert(); 0.19 adds them exactly (no
    merge, s1) and calls this for them, so a rebuild leaves the in-betweens next to a hand key as 0.18 did
    (integration fingerprint, 15 Oct: Gossip Maze's Shefali moved up to 4 cm on her path without it)."""
    prev = nxt = None
    for kp in fc.keyframe_points:
        cx = kp.co.x
        if cx < x and (prev is None or cx > prev.co.x):
            prev = kp
        elif cx > x and (nxt is None or cx < nxt.co.x):
            nxt = kp
    if prev is None or nxt is None or prev.interpolation != 'BEZIER':
        return
    auto = {'AUTO', 'AUTO_CLAMPED'}
    prev_auto = (prev.handle_left_type in auto and prev.handle_right_type in auto) or prev.handle_right_type == 'VECTOR'
    next_auto = (nxt.handle_left_type in auto and nxt.handle_right_type in auto) or nxt.handle_left_type == 'VECTOR'
    if prev_auto and next_auto:
        return                          # auto handles are worked out again anyway
    v1, v2, v3, v4 = prev.co.copy(), prev.handle_right.copy(), nxt.handle_left.copy(), nxt.co.copy()
    h1, h2 = v1 - v2, v4 - v3           # BKE_fcurve_correct_bezpart: handles never pass the other key
    span, l1, l2 = v4.x - v1.x, abs(h1.x), abs(h2.x)
    if l1 + l2 > span > 0.0:
        fac = span / (l1 + l2)
        v2, v3 = v1 - fac * h1, v4 - fac * h2
    lo, hi = 0.0, 1.0                   # where the curve passes x (x(t) rises once corrected)
    for _ in range(60):
        t = (lo + hi) / 2.0
        u = 1.0 - t
        bx = u * u * u * v1.x + 3.0 * u * u * t * v2.x + 3.0 * u * t * t * v3.x + t * t * t * v4.x
        if bx < x:
            lo = t
        else:
            hi = t
    t = (lo + hi) / 2.0
    prev.handle_right = v1.lerp(v2, t)
    nxt.handle_left = v3.lerp(v4, t)


def _add_keys(fc, pts, split=False):
    """Add these keys exactly where they are: keyframe_points.insert and FCurve.update would merge a key into any
    other key within 0.01 frame (a retime squeezes keys that close together). pts: (frame, value[, look]).
    split: cut the neighbours' handles where each key goes in, as insert() does (_split_handles_at)."""
    if not pts:
        return
    if split:
        for p in pts:                   # one at a time, as insert() put them in: each splits the curve it finds
            _split_handles_at(fc, p[0])
            _add_keys(fc, [p])
        return
    n0 = len(fc.keyframe_points)
    fc.keyframe_points.add(len(pts))
    for kp, p in zip(list(fc.keyframe_points)[n0:], pts):
        x, y = p[0], p[1]
        look = p[2] if len(p) > 2 else None
        kp.co = (x, y)
        if not look:
            kp.interpolation = 'BEZIER'
            kp.handle_left_type = kp.handle_right_type = 'AUTO_CLAMPED'
            continue
        kp.interpolation = look.get("i", 'BEZIER')
        kp.easing = look.get("e", 'AUTO')
        kp.type = look.get("ty", 'KEYFRAME')
        kp.handle_left_type, kp.handle_right_type = look.get("ht", ('AUTO_CLAMPED', 'AUTO_CLAMPED'))
        if "h" in look:
            dlx, dly, drx, dry = look["h"]
            kp.handle_left = (x + dlx, y + dly)
            kp.handle_right = (x + drx, y + dry)
    _settle_curve(fc)


def _retime_fcurve(fc, tmap, parked=None):
    """Move this curve's keys to the new timing, to the sub-frame; two keys are never merged. A key in a span that
    has no room for it any more (a hold gone to nothing, a move squeezed to its one frame: _Retime.held) goes to
    `parked` (and off the curve), unless that would leave the curve without keys."""
    moved = False
    gone = []
    for j, kp in enumerate(fc.keyframe_points):
        x = kp.co.x
        h = tmap.held(x, moves=True) if parked is not None else None
        if h is not None:
            gone.append((j, _park_rec(h, kp.co.y, _key_look(kp))))
        nx = tmap(x)
        if abs(nx - x) < 1e-6:
            continue
        lx, rx = tmap(kp.handle_left.x), tmap(kp.handle_right.x)
        kp.co.x = nx
        kp.handle_left.x = min(lx, nx)
        kp.handle_right.x = max(rx, nx)
        moved = True
    if gone and len(gone) == len(fc.keyframe_points):
        gone = gone[1:]                 # one stays on the beat: a curve without keys would read 0
    for j, rec in reversed(gone):
        parked.append(rec)
        fc.keyframe_points.remove(fc.keyframe_points[j], fast=True)
    if moved or gone:
        _settle_curve(fc)
    return moved or bool(gone)


def _is_beat_marker(m, scene=None):
    """A marker the add-on made for a beat (0.19: by its record, so your own "B7" is not one). A staging not yet
    synced by 0.19 falls back to the old rule: B + digits."""
    scene = scene if scene is not None else getattr(m, "id_data", None)
    st = getattr(scene, "bb_st", None)
    marks = _beat_marks(st) if st is not None else None
    if marks is None:
        head = m.name.split(" ", 1)[0]
        return head[:1] == "B" and head[1:].isdigit()
    return any(m.name == n and m.frame == f for n, f in marks.values())


def carried_ids(scene):
    """Every data-block whose animation is timed against this staging's beats: all that lives in its STAGE
    layer (characters, props, cameras and their lenses, crowds) and, when Settings says so, the set."""
    st = scene.bb_st
    obs = []
    for c in layer_colls(scene, "STAGE"):
        obs += coll_objects(c)
    if st.carry_set:
        for c in layer_colls(scene, "SET"):
            obs += coll_objects(c)
        obs += instanced_objects(scene)
    out, seen = [], set()
    for ob in obs:
        if ob.get(ROLE_KEY) == FOLLOWER_ROLE:
            continue                    # a path follower is re-keyed by its path
        if ob.get(SETPIECE_KEY):        # a piece taken from the set shares the set's data: its shape-key, light or
            idbs = (ob,)                # camera keys are the set's own, retimed only with the set (review s4 #3)
        else:
            idbs = (ob, ob.data, getattr(ob.data, "shape_keys", None))
        for idb in idbs:
            if idb is not None and idb.as_pointer() not in seen:
                seen.add(idb.as_pointer())
                out.append((ob, idb))
    return out


def _marker_memo(st):
    try:
        return dict(json.loads(st.carry_memo or "{}"))
    except Exception:
        return {}


def carry_markers(scene, tmap):
    """Move every marker the layout does not place itself (camera cuts, your own markers) to the new timing. A
    marker sits on a whole frame, so where it really is — the fraction a retime gave it, or the hold it is parked
    in while that hold has no time — is kept in st.carry_memo, and the next retime starts from there: shrink a
    move and grow it back and the cut is where it was (audit r1 bug 3)."""
    st = scene.bb_st
    memo = _marker_memo(st)
    seen, moves = {}, []
    for m in scene.timeline_markers:
        if _is_beat_marker(m, scene):
            continue                    # sync_markers puts those on their beats
        k = f"{m.name}@{m.frame}"
        seen[k] = seen.get(k, 0) + 1
        rec = memo.get(f"{k}#{seen[k] - 1}")
        x, park = float(m.frame), None
        if isinstance(rec, list):       # parked in a hold with no time
            ad = tmap.new.get(int(rec[0]))
            if ad is not None and ad[1] > ad[0]:
                moves.append((m, ad[0] + float(rec[1]) * (ad[1] - ad[0]), None))
                continue
            if ad is not None:
                moves.append((m, float(ad[0]), rec))
                continue
        elif isinstance(rec, (int, float)) and abs(rec - m.frame) <= 0.5:
            x = float(rec)
        h = tmap.held(x)
        if h is not None:
            park = [h[0], h[1]]
        moves.append((m, tmap(x), park))
    n, out, again = 0, {}, {}
    for m, y, park in moves:
        nf = int(round(y))
        if nf != m.frame:
            m.frame = nf
            n += 1
    for m, y, park in moves:
        k = f"{m.name}@{m.frame}"
        again[k] = again.get(k, 0) + 1
        if park is not None:
            out[f"{k}#{again[k] - 1}"] = park
        elif abs(y - m.frame) > 1e-6:
            out[f"{k}#{again[k] - 1}"] = round(y, 6)
    text = json.dumps(out, ensure_ascii=False) if out else ""
    if st.carry_memo != text:
        st.carry_memo = text
    return n


def carry_animation(scene, tmap):
    """Move every marker and key that the layout does not rebuild itself to the new timing."""
    keyed = {ob.name for ob in keyed_objects(scene)}
    n = carry_markers(scene, tmap)
    seen = set()
    for ob, idb in carried_ids(scene):
        mine = ob.name in keyed
        held = _held(idb)
        before = json.dumps(held, sort_keys=True)
        for fc in id_fcurves(idb):
            p = fc.as_pointer()
            if p in seen:
                continue
            seen.add(p)
            if mine and idb == ob and (fc.data_path in _BLOCK_PATHS or fc.data_path in POSE_PATHS):
                continue                # the blocking (and a character's pose): rebuilt from the beat poses
            if mine and idb != ob and fc.data_path == "lens":
                continue                # a zoom on the beats: rebuilt too
            if fc.data_path.startswith(f'constraints["{PATH_CON}'):
                continue                # a drawn move: re-keyed by its path
            hk = f"{fc.data_path}|{fc.array_index}"
            back, keep = _unpark(held.get(hk, []), tmap.new)
            n += bool(_retime_fcurve(fc, tmap, keep))
            _add_keys(fc, back)         # keys whose hold has its time back
            n += bool(back)
            held[hk] = keep
        if json.dumps({k: v for k, v in held.items() if v}, sort_keys=True) != before:
            _store_held(idb, held)
    return n


# ------------------------------------------------------------------ natural moves (0.16)
#
# Aman, 11 Oct 2026: "the current blockout was feeling very mechanical". Until 0.15 everybody left a beat
# on the same frame, eased on the same curve over the whole move and froze together on the next beat.
# With Natural moves on, the beat poses stay the only truth and the layout derives the in-between:
#   - everybody takes the time their own move needs (a walk at the walking pace, a step, a turn); the
#     rest of the move is slack: they set off a little after each other and settle before the beat;
#   - a walker turns to where it is going just before it sets off and to its final facing as it lands;
#     walks hold a steady pace between a short start and stop, steps and turns ease all the way;
#   - a prop that stays with a character moves exactly with it;
#   - cameras that move on the beats travel the whole move, with feathered ends.
# Beats › Timing sets any one move by hand (starts after, lands early). The derived keys are typed
# "generated" (the small diamonds in the dope sheet) and are rebuilt on every Save Beat and every retime,
# so they can not go stale. Rotations take the short way round.

WALK_MIN = 1.2          # metres: from here on a move is a walk (turn, go, turn); below it a step that keeps its facing
RAMP_GAIN = 1.4         # a flat Bezier handle of h frames reaches 90 % of the cruising speed after about 1.4 h
WALK_RAMP = 0.55        # seconds a walker takes to get up to pace, and to stop
WALK_LOSS = WALK_RAMP / RAMP_GAIN   # the time those two ramps cost: a walk of d metres takes d / pace + this


def _wrap(a):
    return (a + math.pi) % (2.0 * math.pi) - math.pi


def turn_secs(rad):
    """How long an unhurried turn of this size takes: 30° about 0.5 s, 90° 1 s, 180° 1.7 s (it peaks near 160°/s)."""
    return min(1.8, max(0.35, 0.3 + abs(math.degrees(rad)) / 130.0))


def _jitter(name, uid, salt=0):
    """A fixed number 0..1 per object and beat: the same on every rebuild, different for everybody."""
    h = 2166136261
    for ch in f"{name}|{uid}|{salt}":
        h = ((h ^ ord(ch)) * 16777619) & 0xFFFFFFFF
    return h / 0xFFFFFFFF


def move_rec(scene, ob, uid):
    """The hand-set timing of this object's move into this beat, if any."""
    for m in scene.bb_st.moves:
        if ob is not None and m.owner == ob and m.beat_uid == uid:
            return m
    return None


def natural_plans(scene, poses, layout):
    """For every keyed object and every move: the frames it really moves in and how.
    {object name: [None, plan, ...]}, plan = dict(s2, e2, mode, h, heading); None = nothing to plan."""
    st = scene.bb_st
    f = fps(scene)
    pace = max(0.2, st.pace)
    objs = {ob.name: ob for ob in keyed_objects(scene)}
    recs = {(m.owner.name, m.beat_uid): m for m in st.moves if m.owner is not None}
    plans = {name: [None] * len(st.beats) for name in poses}
    xy = (("location", 0), ("location", 1))
    for i in range(1, len(st.beats)):
        s, e = layout[i - 1][1], layout[i][0]
        span = e - s
        if span < max(3, round(0.4 * f)):
            continue                        # a cut: everybody is simply there
        uid = st.beats[i].uid
        todo, chars = [], {}
        for name, plist in poses.items():
            ob = objs.get(name)
            if ob is None:
                continue
            p, q = plist[i - 1], plist[i]
            dv = Vector([q.get(("location", k), 0.0) - p.get(("location", k), 0.0) for k in range(3)])
            flat, dist = math.hypot(dv.x, dv.y), dv.length
            rot = [abs(_wrap(q.get(("rotation_euler", k), 0.0) - p.get(("rotation_euler", k), 0.0))) for k in range(3)]
            zoom = abs(q.get(LENS_CH, 0.0) - p.get(LENS_CH, 0.0))
            posed = max([abs(q.get(k, 0.0) - p.get(k, 0.0)) for k in POSE_KEYS if k in p and k in q] or [0.0])
            if dist < 1e-4 and max(rot) < 1e-4 and zoom < 1e-4 and posed < 1e-4:
                continue
            role = "cam" if ob.type == 'CAMERA' else ob.get(ROLE_KEY)
            it = dict(name=name, role=role, rec=recs.get((name, uid)), p=p, q=q, heading=0.0)
            path = path_for(scene, ob, uid)
            if role == "cam":
                it.update(mode='GLIDE', need=span / f)
            elif path is not None:
                it.update(mode='PATH', need=path_length(path) / pace + WALK_LOSS)
            elif role == "char":
                face = it["rec"].face if it["rec"] is not None else 'AUTO'
                walk = flat >= WALK_MIN if face == 'AUTO' else (face == 'ALONG' and flat > 0.05)
                if walk:
                    it.update(mode='WALK', need=flat / pace + WALK_LOSS, heading=math.atan2(-dv.x, dv.y))
                elif dist >= 0.05:
                    it.update(mode='STEP', need=max(0.5 + 0.9 * dist if dist < WALK_MIN else dist / pace + WALK_LOSS,
                                                    turn_secs(rot[2]) if rot[2] > math.radians(1.0) else 0.0))
                elif max(rot) >= math.radians(1.0):
                    it.update(mode='TURN', need=turn_secs(max(rot)))
                elif posed >= 1e-3:
                    it.update(mode='POSE', need=0.0)
                else:
                    continue                # a hair of a change: it eases over the whole move
                if posed >= 1e-3:           # sitting down, lying down, getting up: it takes its own time (0.19)
                    rest = p.get(REST_KEY, 0.0), q.get(REST_KEY, 0.0)
                    it.update(need=it["need"] + POSE_SECS,
                              pose_dir=1 if rest[1] > rest[0] + 1e-3 else (-1 if rest[1] < rest[0] - 1e-3 else 0))
                chars[name] = it
            else:
                it.update(mode='GLIDE', need=min(span / f, 0.5 + dist / 6.0))
            todo.append(it)
        for it in todo:                     # a prop that is with the same character before and after rides with it
            if it["role"] != "prop" or it["rec"] is not None or not all(k in it["p"] for k in xy):
                continue
            best = None
            for c in chars.values():
                if not all(k in c["p"] for k in xy):
                    continue
                d0 = math.hypot(it["p"][xy[0]] - c["p"][xy[0]], it["p"][xy[1]] - c["p"][xy[1]])
                d1 = math.hypot(it["q"][xy[0]] - c["q"][xy[0]], it["q"][xy[1]] - c["q"][xy[1]])
                if d0 < 0.8 and d1 < 0.8 and (best is None or d0 + d1 < best[0]):
                    best = (d0 + d1, c)
            if best is not None:
                it["carrier"] = best[1]
        free = [it for it in todo if it["role"] != "cam" and it["rec"] is None and "carrier" not in it]
        free.sort(key=lambda it: (-it["need"], _jitter(it["name"], uid)))
        stops = set()
        for rank, it in enumerate(free):    # whoever has the most to do leads, the others follow a beat later
            need = max(2, round(it["need"] * f))
            slack = span - need
            if slack <= round(0.12 * f):
                s2, e2 = s, e
            else:
                wait = (0.10 + 0.18 * min(rank, 5) + 0.10 * _jitter(it["name"], uid, 1)) * f
                s2 = s + min(round(wait), int(slack * 0.5))
                e2 = s2 + need
            while e2 in stops and e2 - s2 > 2:
                e2 -= 1                     # nobody stops on the same frame as somebody else
            stops.add(e2)
            it["win"] = (s2, e2)
        for it in todo:
            if it["rec"] is not None:
                s2 = min(e - 2, s + round(max(0.0, it["rec"].start_s) * f))
                it["win"] = (s2, min(e, max(s2 + 2, e - round(max(0.0, it["rec"].end_s) * f))))
            elif it["role"] == "cam":
                it["win"] = (s, e)
        for it in todo:     # a pose change takes its own part of the window: sitting down after the walk, up before it
            if "pose_dir" not in it:
                continue
            s2, e2 = it["win"]
            if it["mode"] == 'POSE' or it["pose_dir"] == 0:
                it["pwin"] = (s2, e2)
                continue
            t = min(max(2, round(POSE_SECS * f)), max(2, int((e2 - s2) * 0.6)))
            if it["pose_dir"] > 0:
                it["pwin"], it["win"] = (e2 - t, e2), (s2, max(s2 + 2, e2 - t))
            else:
                it["pwin"], it["win"] = (s2, s2 + t), (min(e2 - 2, s2 + t), e2)
        for it in todo:
            c = it.get("carrier")
            if c is not None:
                it["win"], it["mode"] = c["win"], 'CARRIED'
        for it in todo:
            s2, e2 = it["win"]
            src = it.get("carrier") or it
            if src["role"] == "cam":
                h = min(1.4, max(0.35, 0.25 * (e2 - s2) / f)) * f / RAMP_GAIN
            elif src["mode"] in ('WALK', 'PATH'):
                h = WALK_RAMP * f / RAMP_GAIN
            else:
                h = None                    # a step, a turn, a glide: eased all the way
            plans[it["name"]][i] = dict(s2=s2, e2=e2, mode=it["mode"], h=h, heading=it["heading"], pwin=it.get("pwin"))
    return plans


KEY_EPS = 1e-6              # closer than this on a channel and the two beats hold the same pose


def _hold_interior(values, layout=None, busy=None):
    """Which beats need no key on this channel: the ones inside a hold, where nothing moves either side.
    A move keeps a key at both ends, so holds can be dragged whole and the curve editor stays readable.
    busy: frames of the other keys on this channel (a walker's turn keys, keys made by hand). A beat next to a
    move that carries such a key keeps its own key: without it the curve bent from the last key before through
    every key-less hold — a walker that ends facing where he started turned 129° while standing (fuzz bug A), a
    hand key bent the holds around it and the next save baked the bend in (audit r1 bug 2)."""
    n = len(values)
    skip = set()
    for i in range(1, n - 1):
        if abs(values[i] - values[i - 1]) <= KEY_EPS and abs(values[i + 1] - values[i]) <= KEY_EPS:
            if busy and layout is not None:
                lo, hi = layout[i - 1][1], layout[i + 1][0]
                if any(lo < x < hi for x in busy):
                    continue
            skip.add(i)
    return skip


def _natural_keys(chans, plist, plans, layout, f, hand=None):
    """One object's keys on every channel, derived from its beat poses and its plans:
    {(path, index): ([(frame, value, generated, auto handle)], {(frame, frame): handle length})}.
    hand: {(path, index): [frames of keys made by hand]} (they stay; the beats around them keep their keys)."""
    out = {key: ([], {}) for key in chans}
    anchors = {key: [] for key in chans}        # (beat, arrive, leave, value, auto): filtered before they are written
    cur = {}
    yaw = ("rotation_euler", 2)
    n = len(plist)

    def put(key, frame, value, gen=True, auto=False):
        out[key][0].append((int(frame), float(value), gen, auto))

    def through(i):
        """A camera or prop on its way through a beat it does not hold on keeps moving."""
        if not (0 < i < n - 1) or layout[i][1] > layout[i][0]:
            return False
        a, b = plans[i], plans[i + 1]
        return bool(a and b and a["mode"] == b["mode"] == 'GLIDE'
                    and (a["s2"], a["e2"]) == (layout[i - 1][1], layout[i][0])
                    and (b["s2"], b["e2"]) == (layout[i][1], layout[i + 1][0]))

    for i in range(n):
        a, d = layout[i]
        plan = plans[i] if i else None
        tgt = {}
        for key in chans:
            v = plist[i].get(key, cur.get(key, 0.0))
            if key[0] == "rotation_euler" and key in cur:
                v = cur[key] + _wrap(v - cur[key])          # the short way round
            tgt[key] = v
        if plan is not None:
            s, s2, e2, mode, h = layout[i - 1][1], plan["s2"], plan["e2"], plan["mode"], plan["h"]
            dur = e2 - s2
            for key in chans:
                p, q = cur[key], tgt[key]
                if abs(q - p) < 1e-7 or (key == yaw and mode == 'WALK'):
                    continue
                k0, k1 = s2, e2
                if key in POSE_KEYS and plan.get("pwin"):
                    k0, k1 = plan["pwin"]                   # sitting or lying down has its own stretch of the move
                if key == yaw and mode in ('STEP', 'TURN'):
                    k1 = min(e2, s2 + max(2, round(turn_secs(q - p) * f)))     # the turn comes first
                if k0 > s:
                    put(key, k0, p)
                if k1 < a:
                    put(key, k1, q)
                if h is not None and (key[0] == "location" or key == LENS_CH or mode == 'GLIDE'):
                    out[key][1][(int(k0), int(k1))] = h
            if mode == 'WALK' and yaw in chans:
                y0 = cur[yaw]
                way = y0 + _wrap(plan["heading"] - y0)
                y1 = way + _wrap(tgt[yaw] - way)
                tgt[yaw] = y1
                t_in = round(turn_secs(way - y0) * f) if abs(way - y0) > math.radians(3.0) else 0
                t_out = round(turn_secs(y1 - way) * f) if abs(y1 - way) > math.radians(3.0) else 0
                t_in, t_out = min(t_in, int(dur * 0.45)), min(t_out, int(dur * 0.45))
                if t_in:
                    ts = max(s, s2 - round(0.2 * f))        # the turn starts just before the feet do
                    if ts > s:
                        put(yaw, ts, y0)
                    put(yaw, ts + t_in, way)
                if t_out:
                    put(yaw, e2 - t_out, way)
                if e2 < a:
                    put(yaw, e2, y1)
        auto = through(i)
        for key in chans:
            anchors[key].append((i, a, d, tgt[key], auto))
        cur = tgt
    for key, rows in anchors.items():           # only the ends of a move are keyed, never the inside of a hold
        busy = [k[0] for k in out[key][0]] + list((hand or {}).get(key, ()))
        skip = _hold_interior([r[3] for r in rows], layout, busy)
        for i, a, d, v, auto in rows:
            if i in skip:
                continue
            put(key, a, v, gen=False, auto=auto)
            if d > a:
                put(key, d, v, gen=False)
    return out


def _write_channel(fc, keys, caps):
    """Make one blocking F-curve hold exactly these keys: flat handles (everybody stops on a pose), as
    long as a third of the way to the neighbour or as short as the cap says (a steady walk)."""
    merged = []
    for k in sorted(keys, key=lambda k: k[0]):
        if merged and merged[-1][0] == k[0]:
            merged[-1] = (k[0], k[1], merged[-1][2] and k[2], merged[-1][3] or k[3])
        else:
            merged.append(k)
    while len(fc.keyframe_points):
        fc.keyframe_points.remove(fc.keyframe_points[-1], fast=True)
    n = len(merged)
    fc.keyframe_points.add(n)
    for j, (kp, (x, y, gen, auto)) in enumerate(zip(fc.keyframe_points, merged)):
        kp.co = (x, y)
        kp.interpolation = 'BEZIER'
        kp.type = GEN_KEY if gen else 'KEYFRAME'
        if auto:
            kp.handle_left_type = kp.handle_right_type = 'AUTO_CLAMPED'
            continue
        left = (x - merged[j - 1][0]) if j else (merged[1][0] - x if n > 1 else 9.0)
        right = (merged[j + 1][0] - x) if j < n - 1 else left
        hl, hr = left / 3.0, right / 3.0
        if j:
            hl = min(hl, caps.get((merged[j - 1][0], x), hl))
        if j < n - 1:
            hr = min(hr, caps.get((x, merged[j + 1][0]), hr))
        kp.handle_left_type = kp.handle_right_type = 'FREE'
        kp.handle_left = (x - hl, y)
        kp.handle_right = (x + hr, y)
    fc.update()


def write_beat_layout(scene, poses, start=None, _again=False, only=None):
    """Re-key the blocking from the beat poses on the current Move/Hold timing. Everything else that is
    timed against the beats (camera cuts, lens and scale keys, crowd cues, hand-made keys) goes along.

    only (0.19): re-key just these object names (a camera control: relayout_only). poses are still everybody's,
    so Natural moves times every move as a full re-key would; anybody else whose timing that changes (say the
    aim now moves into a beat and takes the lead) is re-keyed too, unless he stands off his keys (an unsaved
    move: his beat stays orange and his next save re-times him)."""
    st = scene.bb_st
    if not len(st.beats):
        return
    eyes_poses(scene, poses, only)       # a POV camera's step-off beat is a beat pose like any other (0.19)
    carry = dict(_CARRY) if _CARRY.get("scene") == scene.name else {}
    _CARRY.clear()
    layout = beat_layout(scene, start)
    new_layout = {b.uid: ad for b, ad in zip(st.beats, layout)}
    tmap = time_map(carry.get("old", {}), new_layout)
    marks = sorted({int(x) for ad in layout for x in ad})
    hand = carry.get("hand", {})
    natural = bool(st.natural)
    plans = natural_plans(scene, poses, layout) if natural else {}
    if only is not None and natural:
        only = set(only) | _retimed(scene, plans, only)
    f = fps(scene)
    for ob in keyed_objects(scene):
        p = poses.get(ob.name)
        chans = block_channels(ob)
        if p is None or not chans or (only is not None and ob.name not in only):
            continue
        # the keys made by hand between beats, on the new timing (to the sub-frame; parked while the hold they sat
        # in has no time, and back when it has)
        held = _held(ob)
        extra = {}
        for key in chans:
            hk = f"{key[0]}|{key[1]}"
            pts, keep = _unpark(held.get(hk, []), new_layout)
            for x, y, look in hand.get((ob.name, key), ()):
                h = tmap.held(x, moves=True) if tmap is not None else None
                if h is not None:
                    keep.append(_park_rec(h, y, look))
                    continue
                nx = tmap(x) if tmap is not None else x
                if not _on_mark(nx, marks):
                    pts.append((nx, y, look))
            held[hk] = keep
            extra[key] = sorted(pts, key=lambda p: p[0])
        try:
            _store_held(ob, held)
        except Exception as e:      # a linked object: its hand keys simply are not parked
            print("BB Stage parked keys:", e)
        busy = {key: [p[0] for p in pts] for key, pts in extra.items()}
        mine = plans.get(ob.name) or [None] * len(p)
        derived = _natural_keys(chans, p, mine, layout, f, busy) if natural else None
        for key, fc in chans.items():
            if natural:
                _write_channel(fc, *derived[key])
            else:
                pts = []
                vals = [pose.get(key, 0.0) for pose in p]
                skip = _hold_interior(vals, layout, busy.get(key))   # the inside of a hold carries no key either
                for i, ((a, d), pose) in enumerate(zip(layout, p)):
                    if key in pose and i not in skip:
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
            _add_keys(fc, extra[key], split=True)           # hand-made keys between beats stay, re-timed
        if REST_KEY in chans:
            try:
                plant_feet(ob, layout)      # sitting down or getting up never puts the legs through the floor
            except Exception as e:
                print("BB Stage feet on the floor:", ob.name, e)
        wins ={str(st.beats[i].uid): [pl["s2"], pl["e2"]] for i, pl in enumerate(mine) if pl}
        had = ob.get(MOVE_KEY)
        if wins:
            if had is None or had.to_dict() != wins:
                ob[MOVE_KEY] = wins
        elif had is not None:
            del ob[MOVE_KEY]
    if tmap is not None:
        carry_animation(scene, tmap)
    for b, (a, d) in zip(st.beats, layout):
        b.frame, b.frame_out = a, d
    sync_markers(scene)
    scene.frame_end = max(layout[-1][1], layout[0][0] + 1)
    apply_eyes(scene)                    # a POV camera's hand-off sits on its beat, on the new timing
    apply_look(scene)                    # and every camera's look follows its beats too
    turned = refresh_paths(scene)        # drawn moves follow the new timing (and drop with a deleted beat)
    if natural and turned and not _again:
        write_beat_layout(scene, sample_beat_poses(scene), start, _again=True, only=only)    # an arrival now faces along its path


def _retimed(scene, plans, only):
    """Objects outside only whose Natural moves windows these plans change (the windows each keeps in MOVE_KEY
    from its last re-key), and that hold their keys at the playhead, so re-keying them loses nothing."""
    st = scene.bb_st
    out = set()
    for ob in keyed_objects(scene):
        if ob.name in only or ob.name not in plans:
            continue
        wins = {str(st.beats[i].uid): [pl["s2"], pl["e2"]] for i, pl in enumerate(plans[ob.name]) if pl}
        had = ob.get(MOVE_KEY)
        try:
            had = {k: [int(x) for x in v] for k, v in had.to_dict().items()} if had is not None else {}
        except Exception:
            had = None
        if had != wins and not _off_its_keys(ob, scene.frame_current):
            out.add(ob.name)
    return out


def rebuild_blocking(scene):
    """Natural moves: derive the in-betweens again from the beat poses, on the timing as it is (after a
    Save Beat, a path edit, a change of Timing or of a setting)."""
    if _QUIET["beats"] or not (is_staging(scene) and len(scene.bb_st.beats)):
        return
    save_unsaved(scene)         # the rebuild re-reads the keys: an unsaved move would be gone (audit r4 H1)
    _QUIET["beats"] = True
    try:
        write_beat_layout(scene, sample_beat_poses(scene))
    finally:
        _QUIET["beats"] = False


def move_window(scene, ob, i):
    """The frames this object really moves in on its way into beat i: the whole move, or the part of it
    that Natural moves gives it."""
    st = scene.bb_st
    s, e = path_window(st, i)
    if st.natural and ob is not None:
        wins = ob.get(MOVE_KEY)
        w = wins.get(str(st.beats[i].uid)) if wins is not None else None
        if w is not None and s <= w[0] < w[1] <= e:
            return int(w[0]), int(w[1])
    return s, e


# ------------------------------------------------------------------ life in the holds, handheld (0.16)
#
# Nothing here adds a key to the blocking. A character's drift is a Noise modifier on its DELTA rotation,
# a camera's handheld is a Noise modifier on its lens shift: both ride on top of the beat poses, never
# touch them, and are set by one slider each. Research note (11 Oct 2026): real handheld is a slow drift,
# about a quarter of a degree, most of it below half a cycle a second; a fast jitter reads as an earthquake.

NOISE_GAIN = 9.9            # Noise modifier strength for an rms of 1 (measured on Blender 5.2, depth 1)
ALIVE_DEG = 1.0             # Life in the holds = 1: the facing drifts a degree (rms), three at its widest
HANDHELD_SHIFT = 0.0035     # Handheld = 1: the frame drifts like a quarter of a degree on a 35 mm (rms)


def _curve(idb, data_path, index=0):
    return next((c for c in id_fcurves(idb) if c.data_path == data_path and c.array_index == max(0, index)), None)


def _one_key_curve(idb, data_path, index, group):
    """An F-curve with one key at the value the property has now: something a Noise modifier can ride on."""
    fc = _curve(idb, data_path, index)
    if fc is None:
        idb.keyframe_insert(data_path, index=index, frame=1, group=group)
        fc = _curve(idb, data_path, index)
    return fc


def _noise_mod(fc, k=0):
    mods = [m for m in fc.modifiers if m.type == 'NOISE']
    while len(mods) <= k:
        mods.append(fc.modifiers.new('NOISE'))
    return mods[k]


def _set_noise(m, strength, scale, phase, depth=1):
    for attr, val in (("blend_type", 'REPLACE'), ("strength", strength), ("scale", scale),
                      ("phase", phase), ("depth", depth)):
        if getattr(m, attr) != val:
            setattr(m, attr, val)


def apply_alive(scene):
    """Life in the holds: every character's facing drifts a little, each in its own slow rhythm, so nobody
    stands like a statue between moves. 0 removes it."""
    st = scene.bb_st
    f = fps(scene)
    for ob in stage_objects(scene, roles=("char",)):
        if st.alive <= 0.0:
            if _curve(ob, "delta_rotation_euler", 2) is not None:
                _drop_fcurves(ob, {"delta_rotation_euler"})
                ob.delta_rotation_euler = (0.0, 0.0, 0.0)
            continue
        fc = _curve(ob, "delta_rotation_euler", 2)
        if fc is None:
            ob.delta_rotation_euler[2] = 0.0
            fc = _one_key_curve(ob, "delta_rotation_euler", 2, "BB Stage life")
        if fc is None:
            continue
        _set_noise(_noise_mod(fc), math.radians(ALIVE_DEG) * st.alive * NOISE_GAIN,
                   2.6 * f * (0.8 + 0.4 * _jitter(ob.name, 0, 7)), 100.0 * _jitter(ob.name, 0, 8))


def apply_handheld(cam_data, f=24.0):
    """Handheld: the frame drifts slowly with a little faster tremor on top, the same amount in the picture
    at any lens. It is lens shift, so the camera itself stays exactly where the beats put it. 0 removes it."""
    amt = cam_data.bbst_handheld
    for k, path in enumerate(("shift_x", "shift_y")):
        fc = _curve(cam_data, path)
        if amt <= 0.0:
            if fc is not None:
                base = fc.keyframe_points[0].co.y if len(fc.keyframe_points) else 0.0
                _drop_fcurves(cam_data, {path})
                setattr(cam_data, path, base)
            continue
        if fc is None:
            fc = _one_key_curve(cam_data, path, -1, "BB Stage handheld")
        if fc is None:
            continue
        s = HANDHELD_SHIFT * amt * NOISE_GAIN * (1.0, 0.8)[k]
        _set_noise(_noise_mod(fc, 0), s, 2.2 * f, 100.0 * _jitter(cam_data.name, k, 3))
        _set_noise(_noise_mod(fc, 1), s * 0.22, 0.33 * f, 100.0 * _jitter(cam_data.name, k, 4))


def _handheld_update(self, context):
    sc = getattr(context, "scene", None)
    apply_handheld(self, fps(sc) if sc is not None else 24.0)


# ------------------------------------------------------------------ a camera travels with a character (0.16)
#
# Sathya's shot division, 11 Oct 2026: "no relative movement between camera and Shefali, both move together
# and stop together". The camera is parented to a hidden helper that sits on the character, so it keeps its
# own framing and simply goes where the character goes. Parenting (not a constraint on the camera) is what
# lets the camera still be moved, flown and keyed by hand on any frame.

# 0.18, Aman 13 Oct 2026: "the Travels with camera setting should also affect rotation, so that I could make
# the camera a Snorricam as well". Turns with them on: the helper copies the character's facing too, so the
# camera is bolted to him — he stays put in frame and the maze swings past behind him, and when he turns his
# head the camera swings around him, with him as the pivot.

RIDE_ROLE = "ride"
RIDE_CON = "BB Ride"
RIDE_ROT = "BB Ride Turn"


def ride_helper(cam):
    p = cam.parent if cam is not None else None
    return p if (p is not None and p.get(ROLE_KEY) == RIDE_ROLE) else None


def ride_target(cam):
    h = ride_helper(cam)
    con = h.constraints.get(RIDE_CON) if h is not None else None
    return con.target if con is not None else None


def ride_turns(cam):
    """True when the camera turns with whoever it travels with (a Snorricam), not only goes where they go."""
    h = ride_helper(cam)
    return h is not None and h.constraints.get(RIDE_ROT) is not None


def ride_matrix(scene, target, turning, frame=None):
    """Where the ride helper sits: on its character, turned with them when it is a Snorricam. Worked out from
    the keys, not from an evaluated matrix — a depsgraph read here is only as fresh as the last update, and a
    stale one silently collapses the camera onto the character.

    0.19: a Snorricam turns with the character's life-in-the-holds drift too (its delta rotation, which the
    helper's Copy Rotation copies), so standing it free keeps every beat to the millimetre, not to 15 cm."""
    f = scene.frame_current if frame is None else frame
    if turning:
        rot = _with_drift(target, Euler(keyed_rotation_at(target, f)), f)
    else:
        rot = Matrix.Identity(3)
    return Matrix.Translation(keyed_location_at(target, f)) @ rot.to_4x4()


def set_ride_turn(scene, cam, on):
    """Switch the turning on or off without the picture moving: whatever the camera is framing right now, it
    keeps framing. From here on its beat poses are read against the character's facing."""
    h = ride_helper(cam)
    tgt = ride_target(cam)
    if h is None or tgt is None or on == ride_turns(cam):
        return
    was = ride_matrix(scene, tgt, ride_turns(cam))
    if on:
        con = h.constraints.new('COPY_ROTATION')
        con.name = RIDE_ROT
        con.target = tgt
    else:
        h.constraints.remove(h.constraints[RIDE_ROT])
    now = ride_matrix(scene, tgt, on)
    cam.matrix_parent_inverse = now.inverted() @ was @ cam.matrix_parent_inverse


def ride_world(scene, cam):
    """Where the camera really is, from its own numbers: its basis, through the helper it rides. Object
    matrix_world is whatever the last depsgraph evaluation left there — on a camera made a moment ago it is
    still the identity, which used to drop a new ride on top of its character."""
    h = ride_helper(cam)
    if h is None:
        return cam.matrix_basis.copy()
    tgt = ride_target(cam)
    base = ride_matrix(scene, tgt, ride_turns(cam)) if tgt is not None else Matrix.Translation(h.location)
    return base @ cam.matrix_parent_inverse @ cam.matrix_basis


def _ride_basis_world(scene, cam, h, f, loc, rot):
    """Where a riding camera really is on frame f when its own (helper-space) pose is loc, rot."""
    tgt = ride_target(cam)
    base = ride_matrix(scene, tgt, ride_turns(cam), f) if tgt is not None else Matrix.Translation(h.location)
    return base @ cam.matrix_parent_inverse @ Matrix.LocRotScale(loc, rot, cam.scale)


def set_ride(scene, cam, target):
    """The camera travels with this character or prop from where both are now (None: it stands free again,
    where it is now). Returns False when it can not: a camera with a drawn path flies its own path.

    0.19: standing free keeps every beat's picture. The beat keys of a riding camera are read against the
    helper; letting go bakes them into world poses, beat by beat, so a keyed camera no longer jumps by the
    distance its character walked (audit r2 H5). A camera in somebody's eyes leaves them first: it is either
    somebody's eyes or travels with somebody, never both (the two exclude each other both ways)."""
    h = ride_helper(cam)
    if target is not None:
        if any(r.owner == cam for r in scene.bb_st.paths):
            return False
        if cam.constraints.get(EYES_CON) is not None:
            set_eyes(scene, cam, None)
            h = ride_helper(cam)
    world = ride_world(scene, cam)
    if target is None:
        if h is not None:
            turned = ride_turns(cam)
            st = scene.bb_st
            poses = sample_beat_poses(scene) if (len(st.beats) and block_channels(cam)) else None
            rows = poses.get(cam.name) if poses is not None else None
            if rows is not None:
                ref = cam.rotation_euler.copy()
                for j, b in enumerate(st.beats):
                    row = rows[j]
                    loc = Vector([row.get(("location", k), cam.location[k]) for k in range(3)])
                    rot = Euler([row.get(("rotation_euler", k), cam.rotation_euler[k]) for k in range(3)])
                    w = _ride_basis_world(scene, cam, h, b.frame, loc, rot)
                    wl, wr = w.to_translation(), w.to_euler('XYZ', ref)
                    ref = wr
                    for k in range(3):
                        if ("location", k) in row:
                            row[("location", k)] = wl[k]
                        if ("rotation_euler", k) in row:
                            row[("rotation_euler", k)] = wr[k]
            cam.parent = None
            cam.matrix_parent_inverse = Matrix.Identity(4)
            cam.location = world.to_translation()
            if turned:          # it was bolted to somebody: its facing was theirs, keep what we see
                cam.rotation_euler = world.to_euler('XYZ', cam.rotation_euler)
            if not helper_used(h, [c for c in rig_cams(scene) if c != cam]):
                bpy.data.objects.remove(h)
            if rows is not None:
                relayout_only(scene, [cam], poses)
        return True
    if h is None:
        h = bpy.data.objects.new(f"Ride · {cam.name}", None)
        h[ROLE_KEY] = RIDE_ROLE
        h.empty_display_size = 0.1
        h.hide_render = True
        h.hide_select = True
        coll = sub_coll(scene, "STAGE", "Cameras") or scene.collection
        coll.objects.link(h)
        h.constraints.new('COPY_LOCATION').name = RIDE_CON
    h.constraints[RIDE_CON].target = target
    turn = h.constraints.get(RIDE_ROT)
    if turn is not None:
        turn.target = target                         # a Snorricam handed to somebody else turns with them
    at = keyed_location_at(target, scene.frame_current)
    h.location = at                                  # where the helper rests should its character ever go
    if turn is None:
        off = world.to_translation() - cam.location  # a camera that already travels keeps its picture
        cam.parent = h
        cam.matrix_parent_inverse = Matrix.Translation(off - at)
    else:
        cam.parent = h
        cam.matrix_parent_inverse = ride_matrix(scene, target, True).inverted() @ world @ cam.matrix_basis.inverted()
    return True


def clear_rides_of(scene, target):
    """Cameras that travelled with this object stand free, each beat where it was."""
    for cam in stage_cams(scene):
        if ride_target(cam) == target:
            set_ride(scene, cam, None)


# ------------------------------------------------------------------ where a camera looks (0.18)
#
# Aman, 13 Oct 2026: "in beat B3, Cam to Jai, I want the camera to point towards Jai and track Jai while it is
# moving ... we can just keyframe the camera in one beat where the camera is looking at one point and then the
# other ... ideally we should be able to keyframe the camera itself to where to look or track something."
#
# So every camera has one aim point, "Aim · <camera>": a hidden empty it points at. The aim is a pose like any
# other — put it somewhere on a beat and Save Beat — and it can be told to ride a character or a prop, in which
# case the camera tracks them live, wherever the blocking takes them. Which it rides is part of the beat too, so
# a camera can hold on Jai, then let go and look at a spot, then pick up Shefali, all in one shot. Switching
# between two people slides the aim from one to the other over the move, so the camera pans instead of snapping.

AIM_ROLE = "aim"
LOOK_CON = "BB Look"               # on the camera: Track To, pointing at its aim
AIM_CON = "BB Aim · "              # on the aim: Copy Location per character it can ride; the rest of its name is its key
LOOK_KEY = "bb_st_look"            # on the camera: {beat uid: "" (a free point) | rider key | "off"}
LOOK_OFF = "off"                   # the camera is not pointing at anything: its own rotation keys rule
AIM_HEAD = 1.55                    # a character is aimed at around the head, not the feet
AIM_AHEAD = 4.0                    # an aim point made from nothing sits this far in front of the camera
OWNER_KEY = "bb_st_owner"          # retired before release: an object pointer here counted as a user of the camera

# 0.19: who a camera looks at is held by pointers, never by names. A look-table entry is a rider key: the rest of
# the name of one Copy Location on the aim, and that constraint's target is the object. Renaming a character (one
# click in the Cast list) used to drop the look and swing the camera onto the world origin (audits r2 M1, r4 H5);
# now the pointer follows the object, and another object taking the old name changes nothing. 0.18 used the
# object's name as the key, which is exactly the name of the constraint it made, so its tables read the same.


def aim_of(cam):
    con = cam.constraints.get(LOOK_CON) if (cam is not None and cam.type == 'CAMERA') else None
    tgt = con.target if con is not None else None
    return tgt if (tgt is not None and tgt.get(ROLE_KEY) == AIM_ROLE) else None


def rig_cams(scene):
    """Every camera anywhere in the staging's STAGE layer: the Cameras collection and any collection filed under
    it or beside it. Shot cameras tidied into a child collection ("Shots 1-10") are not in stage_cams, but their
    aims and ride helpers are still theirs, and must never be cleared away as left over (review of 0.19 s2)."""
    out, seen = [], set()
    for c in layer_colls(scene, "STAGE"):
        for ob in coll_objects(c):
            if ob.type == 'CAMERA' and ob.as_pointer() not in seen:
                seen.add(ob.as_pointer())
                out.append(ob)
    return out


def _helper_get(ob):
    return {AIM_ROLE: aim_of, RIDE_ROLE: ride_helper, EYES_ROLE: eyes_helper}.get(ob.get(ROLE_KEY)) if ob else None


def helper_used(ob, cams):
    """True when one of these cameras uses this aim, ride helper or eyes."""
    get = _helper_get(ob)
    return get is not None and any(get(c) == ob for c in cams)


def _used_anywhere(ob):
    """Last word before a helper is taken away: does any camera that is still in some scene use it? Read from
    the cameras themselves (a Track To, a parent, the eyes' Copy Location), so it costs nothing to record and
    nothing can go stale. Only asked for the rare helper the staging's own cameras no longer use."""
    get = _helper_get(ob)
    if get is None:
        return False
    for c in bpy.data.objects:
        if c.type == 'CAMERA' and get(c) == ob and len(c.users_scene):
            return True
    return False


def helper_keeper(h, users, prefix):
    """Of the cameras sharing one helper (a Shift+D copy shares its original's), the one that keeps it: the one
    it is named after, else the oldest in this session (a copy is always younger than what it was copied from).

    0.19: who owns a helper is read from who uses it, never stored. An object pointer stored on the helper
    counted as a user of the camera, so X in a 3D view no longer deleted the camera and its cut kept firing."""
    for c in users:
        want = f"{prefix}{c.name}"
        if h.name == want or (want.startswith(h.name) and len(h.name.encode("utf-8")) >= 60):
            return c
    return min(users, key=lambda c: getattr(c, "session_uid", 0))


def _alive_in(scene, ob):
    try:
        return ob is not None and scene.objects.get(ob.name) == ob
    except ReferenceError:
        return False


def look_table(cam):
    """{beat uid: what this camera looks at on that beat}. Beats with no entry inherit the one before."""
    rec = cam.get(LOOK_KEY) if cam is not None else None
    try:
        return {int(k): str(v) for k, v in dict(rec).items()}
    except Exception:
        return {}


def rider_cons(aim):
    """{rider key: Copy Location} for everybody this aim can ride."""
    if aim is None:
        return {}
    return {c.name[len(AIM_CON):]: c for c in aim.constraints if c.name.startswith(AIM_CON)}


def look_target(cam, key):
    """The object a rider key stands for: the target of its constraint on the aim (a pointer), else, for an
    entry no constraint holds yet, the object of that name. None: it is gone."""
    if not key or key == LOOK_OFF:
        return None
    c = rider_cons(aim_of(cam)).get(key)
    if c is not None:
        return c.target
    return bpy.data.objects.get(key)


def look_states(scene, cam, table=None):
    """What the camera looks at on every beat, inherited forward: None (never set), LOOK_OFF, "" (its aim
    point) or a rider key."""
    table = look_table(cam) if table is None else table
    out, cur = [], None
    for b in scene.bb_st.beats:
        if b.uid in table:
            cur = table[b.uid]
        out.append(cur)
    return out


def look_source(scene, cam, i):
    """The beat that set the look beat i has (i itself, or an earlier one it inherits from)."""
    table = look_table(cam)
    for j in range(min(i, len(scene.bb_st.beats) - 1), -1, -1):
        if scene.bb_st.beats[j].uid in table:
            return j
    return None


def look_at_beat(scene, cam, i):
    """What the camera looks at on beat i, inheriting from the beats before it: None (nothing),
    "" (its own aim point) or an object."""
    if i is None:
        return None
    states = look_states(scene, cam)
    if not (0 <= i < len(states)):
        return None
    val = states[i]
    if val is None or val == LOOK_OFF:
        return None
    return look_target(cam, val) if val else ""


def order_cam_rig(cam):
    """Where a camera points is worked out last: its drawn path or the eyes it sits in move it first, then its
    Track To aims from where it really is. Set the other way round (Looks at first, then a path or Eyes of),
    the camera aimed from its keyed spot and missed by up to 89° on an orbit (audits r2 H4, r4 H4)."""
    if cam is None or cam.type != 'CAMERA':
        return False
    cons = cam.constraints
    i = cons.find(LOOK_CON)
    if i < 0 or i == len(cons) - 1:
        return False
    cons.move(i, len(cons) - 1)
    return True


def ensure_aim(scene, cam):
    """The camera's aim point, made on demand and parked a few metres in front of it."""
    aim = aim_of(cam)
    if aim is None:
        aim = bpy.data.objects.new(f"Aim · {cam.name}", None)
        aim[ROLE_KEY] = AIM_ROLE
        aim.empty_display_type = 'SPHERE'
        aim.empty_display_size = 0.22
        aim.hide_render = True
        aim.show_in_front = True
        (sub_coll(scene, "STAGE", "Cameras") or scene.collection).objects.link(aim)
        fwd = (cam.matrix_world.to_3x3() @ Vector((0.0, 0.0, -1.0))).normalized()
        aim.location = cam.matrix_world.translation + fwd * AIM_AHEAD
        con = cam.constraints.get(LOOK_CON) or cam.constraints.new('TRACK_TO')
        con.name = LOOK_CON
        con.target = aim
        con.track_axis, con.up_axis = 'TRACK_NEGATIVE_Z', 'UP_Y'
        con.influence = 0.0
    want = f"Aim · {cam.name}"
    if (aim.name != want and bpy.data.objects.get(want) is None
            and not helper_used(aim, [c for c in rig_cams(scene) if c != cam])):
        aim.name = want                 # never renamed back and forth between two cameras (audit r2 M3)
    order_cam_rig(cam)
    return aim


def _ensure_rider(aim, target):
    """The rider key of this object on this aim, making its Copy Location if it has none yet."""
    for k, c in rider_cons(aim).items():
        if c.target == target:
            return k
    c = aim.constraints.new('COPY_LOCATION')
    c.name = AIM_CON + target.name          # Blender keeps it unique (and short): the key is what it ends up as
    c.target = target
    c.use_offset = True
    c.influence = 0.0
    return c.name[len(AIM_CON):]


def ensure_beat_keys(scene, ob):
    """Give an object whose place and turn are not keyed yet its beat keys: the pose it has now, on every beat."""
    st = scene.bb_st
    if not len(st.beats) or any(k[0] in _BLOCK_PATHS for k in block_channels(ob)):
        return False
    for f in sorted({st.beats[0].frame, beat_out(st.beats[-1])}):     # keyed at both ends, as a layout keys a hold
        ob.keyframe_insert("location", frame=f, group="BB Stage")
        ob.keyframe_insert("rotation_euler", frame=f, group="BB Stage")
    return True


def _cam_parent_matrix(scene, cam, f):
    """What a camera's own pose is read against on frame f: the world, or the helper it travels on."""
    h = ride_helper(cam)
    if h is None:
        return Matrix.Identity(4)
    tgt = ride_target(cam)
    base = ride_matrix(scene, tgt, ride_turns(cam), f) if tgt is not None else Matrix.Translation(h.location)
    return base @ cam.matrix_parent_inverse


def cam_own_matrix(scene, cam, f):
    """The camera's world matrix on frame f from its keys and its rig (Travels with, Eyes of), before any Looks
    at — read from the keys, so no playhead moves and no unsaved move is lost. Exact on beat frames."""
    m = _cam_parent_matrix(scene, cam, f) @ Matrix.LocRotScale(
        keyed_location_at(cam, f), Euler(keyed_rotation_at(cam, f)), cam.scale)
    con = cam.constraints.get(EYES_CON)
    if con is not None and eyes_helper(cam) is not None:
        fc = _curve(cam, EYES_INF)
        inf = fc.evaluate(f) if fc is not None else con.influence
        e = eyes_world(cam, f)
        if e is not None and inf > 0.0:
            m.translation = m.translation.lerp(e.translation, min(1.0, inf))
    return m


def track_rotation(eye, point, ref=None):
    """The world rotation BB Look gives a camera at eye that points at point (-Z at it, Y up), or None."""
    d = point - eye
    if d.length < 1e-6:
        return None
    q = d.to_track_quat('-Z', 'Y')
    return q.to_euler('XYZ', ref) if ref is not None else q.to_euler('XYZ')


def _aim_point(scene, cam, state, arow, f):
    """The world point the camera aims at on frame f of a beat in this look state, from the aim's beat pose
    (None: it aims at nothing, or at somebody who is gone)."""
    if state is None or state == LOOK_OFF or arow is None:
        return None
    p = Vector([arow.get(("location", k), 0.0) for k in range(3)])
    if state == "":
        return p
    tgt = look_target(cam, state)
    if not _alive_in(scene, tgt):
        return None
    return p + keyed_location_at(tgt, f)


def _ahead_point(scene, cam, f):
    m = cam_own_matrix(scene, cam, f)
    return m.translation + (m.to_3x3() @ Vector((0.0, 0.0, -1.0))).normalized() * AIM_AHEAD


def set_look(scene, cam, i, target):
    """On this beat the camera looks at: an object (it tracks it, wherever it goes), "" (its own aim point,
    which is a pose you place), or None (nothing — its own rotation keys rule again). It holds until a beat
    changes it.

    0.19 (audits r2 H2, H3, M9 and r4 H3): only the beats whose look really changes are touched, and each keeps
    its picture. A beat that starts tracking somebody aims at their head (the offset is keyed as a beat pose,
    never left loose for the old keys to take back); a beat that switches to the aim point gets the point the
    camera was aiming at; a beat that lets go keeps the rotation the look gave it. Beats that keep their look,
    and the aim positions saved on them, are left alone."""
    st = scene.bb_st
    if cam is None or cam.type != 'CAMERA' or not len(st.beats):
        return
    i = min(max(int(i), 0), len(st.beats) - 1)
    tidy_camera_rigs(scene)
    aim = ensure_aim(scene, cam)
    ensure_beat_keys(scene, aim)
    table = look_table(cam)
    before = look_states(scene, cam, table)
    if target is None:
        value = LOOK_OFF
    elif hasattr(target, "name"):
        value = _ensure_rider(aim, target)
    else:
        value = ""
    table[st.beats[i].uid] = value
    after = look_states(scene, cam, table)
    changed = [j for j in range(len(after)) if before[j] != after[j]]
    poses = sample_beat_poses(scene) if changed else None
    arows = poses.get(aim.name) if poses is not None else None
    crows = poses.get(cam.name) if poses is not None else None
    dirty = False
    for j in changed:
        f = st.beats[j].frame
        was = _aim_point(scene, cam, before[j], arows[j] if arows is not None else None, f)
        new = after[j]
        if new is None or new == LOOK_OFF:
            if was is None:
                continue                    # it was not aiming at anything: its own rotation already rules
            ref = Euler(keyed_rotation_at(cam, f))
            rot = track_rotation(cam_own_matrix(scene, cam, f).translation, was, ref)
            if rot is None:
                continue
            world = Matrix.LocRotScale(cam_own_matrix(scene, cam, f).translation, rot, Vector((1.0, 1.0, 1.0)))
            local = (_cam_parent_matrix(scene, cam, f).inverted() @ world).to_euler('XYZ', ref)
            if crows is not None and all(("rotation_euler", k) in crows[j] for k in range(3)):
                for k in range(3):
                    crows[j][("rotation_euler", k)] = local[k]
                dirty = True
            elif j == i:
                cam.rotation_euler = local  # a Static camera: it keeps the picture of this beat
        elif arows is not None:
            if new == "":
                p = was if was is not None else _ahead_point(scene, cam, f)
            else:
                tgt = look_target(cam, new)
                p = look_offset(tgt, f)     # his head on this beat, at his height and in his pose (0.19)
            for k in range(3):
                arows[j][("location", k)] = p[k]
            dirty = True
    cam[LOOK_KEY] = {str(k): v for k, v in table.items()}
    if dirty:
        relayout_only(scene, [aim, cam], poses)
    else:
        apply_look(scene)


def fill_stops(scene, ob):
    """Beats a Save Beat must not fill a changed pose into. For a camera's aim: every beat where its look
    changes — an aim point is a place in the world, while on a beat that tracks somebody the aim's position is
    an offset from them, and a fill across the two moved one with the other (audit r4 H3c). Nothing for
    anything else."""
    if ob is None or ob.get(ROLE_KEY) != AIM_ROLE:
        return set()
    cam = next((c for c in stage_cams(scene) if aim_of(c) == ob), None)
    if cam is None:
        return set()
    s = look_states(scene, cam)
    return {j for j in range(1, len(s)) if s[j] != s[j - 1]}


def apply_look(scene):
    """Write every camera's look from its beat table: the Track To fades in over the move into the beat it
    starts on and out again where it stops, and the aim rides whoever that beat names. Rebuilt from the table
    on every save and retime, so it follows the beats around. A beat naming somebody who is gone points at
    nothing (its own rotation), never at the bare offset near the world origin."""
    st = scene.bb_st
    if not len(st.beats):
        return
    tidy_camera_rigs(scene, deep=False)     # inside a layout: nothing here may start another one
    layout = [(b.frame, beat_out(b)) for b in st.beats]
    for cam in stage_cams(scene):
        table = look_table(cam)
        con = cam.constraints.get(LOOK_CON)
        if not table:
            if con is not None:
                _drop_fcurves(cam, {f'constraints["{LOOK_CON}"].influence'})
                con.influence = 0.0
            continue
        aim = ensure_aim(scene, cam)
        riders = rider_cons(aim)
        renamed = {}
        for key in {v for v in table.values() if v not in ("", LOOK_OFF)}:
            if key not in riders:           # an entry no constraint holds yet: found by name, it gets one
                tgt = bpy.data.objects.get(key)
                if tgt is not None:
                    new = _ensure_rider(aim, tgt)
                    if new != key:
                        renamed[key] = new
        if renamed:
            table = {u: renamed.get(v, v) for u, v in table.items()}
            cam[LOOK_KEY] = {str(k): v for k, v in table.items()}
        riders = rider_cons(aim)
        state = look_states(scene, cam, table)
        live = {k for k, c in riders.items() if _alive_in(scene, c.target)}
        # the camera's Track To: on wherever the beat names its aim point or somebody who is still here
        on = [s == "" or (s not in (None, LOOK_OFF) and s in live) for s in state]
        keys = []
        for i, b in enumerate(st.beats):
            a = layout[i][0]
            if i == 0:
                keys.append((a, 1.0 if on[0] else 0.0))
            elif on[i] != on[i - 1]:
                keys.append((layout[i - 1][1], 0.0 if on[i] else 1.0))     # it swings over during the move
                keys.append((a, 1.0 if on[i] else 0.0))
        _write_keys(cam, f'constraints["{LOOK_CON}"].influence', keys, 'BEZIER')
        # the aim: riding whoever this beat names, or sitting on its own keys
        used = {s for s in state if s not in (None, LOOK_OFF, "")}
        for key in used:
            c = riders.get(key)
            if c is None:
                continue
            rows = []
            for i, b in enumerate(st.beats):
                want = 1.0 if state[i] == key else 0.0
                a = layout[i][0]
                if i == 0:
                    rows.append((a, want))
                elif (state[i] == key) != (state[i - 1] == key):
                    rows.append((layout[i - 1][1], 1.0 - want))
                    rows.append((a, want))
            _write_keys(aim, f'constraints["{c.name}"].influence', rows, 'BEZIER')
        for key, c in list(riders.items()):    # a target nobody looks at any more
            if key not in used:
                _drop_fcurves(aim, {f'constraints["{c.name}"].influence'})
                aim.constraints.remove(c)
        order_cam_rig(cam)
        if st.natural:
            _even_look_blends(cam, aim, state, live, layout)


def _even_look_blends(cam, aim, state, live, layout):
    """Natural moves give an aim point its own short, staggered glide, while the hand-over between the aim
    point and somebody the camera tracks fades over the whole move: on two clocks, the look whipped off the
    line between the two (audit r2 M6, 2.4 m). On those moves the aim now travels on exactly the fade's
    curve, so the look slides straight from one to the other."""
    riders = rider_cons(aim)
    locs = [fc for fc in id_fcurves(aim) if fc.data_path == "location"]
    if not locs:
        return
    for i in range(1, len(state)):
        a, b = state[i - 1], state[i]
        if a == b or "" not in (a, b):
            continue
        other = b if a == "" else a
        c = riders.get(other)
        if other not in live or c is None:
            continue
        inf = _curve(aim, f'constraints["{c.name}"].influence')
        s, e = layout[i - 1][1], layout[i][0]
        if inf is None or e - s < 2:
            continue
        k0 = next((k for k in inf.keyframe_points if abs(k.co.x - s) < 0.5), None)
        k1 = next((k for k in inf.keyframe_points if abs(k.co.x - e) < 0.5), None)
        if k0 is None or k1 is None:
            continue
        hr, hl = k0.handle_right.x - k0.co.x, k1.co.x - k1.handle_left.x
        for fc in locs:
            pts = fc.keyframe_points
            for n in reversed(range(len(pts))):
                if s + 0.5 < pts[n].co.x < e - 0.5 and pts[n].type == GEN_KEY:
                    pts.remove(pts[n], fast=True)
            p0 = next((k for k in pts if abs(k.co.x - s) < 0.5), None)
            p1 = next((k for k in pts if abs(k.co.x - e) < 0.5), None)
            if p0 is not None:
                p0.handle_right_type = 'FREE'
                p0.handle_right = (p0.co.x + hr, p0.co.y)
            if p1 is not None:
                p1.handle_left_type = 'FREE'
                p1.handle_left = (p1.co.x - hl, p1.co.y)
            fc.update()


# ------------------------------------------------------------------ a camera in a character's eyes (0.17)
#
# Aman, 12 Oct 2026, the Gossip Maze: "we cut to a camera that is basically Jai's POV ... he turns 180° and
# the camera slightly drifts and somehow comes on Jai's front face." A point of view that becomes a shot of
# the person whose point of view it was is two cameras' worth of hand-keying, and the hand-off is where it
# always falls apart. Here it is one camera: it copies a hidden helper sitting in the character's eyes (the
# gaze is posed on the beats like any other pose), and at a beat you choose it lets go over a second or so
# and flies to wherever you parked it on the next beat. It leaves from the pose it was already in, so there
# is nothing to pop, and both ends stay yours to move.

EYES_ROLE = "eyes"
EYES_CON = "BB Eyes"
EYES_KEY = "bb_st_eyes"            # on the camera: [step-off beat uid, seconds] (uid 0: it never steps off)
EYES_OWN_KEY = "bb_st_eyes_own"    # on the camera: [beat uid, x, y, z] its own place on the step-off beat before
                                   # the eyes' place was written there (0.19: given back when the step-off moves)
EYES_INF = f'constraints["{EYES_CON}"].influence'
STEP_OFF_S = 0.8                   # how long the camera takes to leave the eyes, unless told otherwise
EYES_DROP = 0.12                   # the eyes sit this far below the top of the head
EYES_FWD = 0.35                    # and this far in front of it, so the peg's own head is never in shot
                                   # (the same step the eyeline button in the Cast list takes)


def eyes_helper(cam):
    con = cam.constraints.get(EYES_CON) if (cam is not None and cam.type == 'CAMERA') else None
    tgt = con.target if con is not None else None
    return tgt if (tgt is not None and tgt.get(ROLE_KEY) == EYES_ROLE) else None


def eyes_target(cam):
    """The character whose eyes this camera is in (None: it is a camera of its own)."""
    h = eyes_helper(cam)
    return h.parent if h is not None else None


def eyes_aims(cam):
    """True when the eyes also decide where the camera points (the 0.17 rig). From 0.18 the eyes only carry
    the camera and the aim is its own, so it can be keyed or given a Looks at."""
    con = cam.constraints.get(EYES_CON) if (cam is not None and cam.type == 'CAMERA') else None
    return con is not None and con.type == 'COPY_TRANSFORMS'


def eyes_of(scene, char):
    for ob in stage_objects(scene, roles=(EYES_ROLE,)):
        if ob.parent == char:
            return ob
    return None


def ensure_eyes_helper(scene, char):
    """The helper that sits in a character's eyes, looking where he faces. One per character: several
    cameras can be in the same pair of eyes."""
    h = eyes_of(scene, char)
    if h is None:
        h = bpy.data.objects.new(f"Eyes · {char.name}", None)
        h[ROLE_KEY] = EYES_ROLE
        h.empty_display_type = 'PLAIN_AXES'
        h.empty_display_size = 0.25
        h.hide_render = True
        h.show_in_front = True
        (sub_coll(scene, "STAGE", "Cameras") or scene.collection).objects.link(h)
        h.parent = char
        h.matrix_parent_inverse = Matrix.Identity(4)
        fwd = EYES_FWD
        if char.get(ROLE_KEY) == "char":   # never behind the nose of a very wide peg (s7 review)
            fwd = max(fwd, round(peg_dims(peg_height_of(char), peg_width_of(char))["nose_tip"] + 0.01, 3))
        h.location = (0.0, fwd, max(0.3, peg_height_of(char) - EYES_DROP))
        h.rotation_euler = (math.pi / 2, 0.0, 0.0)      # a camera that copies it looks where the character faces
        for b in scene.bb_st.beats:
            for f in sorted({b.frame, beat_out(b)}):
                h.keyframe_insert("location", frame=f, group="BB Stage")
                h.keyframe_insert("rotation_euler", frame=f, group="BB Stage")
    want = f"Eyes · {char.name}"
    if h.name != want and bpy.data.objects.get(want) is None:
        h.name = want
    ensure_eyes_posture(h)              # he sits or lies down: his eyes go with him (0.19)
    return h


def set_eyes(scene, cam, char):
    """The camera sits in this character's eyes (None: it comes out and stays exactly where it is now).
    Returns False when it can not: a camera with a drawn path flies its own path.

    0.19: coming out keeps what the eyes gave it, its place beat by beat, and keeps its own aim: the 0.18
    eyes carry the camera only, so its rotation keys are its own and are no longer overwritten with the
    character's facing (audit r2 H6). Going into another character's eyes takes the old helper away when
    nobody else sits in it (fuzz N). It ends a Travels with, as Travels with ends the eyes."""
    if cam is None or cam.type != 'CAMERA':
        return False
    st = scene.bb_st
    con = cam.constraints.get(EYES_CON)
    world = _evaluated_matrix(cam, _scene_depsgraph(scene))     # where it really is, constraint and all
    if char is None:
        aims = eyes_aims(cam)
        uid, _secs = step_off(cam)
        i = beat_index_of(st, uid) if uid else None
        poses = sample_beat_poses(scene) if (len(st.beats) and eyes_helper(cam) is not None) else None
        rows = poses.get(cam.name) if poses is not None else None
        if rows is not None:
            ref = cam.rotation_euler.copy()
            last = len(st.beats) - 1 if i is None else i
            for j, b in enumerate(list(st.beats)[:last + 1]):     # the shot it had in the eyes becomes its own poses
                m = eyes_world(cam, b.frame)
                if m is None:
                    continue
                for k in range(3):
                    if ("location", k) in rows[j]:
                        rows[j][("location", k)] = m.translation[k]
                if aims:
                    rot = m.to_euler('XYZ', ref)
                    ref = rot
                    for k in range(3):
                        if ("rotation_euler", k) in rows[j]:
                            rows[j][("rotation_euler", k)] = rot[k]
        if con is not None:
            cam.constraints.remove(con)
        _drop_fcurves(cam, {EYES_INF})
        for key in (EYES_KEY, EYES_OWN_KEY):
            if key in cam:
                del cam[key]
        cam.location = world.to_translation()
        if aims:
            cam.rotation_euler = world.to_euler('XYZ', cam.rotation_euler)
        for h in stage_objects(scene, roles=(EYES_ROLE,)):      # nobody left in these eyes: the helper goes
            if not helper_used(h, rig_cams(scene)):
                bpy.data.objects.remove(h)
        if rows is not None:
            relayout_only(scene, [cam], poses)
        return True
    if any(r.owner == cam for r in st.paths):
        return False
    set_ride(scene, cam, None)                   # a camera is either somebody's eyes or travels with somebody
    old = eyes_helper(cam)
    h = ensure_eyes_helper(scene, char)
    if con is None:
        con = cam.constraints.new('COPY_LOCATION')   # 0.18: the eyes carry it, the aim stays its own (0.19: so its
        con.name = EYES_CON                          # rotation is left as it is; copying the world one, Looks at and
    con.target = h                                   # all, made a move nobody saved)
    con.influence = 1.0
    order_cam_rig(cam)
    if old is not None and old != h and not helper_used(old, rig_cams(scene)):
        bpy.data.objects.remove(old)
    if not cam_moves(cam):
        set_cam_moves(scene, cam, True)          # the pose it lands in is a beat pose like any other
    stepped = EYES_OWN_KEY in cam
    cam[EYES_KEY] = [0, STEP_OFF_S]
    if stepped and len(st.beats):
        relayout_only(scene, [cam])     # the beat it stepped off on gets its own pose back
    apply_eyes(scene)
    return True


def step_off(cam):
    """(beat uid, seconds) of this camera's hand-off; uid 0: it stays in the eyes to the end."""
    rec = cam.get(EYES_KEY) if cam is not None else None
    try:
        return int(rec[0]), float(rec[1])
    except Exception:
        return 0, STEP_OFF_S


def set_step_off(scene, cam, uid=None, secs=None):
    old_uid, old_s = step_off(cam)
    cam[EYES_KEY] = [int(old_uid if uid is None else uid), float(max(0.1, old_s if secs is None else secs))]
    if step_off(cam)[0] and not cam_moves(cam):
        set_cam_moves(scene, cam, True)       # it needs beat poses to fly to once it lets go
    if len(scene.bb_st.beats) and step_off(cam)[0] != old_uid:
        relayout_only(scene, [cam])     # the new step-off beat takes the eyes' place, the old one its own
    else:
        apply_eyes(scene)


def eyes_world(cam, frame):
    """Where the camera sits and looks while it is in the eyes, on this frame — read from the keys, so no
    playhead has to move to find out."""
    h = eyes_helper(cam)
    if h is None:
        return None
    p = h.parent
    m = _eyes_local(h, keyed_location_at(h, frame), Euler(keyed_rotation_at(h, frame)),
                    pose_at(p, frame) if p is not None else None)
    if p is not None:
        pm = Matrix.LocRotScale(keyed_location_at(p, frame), _with_drift(p, Euler(keyed_rotation_at(p, frame)), frame),
                                p.scale)
        m = pm @ h.matrix_parent_inverse @ m
    return m


def _eyes_local(h, loc, rot, pose):
    """An Eyes helper's own matrix from its keyed place and turn, with its character's posture on top (the
    drivers on its delta location and delta X turn, ensure_eyes_posture): Blender adds the delta location and
    turns by the delta rotation after its own."""
    post = eyes_posture(h, pose) if pose is not None else None
    r = Euler(rot).to_matrix()
    if post is not None:
        loc = Vector(loc) + post[0]
        r = Matrix.Rotation(post[1], 3, 'X') @ r
    return Matrix.LocRotScale(Vector(loc), r, h.scale)


EYES_POSE_KEY = "bbst_eyes_pose"   # on an Eyes helper: [y, z, hip, lie offset, sit offset] its posture drivers were
                                   # built for (0.19 wrote one rest offset: [y, z, hip, offset])
_EYES_POSE_EXPR = (
    ("delta_location", 1, "{y}*(cos(t)-1)-({zh})*sin(t)"),
    ("delta_location", 2, "{y}*sin(t)+({zh})*(cos(t)-1)+(s+{os}+({ol}-{os})*abs(sin(t))-{hip})*r"),
    ("delta_rotation_euler", 0, "t"),
)


def eyes_posture(h, pose):
    """(delta location, delta X turn) that carry an Eyes helper where its character's sit or lie puts his eyes:
    the peg torso's turn about the hip and lift onto the seat. None when the helper has no posture drivers."""
    k = h.get(EYES_POSE_KEY) if h is not None else None
    if k is None or len(k) not in (4, 5) or pose is None:
        return None
    k = [float(x) for x in k]
    y, z, hip, off = k[:4]
    t = float(pose.get("bbst_tilt", 0.0))
    c, s = math.cos(t), math.sin(t)
    zh = z - hip
    off = rest_offset(k[4], off, t) if len(k) == 5 else off
    lift = (float(pose.get("bbst_seat", POSE_NEUTRAL["bbst_seat"])) + off - hip) * float(pose.get("bbst_rest", 0.0))
    return Vector((0.0, y * (c - 1.0) - zh * s, y * s + zh * (c - 1.0) + lift)), t


def ensure_eyes_posture(h):
    """0.19 integration (s3 poses x s2 Eyes of): an Eyes helper sits and lies down with its character. Drivers
    on its delta location (Y, Z) and delta X turn read the peg's pose channels (Lie back, Seat height, Resting);
    its own place and turn stay keyed on the beats (the gaze). Standing they add exactly nothing. A character
    without joints gets none (and loses stale ones). Cheap when in place; True when something changed."""
    if h is None or h.get(ROLE_KEY) != EYES_ROLE:
        return False
    char = h.parent
    want = None
    if is_peg(char):
        d = peg_dims(peg_height_of(char), peg_width_of(char))
        loc = [float(h.location[k]) for k in range(3)]
        for fc in id_fcurves(h):        # its keyed place (the first key), not wherever the playhead has it
            if fc.data_path == "location" and fc.array_index in (1, 2) and len(fc.keyframe_points):
                loc[fc.array_index] = float(fc.keyframe_points[0].co.y)
        want = [round(loc[1], 6), round(loc[2], 6), round(d["hip"], 6), round(d["rest_off"], 6), round(d["sit_off"], 6)]
    have = h.get(EYES_POSE_KEY)
    drivers = {(fc.data_path, fc.array_index): fc for fc in (h.animation_data.drivers if h.animation_data else [])}
    if want is None and have is None:
        return False
    ok = (want is not None and have is not None and [round(float(x), 6) for x in have] == want
          and all((pth, i) in drivers for pth, i, _e in _EYES_POSE_EXPR)
          and all(v.targets[0].id == char for pth, i, _e in _EYES_POSE_EXPR for v in drivers[(pth, i)].driver.variables))
    if ok:
        return False
    for pth, i, _e in _EYES_POSE_EXPR:
        if (pth, i) in drivers:
            h.driver_remove(pth, i)
        getattr(h, pth)[i] = 0.0
    if want is None:
        if EYES_POSE_KEY in h:
            del h[EYES_POSE_KEY]
        return True
    y, z, hip, off, off_sit = want
    for pth, i, expr in _EYES_POSE_EXPR:
        fc = h.driver_add(pth, i)
        drv = fc.driver
        drv.type = 'SCRIPTED'
        drv.expression = expr.format(y=repr(y), zh=repr(round(z - hip, 6)), ol=repr(off), os=repr(off_sit),
                                     hip=repr(hip))
        used = drv.expression.replace("cos", "").replace("sin", "").replace("abs", "")
        for name, prop in (("t", "bbst_tilt"), ("s", "bbst_seat"), ("r", "bbst_rest")):
            if name in used:
                var = drv.variables.new()
                var.name = name
                var.type = 'SINGLE_PROP'
                var.targets[0].id_type = 'OBJECT'
                var.targets[0].id = char
                var.targets[0].data_path = f'["{prop}"]'
    h[EYES_POSE_KEY] = want
    return True


def _with_drift(ob, rot, frame):
    """A rotation with the object's life-in-the-holds drift (its delta rotation) on top, as Blender applies it:
    leaving the eyes kept everything but that drift, a centimetre at the eyes (fuzz K)."""
    d = Euler([(lambda fc: fc.evaluate(frame) if fc is not None else ob.delta_rotation_euler[k])(
        _curve(ob, "delta_rotation_euler", k)) for k in range(3)])
    if max(abs(x) for x in d) < 1e-9:
        return rot.to_matrix()
    return d.to_matrix() @ rot.to_matrix()


def _eyes_world_in(poses, cam, i, frame):
    """eyes_world on beat i, read from beat poses about to be written (a pose just saved counts)."""
    h = eyes_helper(cam)
    if h is None:
        return None

    def pose(ob):
        rows = poses.get(ob.name)
        if rows is None:
            return keyed_location_at(ob, frame), Euler(keyed_rotation_at(ob, frame))
        r = rows[i]
        return (Vector([r.get(("location", k), ob.location[k]) for k in range(3)]),
                Euler([r.get(("rotation_euler", k), ob.rotation_euler[k]) for k in range(3)]))
    loc, rot = pose(h)
    p = h.parent
    posture = None
    if p is not None:
        posture = pose_at(p, frame)
        rows = poses.get(p.name)
        if rows is not None:            # a sit or a lie just saved on this beat counts too
            posture.update({prop: rows[i][(path, 0)] for path, prop in POSE_PATHS.items() if (path, 0) in rows[i]})
    m = _eyes_local(h, loc, rot, posture)
    if p is not None:
        ploc, prot = pose(p)
        m = Matrix.LocRotScale(ploc, _with_drift(p, prot, frame), p.scale) @ h.matrix_parent_inverse @ m
    return m


def _move_key(fc, frame, value):
    """Put this curve's key on this frame at a value, handles and all (the blocking writes flat handles:
    they travel with the key)."""
    for kp in fc.keyframe_points:
        if int(round(kp.co.x)) == int(frame):
            dy = value - kp.co.y
            kp.co.y = value
            kp.handle_left.y += dy
            kp.handle_right.y += dy
            return
    fc.keyframe_points.insert(float(frame), float(value))


def eyes_poses(scene, poses, only=None):
    """Before a layout: every POV camera's own pose on its step-off beat is the pose it has in the eyes there,
    so when it lets go it is already exactly where we were watching from, and only the flight to the next beat
    is left to show. 0.19: written into the beat poses, not stamped onto the keys afterwards, so the moves on
    either side are derived like any other and the beats around it keep their holds (fuzz C: the stamp bent
    the next hold and the camera never reached its own pose). When the step-off moves, the beat it left gets
    back the pose that was there before (audit r2 M4: the camera flew through the head)."""
    st = scene.bb_st
    for cam in stage_cams(scene):
        rows = poses.get(cam.name)
        if rows is None or (only is not None and cam.name not in only):
            continue                    # not re-keyed this time: its keys (and what it remembers) stay as they are
        con = cam.constraints.get(EYES_CON)
        uid = step_off(cam)[0] if (con is not None and eyes_helper(cam) is not None) else 0
        i = beat_index_of(st, uid) if uid else None
        own = cam.get(EYES_OWN_KEY)
        if own is not None:
            try:
                own_uid, own_loc = int(own[0]), [float(x) for x in list(own)[1:4]]
            except Exception:
                own_uid, own_loc = 0, []
            if i is None or own_uid != uid:
                k = beat_index_of(st, own_uid) if own_uid else None
                if k is not None and len(own_loc) == 3:
                    for n in range(3):
                        if ("location", n) in rows[k]:
                            rows[k][("location", n)] = own_loc[n]
                del cam[EYES_OWN_KEY]
        if i is None:
            continue
        m = _eyes_world_in(poses, cam, i, st.beats[i].frame)
        if m is None:
            continue
        if EYES_OWN_KEY not in cam:
            cam[EYES_OWN_KEY] = [float(uid)] + [float(rows[i].get(("location", n), cam.location[n])) for n in range(3)]
        for n in range(3):
            if ("location", n) in rows[i]:
                rows[i][("location", n)] = m.translation[n]
        if con.type == 'COPY_TRANSFORMS':        # the 0.17 rig also decided where it pointed
            ref = Euler([rows[i].get(("rotation_euler", n), 0.0) for n in range(3)])
            rot = m.to_euler('XYZ', ref)
            for n in range(3):
                if ("rotation_euler", n) in rows[i]:
                    rows[i][("rotation_euler", n)] = rot[n]


def apply_eyes(scene):
    """Keep every POV camera's hand-off on its beat: it holds the eyes until its step-off beat and is free a
    second later. Its own pose on that beat is part of the beat poses (eyes_poses); no other beat of the
    camera is touched: the pose you park for it to land on stays yours."""
    st = scene.bb_st
    f = fps(scene)
    for cam in stage_cams(scene):
        con = cam.constraints.get(EYES_CON)
        if con is None or eyes_helper(cam) is None:
            continue
        uid, secs = step_off(cam)
        i = beat_index_of(st, uid) if uid else None
        _drop_fcurves(cam, {EYES_INF})
        if i is None:
            con.influence = 1.0
            continue
        f0 = st.beats[i].frame
        f1 = max(f0 + 1, f0 + int(round(max(0.1, secs) * f)))
        for fr, v in ((f0, 1.0), (f1, 0.0)):
            con.influence = v
            cam.keyframe_insert(EYES_INF, frame=fr, group="BB Stage eyes")
        fc = _curve(cam, EYES_INF)
        for kp in (fc.keyframe_points if fc is not None else ()):
            kp.interpolation = 'BEZIER'
            kp.handle_left_type = kp.handle_right_type = 'AUTO_CLAMPED'     # it leaves gently and settles gently


def set_zoom(scene, cam, on):
    """Zoom on: the lens becomes part of every beat (change it on a beat and that beat keeps it), and the
    camera moves on the beats. Off: one lens for the whole staging, the one it has now."""
    if cam is None or cam.type != 'CAMERA':
        return
    st = scene.bb_st
    if on:
        if not cam_moves(cam):
            set_cam_moves(scene, cam, True)
        # its place and turn are keyed first: the lens curve alone would count as its beat keys, and a camera
        # given Zoom before its first Save Beat never had its moves keyed (fuzz M)
        ensure_beat_keys(scene, cam)
        for b in st.beats:
            for f in sorted({b.frame, beat_out(b)}):
                cam.data.keyframe_insert("lens", frame=f, group="BB Stage")
        have = block_channels(cam)          # a camera never keyed yet (just added) gets its pose keyed too, where it
        if len(st.beats):                   # stands — never a lens without a place (fuzz bug M, keys-incomplete)
            f0 = st.beats[_clamped_beat(st)].frame
            for path in _BLOCK_PATHS:
                for k in range(3):
                    if (path, k) not in have:
                        cam.keyframe_insert(path, index=k, frame=f0, group="BB Stage")
    elif lens_fcurve(cam) is not None:
        lens = cam.data.lens
        _drop_fcurves(cam.data, {"lens"})
        cam.data.lens = lens


def _lens_mm_set(self, v):
    """The lens field of the panel and the pane header. On a camera that zooms, the beat at the playhead
    takes the new lens (anywhere else the change would be lost on the next frame).

    0.19: that beat and only that beat: the lens is written as its beat pose, so the beats either side keep
    theirs and its hold stays one lens. Keying the two frames alone left the neighbouring beats without keys,
    and the curve bent through them (audit r2 M7, fuzz C: 35 mm on B2 became 54.7)."""
    lens = float(min(300, max(8, v)))
    scene = getattr(bpy.context, "scene", None)
    i = None
    if (_curve(self, "lens") is not None and scene is not None and is_staging(scene)
            and len(scene.bb_st.beats)):
        i = beat_at_frame(scene)
    cam = next((o for o in stage_cams(scene) if o.data == self), None) if i is not None else None
    if cam is None:
        self.lens = lens
        return
    keep_unsaved(scene, [cam])          # its own unsaved move at the playhead is saved first, never thrown away
    self.lens = lens
    poses = sample_beat_poses(scene)
    rows = poses.get(cam.name)
    if rows is None or LENS_CH not in rows[i]:
        return
    rows[i][LENS_CH] = lens
    relayout_only(scene, [cam], poses)


# ------------------------------------------------------------------ camera rigs stay their own (0.19)
#
# A camera's helpers (its aim, the helper it travels on) belong to it by pointer. A Shift+D copy of a camera
# used to share them: the copy turned the original towards its own target, and setting the copy to stand free
# deleted the helper the original was riding, which then jumped 6 m (audit r2 M3). Deleting a camera left its
# aim keyed on every save and its cuts on the timeline under a dead name (audit r4 M5, fuzz I); deleting a
# character threw the camera in his eyes 3.5 m and left the cameras that looked at him staring at the world
# origin (fuzz K, audit r2 M2). Here is what keeps all of that in order.

_TIDY = {"busy": False}


def relayout_only(scene, obs, poses=None):
    """Re-key these objects from their beat poses: a camera control changes its camera (and its aim), and
    nobody else's keys are rewritten, so nobody's unsaved move is thrown away.

    The poses given are everybody's (the full sample): Natural moves times every move from everybody who moves
    in it (who leads, who follows a beat later), so planning from these objects alone re-timed the aim's moves on
    every beat, the picture differing by 10 degrees until the next Save Beat put the old timing back (review of
    0.19 s2). The keys written are exactly the ones a full re-key would give them."""
    poses = sample_beat_poses(scene) if poses is None else poses
    write_beat_layout(scene, poses, only={o.name for o in obs if o is not None})


def _off_its_keys(ob, f):
    """s1's test (off_key_channels): a whole number of turns is no move, a never-keyed object never off its keys."""
    return ob is not None and _off_keys(ob, f)


def keep_unsaved(scene, obs=None):
    """A camera control that re-keys these objects first saves an unsaved (orange) move at the playhead when one
    of them is standing off its keys, the way a beat click does, so the move is never thrown away. Everybody
    else's unsaved moves are left alone: since 0.19 a camera control re-keys only its own camera and aim."""
    st = scene.bb_st if is_staging(scene) else None
    if st is None or not len(st.beats):
        return
    i = beat_at_frame(scene)
    if i is None or not (st.beats[i].dirty or _TOUCHED.get(_sid(scene))):
        return
    if obs is None or any(_off_its_keys(o, scene.frame_current) for o in obs):
        save_unsaved(scene)             # s1's save-first: only what was moved is written, into the playhead's beat


def _set_name(thing, want, unique=True):
    """Rename an object or a marker to want, unless it is already that (or that cut short by Blender's name
    length) or, for an object, the name is taken. True when it changed."""
    cur = thing.name
    if cur == want or (want.startswith(cur) and len(cur.encode("utf-8")) >= 60):
        return False
    if unique and bpy.data.objects.get(want) is not None:
        return False
    thing.name = want
    return thing.name != cur


def _remove_helper(ob):
    act = ob.animation_data.action if ob.animation_data else None
    bpy.data.objects.remove(ob)
    if act is not None and act.users == 0:
        bpy.data.actions.remove(act)


def _own_copy(helper, name):
    """A copy of a shared helper for another camera: constraints, keys (its own action) and collections."""
    new = helper.copy()
    if OWNER_KEY in new:
        del new[OWNER_KEY]
    ad = helper.animation_data
    if ad is not None and ad.action is not None:
        new.animation_data.action = ad.action.copy()
    for c in helper.users_collection:
        c.objects.link(new)
    _set_name(new, name)
    return new


# The name each camera had at the last tidy-up, by session id: a camera renamed in the Outliner takes along the
# cuts that were called after its old name, and nothing else (a cut Aman named himself keeps its name).
_CAM_NAMES = {}


def _cut_names_follow(scene, cams):
    changed = False
    for cam in cams:
        key = getattr(cam, "session_uid", None) or cam.as_pointer()
        old = _CAM_NAMES.get(key)
        _CAM_NAMES[key] = cam.name
        if old is None or old == cam.name:
            continue
        for m in scene.timeline_markers:
            if m.camera == cam and m.name == f"{CUT_PREFIX}{old}":
                changed = _set_name(m, f"{CUT_PREFIX}{cam.name}", unique=False) or changed
    if len(_CAM_NAMES) > 4096:
        _CAM_NAMES.clear()
    return changed


def _riders_follow_names(cam):
    """A look-table entry is a rider key (its constraint's target decides who is tracked), and it is kept reading
    as that object's name: after a rename the rider constraint and the table follow, the way helpers and cuts
    follow their camera. Nothing tracks anybody else for it (the pointer already decided that); it keeps the table
    readable, and code that still reads it by name (0.18 files, a staging split) finds the right object. A key
    another rider already holds is left as it is."""
    aim = aim_of(cam)
    if aim is None:
        return False
    ren = {}
    for key, c in rider_cons(aim).items():
        t = c.target
        if t is None:
            continue
        want = AIM_CON + t.name
        if c.name == want or (want.startswith(c.name) and len(c.name.encode("utf-8")) >= 60):
            continue
        if aim.constraints.get(want) is not None:
            continue
        c.name = want                       # Blender moves its influence keys along (checked in 5.2)
        new = c.name[len(AIM_CON):]
        if new != key:
            ren[key] = new
    if ren:
        table = look_table(cam)
        if table:
            cam[LOOK_KEY] = {str(u): ren.get(v, v) for u, v in table.items()}
    return bool(ren)


def tidy_camera_rigs(scene, names=True, deep=True):
    """Keep every camera's helpers its own and nothing left over:
      - a camera sharing an aim or a ride helper with another (a Shift+D copy) gets its own copy of it, keys and
        all, so neither picture changes and neither can take the other's away;
      - aims and ride helpers no camera uses any more go, so do eyes nobody sits in;
      - eyes whose character is gone let their cameras go (they fall back to their own keys);
      - deep: a camera riding somebody who is gone stands free where it is (this re-keys the staging);
      - names: helpers and "CUT" markers follow their camera's (or character's) name, look-table entries the
        name of whoever they track.
    Safe to run often: it writes only what is wrong. True when it changed anything."""
    if not is_staging(scene) or _TIDY["busy"]:
        return False
    _TIDY["busy"] = True
    try:
        return _tidy_camera_rigs(scene, names, deep)
    finally:
        _TIDY["busy"] = False


def _tidy_camera_rigs(scene, names, deep):
    changed = False
    cams = rig_cams(scene)              # nested shot collections too: their rigs are theirs (review of 0.19 s2)
    for getter, prefix in ((aim_of, "Aim · "), (ride_helper, "Ride · ")):
        groups = {}
        for cam in cams:
            h = getter(cam)
            if h is not None:
                groups.setdefault(h.as_pointer(), (h, []))[1].append(cam)
        for h, users in groups.values():
            if len(users) < 2:
                continue
            keeper = helper_keeper(h, users, prefix)
            for cam in users:
                if cam == keeper:
                    continue
                new = _own_copy(h, f"{prefix}{cam.name}")
                if getter is aim_of:
                    cam.constraints[LOOK_CON].target = new
                else:
                    inv = cam.matrix_parent_inverse.copy()
                    cam.parent = new
                    cam.matrix_parent_inverse = inv     # setting .parent from Python resets it: the copy jumped
                changed = True                          # by where its character stood when the ride was set
    for cam in cams:                                # eyes of somebody who is gone: nothing left to carry it
        h = eyes_helper(cam)
        if h is not None and not _alive_in(scene, h.parent):
            con = cam.constraints.get(EYES_CON)
            if con is not None:
                cam.constraints.remove(con)
            _drop_fcurves(cam, {EYES_INF})
            for key in (EYES_KEY, EYES_OWN_KEY):
                if key in cam:
                    del cam[key]
            changed = True
    used = {AIM_ROLE: {aim_of(c).as_pointer() for c in cams if aim_of(c) is not None},
            RIDE_ROLE: {c.parent.as_pointer() for c in cams if ride_helper(c) is not None},
            EYES_ROLE: {eyes_helper(c).as_pointer() for c in cams if eyes_helper(c) is not None}}
    for ob in stage_objects(scene, roles=(AIM_ROLE, RIDE_ROLE, EYES_ROLE)):
        if ob.as_pointer() not in used[ob.get(ROLE_KEY)] and not _used_anywhere(ob):
            _remove_helper(ob)
            changed = True
    if deep:
        for cam in stage_cams(scene):
            if ride_helper(cam) is not None and not _alive_in(scene, ride_target(cam)):
                set_ride(scene, cam, None)
                changed = True
    if names:
        cams = rig_cams(scene)
        for cam in cams:
            for h, prefix in ((aim_of(cam), "Aim · "), (ride_helper(cam), "Ride · ")):
                if h is not None:
                    changed = _set_name(h, f"{prefix}{cam.name}") or changed
            changed = _riders_follow_names(cam) or changed
        for h in stage_objects(scene, roles=(EYES_ROLE,)):
            if h.parent is not None:
                changed = _set_name(h, f"Eyes · {h.parent.name}") or changed
        changed = _cut_names_follow(scene, cams) or changed
    return changed


def tick_camera_rigs(scene):
    """Watchdog: a Shift+D copy of a camera gets its own helpers at once, and names follow a rename."""
    return tidy_camera_rigs(scene)


def release_camera(scene, cam):
    """Before a camera is deleted: its aim and the helper it travels on go with it, and so do eyes nobody else
    sits in, unless another camera still uses them; its cuts leave the timeline (a cut marker of a deleted
    camera did nothing but sit there under a dead name). A beat marker it was bound to keeps its beat and loses
    only the cut."""
    others = [c for c in rig_cams(scene) if c != cam]
    aim, ride, eyes = aim_of(cam), ride_helper(cam), eyes_helper(cam)
    if ride is not None:
        cam.parent = None
        if not any(c.parent == ride for c in others):
            _remove_helper(ride)
    if aim is not None and not any(aim_of(c) == aim for c in others):
        _remove_helper(aim)
    if eyes is not None and not any(eyes_helper(c) == eyes for c in others):
        _remove_helper(eyes)
    for m in list(scene.timeline_markers):
        if m.camera == cam:
            if m.name.startswith(CUT_PREFIX):
                scene.timeline_markers.remove(m)
            else:
                m.camera = None


def release_target(scene, ob):
    """Before a character or prop is deleted, every camera keeps its picture: a camera in his eyes comes out
    where it is, beat by beat (it used to drop 3.5 m to the world origin); a camera travelling with him stands
    free where it is; a camera that looked at him goes on looking at the places he was, beat by beat, as its
    aim point (it used to swing onto the origin). A helper deleted by itself (scripts can) lets its cameras
    go first, so none is left with a constraint on nothing."""
    st = scene.bb_st
    role = ob.get(ROLE_KEY)
    if role in (EYES_ROLE, RIDE_ROLE, AIM_ROLE):
        for cam in stage_cams(scene):
            if role == EYES_ROLE and eyes_helper(cam) == ob:
                set_eyes(scene, cam, None)
            elif role == RIDE_ROLE and cam.parent == ob:
                set_ride(scene, cam, None)
            elif role == AIM_ROLE and aim_of(cam) == ob:
                con = cam.constraints.get(LOOK_CON)
                _drop_fcurves(cam, {f'constraints["{LOOK_CON}"].influence'})
                if con is not None:
                    cam.constraints.remove(con)
                if LOOK_KEY in cam:
                    del cam[LOOK_KEY]
        return
    for cam in stage_cams(scene):
        if eyes_target(cam) == ob:
            set_eyes(scene, cam, None)
    clear_rides_of(scene, ob)
    todo = []
    for cam in stage_cams(scene):
        aim = aim_of(cam)
        keys = {k for k, c in rider_cons(aim).items() if c.target == ob}
        table = look_table(cam)
        if keys and any(v in keys for v in table.values()):
            ensure_beat_keys(scene, aim)
            todo.append((cam, aim, keys, table))
    if not todo or not len(st.beats):
        return
    poses = sample_beat_poses(scene)
    for cam, aim, keys, table in todo:
        rows = poses.get(aim.name)
        for j, s in enumerate(look_states(scene, cam, table)):
            if s in keys and rows is not None:
                p = _aim_point(scene, cam, s, rows[j], st.beats[j].frame)
                if p is not None:
                    for k in range(3):
                        rows[j][("location", k)] = p[k]
        cam[LOOK_KEY] = {str(u): ("" if v in keys else v) for u, v in table.items()}
    relayout_only(scene, [t[1] for t in todo], poses)


def camera_refs_before_beat_delete(scene, i):
    """Beat i is about to be deleted: what cameras tied to it moves to a neighbour, so nothing silently changes
    meaning (audits r4 L9, r2 L5). A Looks-at set on it now starts on the next beat, unless that one has its own,
    so every beat left keeps its look; a step-off on it happens on the beat before (on the first beat: the next
    one) instead of silently becoming "never"."""
    st = scene.bb_st
    if not (0 <= i < len(st.beats)):
        return
    uid = st.beats[i].uid
    nxt = st.beats[i + 1].uid if i + 1 < len(st.beats) else None
    prv = st.beats[i - 1].uid if i > 0 else None
    for cam in stage_cams(scene):
        table = look_table(cam)
        if uid in table:
            v = table.pop(uid)
            if nxt is not None and nxt not in table:
                table[nxt] = v
            cam[LOOK_KEY] = {str(k): x for k, x in table.items()}
        s_uid, secs = step_off(cam)
        if s_uid and s_uid == uid:
            cam[EYES_KEY] = [int(prv if prv is not None else (nxt or 0)), float(secs)]
        own = cam.get(EYES_OWN_KEY)
        try:
            if own is not None and int(own[0]) == uid:
                del cam[EYES_OWN_KEY]
        except Exception:
            pass


def _migrate_v11_s2(scene):
    """0.19 load step (s2-cameras): every camera's Track To goes last in its stack (audit r2 H4). An owner pointer
    a pre-release 0.19 build stored on aims and ride helpers is dropped: it counted as a user of the camera.
    Idempotent and cheap, so it runs on every load; it renames nothing and removes no object, so opening a file
    changes no name and no object."""
    if not is_staging(scene):
        return
    for h in stage_objects(scene, roles=(AIM_ROLE, RIDE_ROLE)):
        if OWNER_KEY in h:
            del h[OWNER_KEY]
    for cam in stage_cams(scene):
        order_cam_rig(cam)
    _cut_names_follow(scene, rig_cams(scene))   # notes every camera's name: a rename from here on takes its cuts


def prune_moves(scene):
    """Drop hand-set timings whose character or beat is gone."""
    st = scene.bb_st
    uids = {b.uid for b in list(st.beats)[1:]}
    for k in reversed(range(len(st.moves))):
        m = st.moves[k]
        if m.owner is None or scene.objects.get(m.owner.name) != m.owner or m.beat_uid not in uids:
            st.moves.remove(k)


def relayout_beats(scene):
    """A Move or Hold time changed: keep every beat's pose, re-time everything."""
    if _QUIET["beats"] or not (is_staging(scene) and len(scene.bb_st.beats)):
        return
    st = scene.bb_st
    save_unsaved(scene)                     # unsaved moves are kept, never thrown away
    _QUIET["beats"] = True
    try:
        write_beat_layout(scene, sample_beat_poses(scene))
    finally:
        _QUIET["beats"] = False
    scene.frame_set(st.beats[_clamped_beat(st)].frame)
    settle_unsaved(scene)


def _beat_time_update(self, context):
    scene = self.id_data
    if isinstance(scene, bpy.types.Scene):
        relayout_beats(scene)


def _pre_v09_beats(st):
    """Beats timed by their frames (before v0.9): no beat knows where it leaves. Only a staging older than version
    9 can have them; and a B1 on frame 0 with no hold leaves on frame 0 without being one (audit r1 bug 16: the
    old test wiped every Hold of such a staging on each load)."""
    beats = list(st.beats)
    return (st.data_version < 9 and bool(beats) and all(b.frame_out == 0 for b in beats)
            and any(b.frame != 0 for b in beats))


def upgrade_beats(scene):
    """Stagings made before v0.9 timed beats by their frames: turn the gaps into Move times."""
    st = scene.bb_st
    if not _pre_v09_beats(st):
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


def follow_studio_space(scene):
    """However the studio space moves (a handle, a drag, G, Place Studio Space), everything
    standing in it moves with it, live (Aman, 5 Oct 2026). Width/depth changes are not moves:
    resize_studio records the new centre itself."""
    if _QUIET["carry"]:
        return
    b = boundary_of(scene)
    if b is None:
        return
    st = scene.bb_st
    x, y, z = b.location.x, b.location.y, b.location.z
    if not st.bound_xy_set:
        st.bound_xy = (x, y)
        st.bound_z = z
        st.bound_xy_set = True
        return
    dx, dy = x - st.bound_xy[0], y - st.bound_xy[1]
    # with Floors off the studio's height is free (a city has no floors to snap to): a move up
    # or down carries everything too. With Floors on the detected floor sets the height.
    dz = 0.0 if st.use_floors else z - st.bound_z
    if st.use_floors and abs(st.bound_z - z) > 1e-6:
        st.bound_z = z
    if abs(dx) < 1e-6 and abs(dy) < 1e-6 and abs(dz) < 1e-6:
        _snap_selected(scene)
        return
    _QUIET["carry"] = True
    try:
        carry_with_studio(scene, Vector((dx, dy, dz)), skip_selected=True)
        st.bound_xy = (x, y)
        if not st.use_floors:
            st.bound_z = z
            st.floor_z = z
    finally:
        _QUIET["carry"] = False
        _snap_selected(scene)


# The selected objects as they stood after the last look at the studio space (0.19.1): when the space moves, a
# selected object that moved by the same amount was dragged along with it (G on a selection), one that did not move
# was only selected (the space's Location typed in the N panel) and is carried like everything else. VERIFY_0.19
# found the second case left a selected camera and its keys behind while its character moved 2.9 m with the studio.
_SEL_SNAP = {}


def _selected_in(scene):
    out = {}
    for vl in scene.view_layers:
        try:
            for o in vl.objects.selected:
                out[_sid(o)] = o
        except Exception:
            pass
    return out


def _snap_selected(scene):
    try:
        sel = _selected_in(scene)
        _SEL_SNAP[_sid(scene)] = {k: o.location.copy() for k, o in sel.items()}
    except Exception:
        _SEL_SNAP.pop(_sid(scene), None)


def _was_dragged(scene, ob, d):
    """Did this selected object move along with the studio space (by d), or was it only selected? Read from where
    it stood at the last look (_SEL_SNAP), else from where its keys hold it; neither known: dragged (as before)."""
    before = _SEL_SNAP.get(_sid(scene), {}).get(_sid(ob))
    if before is None and block_channels(ob):
        before = keyed_location_at(ob, scene.frame_current)
    if before is None:
        return True
    moved = ob.location - before
    return (moved - d).length <= moved.length


def floor_selects_space(scene, view_layer):
    """Clicking the studio floor selects the studio space (they are one thing)."""
    if view_layer is None:
        return
    floors = [o for o in view_layer.objects.selected if is_studio_floor(o)]
    if not floors:
        return
    b = boundary_of(scene)
    if b is None:
        return
    was_active = view_layer.objects.active in floors
    for f in floors:
        f.select_set(False, view_layer=view_layer)
    if b.hide_select or not b.visible_get(view_layer=view_layer):
        return
    b.select_set(True, view_layer=view_layer)
    if was_active:
        view_layer.objects.active = b


def preview_follow(scene):
    """The preview pane shows the scene camera. Panes are in local view, and Blender does not sync a
    local-view pane's camera to scene.camera (the marker cuts), so this copies it over on every frame."""
    cam = scene.camera
    if cam is None:
        return
    for win in stage_windows():
        if win.scene != scene:
            continue
        a = stage_panes(win).get("CAM0")
        if a is None:
            continue
        sp = a.spaces.active
        if not sp.use_local_camera:
            sp.use_local_camera = True
        if sp.camera != cam:
            sp.camera = cam
            a.tag_redraw()


_PATH_FOCUS = {}        # scene name: the beat its paths are currently shown for


def _bbst_settle_dirty():
    """A frame change has just re-read every beat key, so the unsaved moves on keyed channels are gone: the
    badges are worked out again from what still stands off its keys at the new playhead (only something never
    keyed yet). Runs on a timer, never inside the frame handler (see _bbst_on_frame)."""
    try:
        wm = bpy.context.window_manager
        scenes = {w.scene for w in wm.windows} if wm else set()
        for scene in scenes:
            if is_staging(scene) and len(scene.bb_st.beats) and has_unsaved(scene):
                settle_unsaved(scene)
    except Exception as e:
        print("BB Stage unsaved badge:", e)
    return None


@persistent      # an add-on's handlers must survive File > Open (Blender drops the others on every load)
def _bbst_on_frame(scene):
    try:
        if scene is not None and is_staging(scene):
            preview_follow(scene)
            # the paths follow the playhead onto the beat it lands on — but never from in here:
            # changing visibility inside a frame-change handler re-tags the depsgraph mid-evaluation
            # and Blender 5.2 dies on it. Ask for a sync instead, which runs on a timer.
            if len(scene.bb_st.paths) and _PATH_FOCUS.get(scene.name) != focus_beat(scene):
                request_sync(0.0)
            # the frame change re-read the keys: an orange badge may now be stale (same rule: a timer)
            scr = getattr(bpy.context, "screen", None)
            if (has_unsaved(scene) and not (scr is not None and scr.is_animation_playing)
                    and not bpy.app.timers.is_registered(_bbst_settle_dirty)):
                bpy.app.timers.register(_bbst_settle_dirty, first_interval=0.0)
    except Exception as e:
        print("BB Stage preview:", e)


def note_moves(scene, depsgraph):
    """The depsgraph handler's part of the unsaved state: every staged object this update touched — not only the
    first one (a camera that Looks at an aim point, or rides somebody, is updated along with what was moved and
    can come first in the list) — goes into _TOUCHED while it stands off its keys at the playhead, and out again
    when it is back on them (a single Reset to keys clears the badge too). A lens typed in Blender's own camera
    properties counts for a camera that zooms on the beats."""
    stage = {_sid(ob): ob for ob in keyed_objects(scene)}
    seen = set()
    for up in depsgraph.updates:
        idb = up.id
        if isinstance(idb, bpy.types.Object):
            if up.is_updated_transform and _sid(idb) in stage:
                seen.add(_sid(idb))
        elif isinstance(idb, bpy.types.Camera):
            seen.update(n for n, ob in stage.items() if ob.type == 'CAMERA' and ob.data is not None
                        and _sid(ob.data) == _sid(idb) and LENS_CH in block_channels(ob))
    if not seen:
        return
    f = scene.frame_current
    touched = _TOUCHED.setdefault(_sid(scene), set())
    before = set(touched)
    for n in seen:
        if _off_keys(stage[n], f):
            touched.add(n)
        else:
            touched.discard(n)
    st = scene.bb_st
    i = beat_at_frame(scene)
    stale = (bool(touched) != (st.unsaved_between or (i is not None and st.beats[i].dirty))
             or any(b.dirty for j, b in enumerate(st.beats) if j != i))
    if touched != before or stale:
        _apply_unsaved(scene)


@persistent      # without this the orange "unsaved" badge died on the first File > Open of a session
def _bbst_on_depsgraph(scene, depsgraph):
    """Mark the beat at the playhead orange when a staged object moves off its saved keys."""
    if scene is not None and is_staging(scene) and not _QUIET["carry"]:
        try:
            follow_studio_space(scene)
        except Exception as e:
            print("BB Stage studio follow:", e)
        try:
            floor_selects_space(scene, depsgraph.view_layer)
        except Exception as e:
            print("BB Stage floor select:", e)
        try:
            part_selects_piece(scene, depsgraph.view_layer)
            _guard_set_moves(scene, depsgraph)
        except Exception as e:
            print("BB Stage set edits:", e)
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
        if not _QUIET["saving"]:
            note_moves(scene, depsgraph)
    except Exception as e:
        print("BB Stage unsaved check:", e)


def _beat_label_update(self, context):
    sync_markers(context.scene)


def beat_top_speed(scene, i):
    """Fastest character between beat i and i+1, in m/s (walking tops out ~1.5)."""
    st = scene.bb_st
    if i >= len(st.beats) - 1:
        return None
    f0, f1 = beat_out(st.beats[i]), st.beats[i + 1].frame
    if f1 <= f0:
        return None
    worst = None
    for ob in stage_objects(scene, roles=("char",)):
        ad = ob.animation_data
        if not (ad and ad.action):
            continue
        w0, w1 = move_window(scene, ob, i + 1)      # Natural moves: the part of the move it really walks in
        secs = (w1 - w0) / fps(scene)
        p0, p1 = [0, 0], [0, 0]
        for fc in channelbag_fcurves(ad.action):
            if fc.data_path == "location" and fc.array_index in (0, 1):
                p0[fc.array_index] = fc.evaluate(f0)
                p1[fc.array_index] = fc.evaluate(f1)
        rec = path_for(scene, ob, st.beats[i + 1].uid)
        dist = path_length(rec) if rec is not None else math.hypot(p1[0] - p0[0], p1[1] - p0[1])
        v = dist / secs
        if worst is None or v > worst[1]:
            worst = (ob.name, v)
    return worst


# ------------------------------------------------------------------ paths (drawn moves)
#
# Aman, 5 Oct 2026: a character (or a prop) can walk a drawn Bezier path into a beat instead of
# the straight move, e.g. Jai's single walk down the Dharavi gully. The beat poses stay the
# truth: the path's two ends sit on them (move the character on a beat and the end follows).
# During the move a hidden follower rides the curve; the walker copies its position and
# heading, so the rotation follows the curve. The beat keys themselves are never touched,
# except the arrival heading, which faces along the path.

PATH_ROLE, FOLLOWER_ROLE = "path", "path_follower"
PATH_CON = "BB Path"
_PATH_EDITING = set()       # names of path curves in Edit Mode at the last watchdog tick


def ensure_beat_uids(scene):
    """Beats get a lasting id, so a path stays with its beat when earlier beats are deleted."""
    st = scene.bb_st
    seen = set()
    top = max([b.uid for b in st.beats] + [st.next_uid - 1, 0])
    for b in st.beats:
        if b.uid <= 0 or b.uid in seen:
            top += 1
            b.uid = top
        seen.add(b.uid)
    if st.next_uid <= top:
        st.next_uid = top + 1


def beat_index_of(st, uid):
    for i, b in enumerate(st.beats):
        if b.uid == uid:
            return i
    return None


def path_for(scene, ob, uid):
    for rec in scene.bb_st.paths:
        if ob is not None and rec.owner == ob and rec.beat_uid == uid:
            return rec
    return None


def path_of_curve(scene, curve):
    for rec in scene.bb_st.paths:
        if curve is not None and rec.curve == curve:
            return rec
    return None


def paths_coll(scene):
    c = sub_coll(scene, "STAGE", "Paths")
    roots = layer_colls(scene, "STAGE")
    if c is None and roots:
        c = bpy.data.collections.new(f"Paths · {staging_label(scene)}")
        c[SUB_KEY] = "Paths"
        roots[0].children.link(c)
    return c


def keyed_location_at(ob, frame):
    """Where the beat keys put this object on a frame (never a frame jump: unsaved moves stay)."""
    loc = ob.location.copy()
    ad = ob.animation_data
    for fc in (channelbag_fcurves(ad.action) if ad and ad.action else []):
        if fc.data_path == "location" and 0 <= fc.array_index < 3:
            loc[fc.array_index] = fc.evaluate(frame)
    return loc


def keyed_rotation_at(ob, frame):
    rot = ob.rotation_euler.copy()
    ad = ob.animation_data
    for fc in (channelbag_fcurves(ad.action) if ad and ad.action else []):
        if fc.data_path == "rotation_euler" and 0 <= fc.array_index < 3:
            rot[fc.array_index] = fc.evaluate(frame)
    return rot


def reset_to_keys(scene, obs=None, frame=None):
    """Put staged objects back where their beat keys hold them on this frame: unsaved moves are dropped
    (Aman, 10 Oct 2026). Returns how many moved."""
    f = scene.frame_current if frame is None else frame
    n = 0
    for ob in (obs if obs is not None else keyed_objects(scene)):
        ad = ob.animation_data
        if not (ad and ad.action):
            continue
        loc, rot = keyed_location_at(ob, f), keyed_rotation_at(ob, f)
        posed = reset_pose_to_keys(ob, f)       # a sit or a lie that was not saved goes too (0.19)
        if (loc - ob.location).length > 1e-5 or any(abs(a - b) > 1e-5 for a, b in zip(rot, ob.rotation_euler)):
            ob.location, ob.rotation_euler = loc, rot
            n += 1
        elif posed:
            n += 1
        fc = lens_fcurve(ob)
        if fc is not None and abs(ob.data.lens - fc.evaluate(f)) > 1e-5:
            ob.data.lens = fc.evaluate(f)       # a zooming camera's lens is part of its pose too
            n += 1
    if getattr(scene, "bb_st", None) is not None and frame is None:
        settle_unsaved(scene)       # the badge goes out when nothing is left off its keys (also after one Reset)
    return n


def path_window(st, i):
    """The move into beat i: from the frame beat i-1 is left to the frame beat i is reached."""
    return beat_out(st.beats[i - 1]), st.beats[i].frame


def _path_names(owner, i):
    return f"Path · {owner.name} → B{i + 1}", f"Path follower · {owner.name} → B{i + 1}"


def _con_names(uid):
    return f"{PATH_CON} · {uid} · Loc", f"{PATH_CON} · {uid} · Rot"


def _bez_points(rec):
    cu = rec.curve.data if rec.curve is not None else None
    if cu is None or not len(cu.splines) or cu.splines[0].type != 'BEZIER':
        return None
    return cu.splines[0].bezier_points


def path_length(rec):
    try:
        return rec.curve.data.splines[0].calc_length()
    except Exception:
        return 0.0


def path_world_points(rec, per_seg=12):
    pts = _bez_points(rec)
    if pts is None or len(pts) < 2:
        return []
    off = rec.curve.location.copy()
    out = []
    for a, b in zip(pts[:-1], pts[1:]):
        p0, p1, p2, p3 = a.co.copy(), a.handle_right.copy(), b.handle_left.copy(), b.co.copy()
        for k in range(per_seg):
            t = k / per_seg
            u = 1.0 - t
            out.append(off + p0 * u ** 3 + p1 * (3 * u * u * t) + p2 * (3 * u * t * t) + p3 * t ** 3)
    out.append(off + pts[-1].co)
    return out


CAM_PATH_RGBA = (1.0, 0.72, 0.15, 1.0)     # camera moves read amber in the plan


def path_color(owner):
    return CAM_PATH_RGBA if owner.type == 'CAMERA' else tuple(owner.color)


def _write_keys(ob, data_path, pts, interp):
    """Make one F-curve hold exactly these keys; True when something changed."""
    ad = ob.animation_data
    fc = None
    if ad and ad.action:
        fc = next((f for f in channelbag_fcurves(ad.action) if f.data_path == data_path), None)
    if fc is None:
        ob.keyframe_insert(data_path, frame=pts[0][0], group="BB Path")
        fc = next((f for f in channelbag_fcurves(ob.animation_data.action) if f.data_path == data_path), None)
        if fc is None:
            return False
    want = [(int(f), round(float(v), 5)) for f, v in pts]
    cur = [(int(round(k.co.x)), round(k.co.y, 5)) for k in fc.keyframe_points]
    if cur == want and all(k.interpolation == interp for k in fc.keyframe_points):
        return False
    while len(fc.keyframe_points):
        fc.keyframe_points.remove(fc.keyframe_points[-1], fast=True)
    fc.keyframe_points.add(len(want))
    for kp, (f, v) in zip(fc.keyframe_points, want):
        kp.co = (f, v)
        kp.interpolation = interp
        kp.handle_left_type = kp.handle_right_type = 'AUTO_CLAMPED'
    fc.update()
    return True


def _drop_fcurves(ob, data_paths):
    ad = ob.animation_data
    if not (ad and ad.action):
        return
    for layer in ad.action.layers:
        for strip in layer.strips:
            for cb in strip.channelbags:
                for fc in [f for f in cb.fcurves if f.data_path in data_paths]:
                    cb.fcurves.remove(fc)


def _face_path_update(rec, context):
    scene = rec.id_data
    if not isinstance(scene, bpy.types.Scene):
        return
    i = beat_index_of(scene.bb_st, rec.beat_uid)
    if i:
        time_path(scene, rec, i)
        if rec.face_path:
            set_arrival_heading(scene, rec, i)
        if scene.bb_st.natural:
            rebuild_blocking(scene)


def time_path(scene, rec, i):
    """Key the walk on the beat timing: the follower goes 0 → 1 along the curve over the move
    (a short start and stop, steady in between); the walker follows it from the frame after
    it leaves beat i-1 until it lands on beat i, and turns into and out of the path heading."""
    st = scene.bb_st
    s, e = move_window(scene, rec.owner, i)      # Natural moves: the walk can start late and land early
    span = e - s
    loc_n, rot_n = _con_names(rec.beat_uid)
    owner, fol = rec.owner, rec.follower
    offset = f'constraints["{PATH_CON}"].offset_factor'
    if span < 3:       # too quick to walk anything: the path rests, the move stays straight
        _write_keys(fol, offset, [(s, 0.0)], 'LINEAR')
        _write_keys(owner, f'constraints["{loc_n}"].influence', [(s, 0.0)], 'CONSTANT')
        _write_keys(owner, f'constraints["{rot_n}"].influence', [(s, 0.0)], 'CONSTANT')
        return
    f = fps(scene)
    a = max(1, min(round(0.6 * f), span // 4))
    v = 1.0 / (span - a)
    _write_keys(fol, offset, [(s, 0.0), (s + a, v * a / 2), (e - a, 1.0 - v * a / 2), (e, 1.0)], 'BEZIER')
    _write_keys(owner, f'constraints["{loc_n}"].influence', [(s, 0.0), (s + 1, 1.0), (e, 0.0)], 'CONSTANT')
    r = max(1, min(round(0.3 * f), span // 3))
    if rec.face_path:
        _write_keys(owner, f'constraints["{rot_n}"].influence',
                    [(s, 0.0), (s + r, 1.0), (e - r, 1.0), (e, 0.0)], 'LINEAR')
    else:       # keeps the framing keyed on the beats
        _write_keys(owner, f'constraints["{rot_n}"].influence', [(s, 0.0)], 'CONSTANT')


def fit_path(scene, rec, i):
    """Pin the path's ends on the walker's beat poses (their handles ride along)."""
    pts = _bez_points(rec)
    if pts is None or len(pts) < 2:
        return False
    s, e = path_window(scene.bb_st, i)
    off = rec.curve.location.copy()
    changed = False
    for bp, world in ((pts[0], keyed_location_at(rec.owner, s)), (pts[-1], keyed_location_at(rec.owner, e))):
        d = (world - off) - bp.co
        if d.length > 1e-4:
            bp.handle_left = bp.handle_left + d
            bp.handle_right = bp.handle_right + d
            bp.co = bp.co + d
            changed = True
    return changed


def path_heading_end(rec):
    pts = _bez_points(rec)
    if pts is None or len(pts) < 2:
        return None
    t = pts[-1].co - pts[-1].handle_left
    if t.length < 1e-5:
        t = pts[-1].co - pts[-2].co
    return math.atan2(-t.x, t.y) if t.length > 1e-6 else None


def set_arrival_heading(scene, rec, i):
    """The walker lands on beat i facing along the end of its path. True when the heading changed."""
    if not rec.face_path:
        return False
    th = path_heading_end(rec)
    ob = rec.owner
    ad = ob.animation_data
    fc = next((f for f in channelbag_fcurves(ad.action)
               if f.data_path == "rotation_euler" and f.array_index == 2), None) if (ad and ad.action) else None
    if th is None or fc is None:
        return False
    b = scene.bb_st.beats[i]
    cur = fc.evaluate(b.frame)
    th = cur + ((th - cur + math.pi) % (2 * math.pi) - math.pi)      # the short way round
    if abs(th - cur) > 1e-5:
        pin_beat_keys(scene, fc)        # the other beats keep their facing (fuzz bug C)
    changed = False
    for f in sorted({b.frame, beat_out(b)}):
        kp = next((k for k in fc.keyframe_points if abs(k.co.x - f) < 0.5), None)
        if kp is None:
            fc.keyframe_points.insert(f, th)
            changed = True
        elif abs(kp.co.y - th) > 1e-5:
            d = th - kp.co.y
            kp.co.y = th
            kp.handle_left.y += d       # a flat handle stays flat
            kp.handle_right.y += d
            changed = True
    fc.update()
    return changed


def _set_path_shape(rec, p0, mid, p1):
    cu = rec.curve.data
    off = rec.curve.location.copy()
    cu.splines.clear()
    sp = cu.splines.new('BEZIER')
    sp.bezier_points.add(2)
    for bp, co in zip(sp.bezier_points, (p0, mid, p1)):
        bp.handle_left_type = bp.handle_right_type = 'AUTO'
        bp.co = co - off


def _start_shape(ob, p0, p1):
    mid = (p0 + p1) / 2
    if (p1 - p0).length < 0.6:      # no distance yet: start a loop to drag out
        mid = mid + Matrix.Rotation(ob.rotation_euler.z, 3, 'Z') @ Vector((1.2, 0.0, 0.0))
    return mid


def create_path(scene, ob, i):
    st = scene.bb_st
    ensure_beat_uids(scene)
    uid = st.beats[i].uid
    coll = paths_coll(scene)
    s, e = path_window(st, i)
    p0, p1 = keyed_location_at(ob, s), keyed_location_at(ob, e)
    cname, fname = _path_names(ob, i)
    cu = bpy.data.curves.new(cname, 'CURVE')
    cu.dimensions = '3D'
    cu.resolution_u = 24
    cu.twist_mode = 'Z_UP'
    cu.use_path = True
    cu.bevel_depth = 0.03
    cu.bevel_resolution = 2
    cu.materials.append(ensure_flat_material(f"BB Path · {ob.name}", path_color(ob)))
    curve = bpy.data.objects.new(cname, cu)
    curve[ROLE_KEY] = PATH_ROLE
    curve.color = path_color(ob)
    curve.hide_render = True
    curve.lock_location = (True, True, True)
    curve.lock_rotation = (True, True, True)
    curve.lock_scale = (True, True, True)
    coll.objects.link(curve)
    fol = bpy.data.objects.new(fname, None)
    fol[ROLE_KEY] = FOLLOWER_ROLE
    fol.empty_display_size = 0.2
    fol.hide_render = True
    fol.hide_select = True
    coll.objects.link(fol)
    fp = fol.constraints.new('FOLLOW_PATH')
    fp.name = PATH_CON
    fp.target = curve
    fp.use_curve_follow = True
    fp.use_fixed_location = True
    fp.forward_axis = 'FORWARD_Y'
    fp.up_axis = 'UP_Z'
    loc_n, rot_n = _con_names(uid)
    cl = ob.constraints.new('COPY_LOCATION')
    cl.name = loc_n
    cl.target = fol
    cl.use_z = ob.get(ROLE_KEY) != "char"       # characters stay on the floor
    cr = ob.constraints.new('COPY_ROTATION')
    cr.name = rot_n
    cr.target = fol
    cr.use_x = cr.use_y = False                 # turn only: walkers stay upright, cameras keep their tilt
    cl.influence = cr.influence = 0.0
    rec = st.paths.add()
    rec.owner, rec.curve, rec.follower, rec.beat_uid = ob, curve, fol, uid
    rec["face_path"] = ob.get(ROLE_KEY) != "cam"     # a camera keeps its framing unless asked
    _set_path_shape(rec, p0, _start_shape(ob, p0, p1), p1)
    time_path(scene, rec, i)
    set_arrival_heading(scene, rec, i)
    order_cam_rig(ob)                           # a camera that Looks at somebody aims from the path, not before it
    apply_path_focus(scene)
    return rec


def remove_path(scene, k):
    st = scene.bb_st
    rec = st.paths[k]
    owner, curve, fol, uid = rec.owner, rec.curve, rec.follower, rec.beat_uid
    if owner is not None:
        names = _con_names(uid)
        for n in names:
            c = owner.constraints.get(n)
            if c is not None:
                owner.constraints.remove(c)
        _drop_fcurves(owner, {f'constraints["{n}"].influence' for n in names})
    for ob in (fol, curve):
        if ob is None:
            continue
        data = ob.data
        act = ob.animation_data.action if ob.animation_data else None
        _PATH_EDITING.discard(ob.name)
        bpy.data.objects.remove(ob)
        if data is not None and data.users == 0:
            bpy.data.curves.remove(data)
        if act is not None and act.users == 0:
            bpy.data.actions.remove(act)
    st.paths.remove(k)


def _strip_stray_path_constraints(scene):
    """A Shift+D copy of a walker carries its path constraints: only real owners keep them."""
    for ob in stage_objects(scene, roles=("char", "prop")) + stage_cams(scene):
        for c in list(ob.constraints):
            if not c.name.startswith(PATH_CON + " · "):
                continue
            try:
                uid = int(c.name.split(" · ")[1])
            except (IndexError, ValueError):
                continue
            if path_for(scene, ob, uid) is None:
                _drop_fcurves(ob, {f'constraints["{c.name}"].influence'})
                ob.constraints.remove(c)


def refresh_paths(scene, edited=()):
    """Keep every path on its beats: drop the ones whose walker, curve or beat is gone, pin the
    ends on the beat poses, re-key the timing, face the arrival along the path. Writes only
    what changed, so it is safe to run often."""
    if not is_staging(scene):
        return False
    st = scene.bb_st
    turned = False
    if len(st.paths):
        ensure_beat_uids(scene)
    for k in reversed(range(len(st.paths))):
        rec = st.paths[k]
        i = beat_index_of(st, rec.beat_uid)
        alive = all(o is not None and scene.objects.get(o.name) == o
                    for o in (rec.owner, rec.curve, rec.follower))
        if not alive or not i:
            remove_path(scene, k)
            continue
        editing = rec.curve.mode == 'EDIT'
        moved = False if editing else fit_path(scene, rec, i)
        if not editing and (moved or rec.curve.name in edited):
            turned = bool(set_arrival_heading(scene, rec, i)) or turned
        time_path(scene, rec, i)
        if _rgba_differs(rec.curve.color, path_color(rec.owner)):
            rec.curve.color = path_color(rec.owner)
        cname, fname = _path_names(rec.owner, i)
        if rec.curve.name != cname and bpy.data.objects.get(cname) is None and not editing:
            rec.curve.name = cname
        if rec.follower.name != fname and bpy.data.objects.get(fname) is None:
            rec.follower.name = fname
    _strip_stray_path_constraints(scene)
    apply_path_focus(scene)
    return turned


def focus_beat(scene):
    """The beat the paths are shown for: the one the playhead sits on, or the one being moved into."""
    st = scene.bb_st
    f = scene.frame_current
    for i, b in enumerate(st.beats):
        if f <= beat_out(b) + 0.5:
            return i
    return len(st.beats) - 1 if len(st.beats) else None


def apply_path_focus(scene):
    """Aman, 13 Oct 2026: "whenever I select a beat, the paths that lead to that beat from the last beat
    should be visible ... the paths for the rest of the beats should disappear". With Paths: all, every
    drawn move is shown at once, which is how it was before.

    Never call this from a frame-change handler: it changes visibility, which re-tags the depsgraph."""
    st = scene.bb_st
    if not len(st.paths):
        return
    i = focus_beat(scene)
    _PATH_FOCUS[scene.name] = i
    uid = st.beats[i].uid if (i is not None and i < len(st.beats)) else None
    for rec in st.paths:
        show = (not st.path_focus) or rec.beat_uid == uid or (rec.curve is not None and rec.curve.mode == 'EDIT')
        for ob in (rec.curve, rec.follower):
            if ob is not None and ob.hide_viewport != (not show):
                ob.hide_viewport = not show


def _path_focus_update(self, context):
    scene = self.id_data
    if isinstance(scene, bpy.types.Scene) and is_staging(scene):
        apply_path_focus(scene)


def tick_paths(scene):
    """Watchdog: notice a path leaving Edit Mode (Tab or Done) and settle it."""
    edited = set()
    for rec in scene.bb_st.paths:
        c = rec.curve
        if c is None:
            continue
        if c.mode == 'EDIT':
            _PATH_EDITING.add(c.name)
        elif c.name in _PATH_EDITING:
            _PATH_EDITING.discard(c.name)
            edited.add(c.name)
    if refresh_paths(scene, edited) or (edited and scene.bb_st.natural):
        rebuild_blocking(scene)         # a reshaped path: another length, another arrival heading


# ------------------------------------------------------------------ properties

def _caption_redraw(self, context):
    scr = getattr(context, "screen", None)
    for a in (scr.areas if scr else []):
        if a.type == "VIEW_3D":
            a.tag_redraw()


def _black_outside_update(self, context):
    apply_passepartout(context.scene)   # defined further down; resolved at call time


def _natural_update(self, context):
    scene = self.id_data
    if isinstance(scene, bpy.types.Scene) and is_staging(scene):
        rebuild_blocking(scene)


def _alive_update(self, context):
    scene = self.id_data
    if isinstance(scene, bpy.types.Scene) and is_staging(scene):
        apply_alive(scene)


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
    note: bpy.props.StringProperty(name="Note", default="", update=_caption_redraw)
    dirty: bpy.props.BoolProperty(default=False)   # something moved on this beat and isn't saved
    uid: bpy.props.IntProperty(default=0)          # lasting id (paths hold on to it)


class BBST_Path(bpy.types.PropertyGroup):
    """One drawn move: this walker follows this curve into the beat with this id."""
    owner: bpy.props.PointerProperty(type=bpy.types.Object)
    curve: bpy.props.PointerProperty(type=bpy.types.Object)
    follower: bpy.props.PointerProperty(type=bpy.types.Object)
    beat_uid: bpy.props.IntProperty(default=0)
    face_path: bpy.props.BoolProperty(
        name="Face along path", default=True, update=lambda self, ctx: _face_path_update(self, ctx),
        description="Turn to face where the path goes. Off (cameras' default): keep the framing "
                    "set on the beats while travelling the path")


class BBST_Move(bpy.types.PropertyGroup):
    """Natural moves: the timing of one move (this character, prop or camera into this beat), set by hand."""
    owner: bpy.props.PointerProperty(type=bpy.types.Object)
    beat_uid: bpy.props.IntProperty(default=0)
    start_s: bpy.props.FloatProperty(
        name="Starts after (s)", default=0.0, min=0.0, soft_max=20.0, step=10, precision=2, update=_natural_update,
        description="Seconds it waits after the previous beat lets go before it starts to move")
    end_s: bpy.props.FloatProperty(
        name="Lands early (s)", default=0.0, min=0.0, soft_max=20.0, step=10, precision=2, update=_natural_update,
        description="Seconds before the beat at which it has arrived and settled")
    face: bpy.props.EnumProperty(name="Facing", update=_natural_update, default='AUTO', items=[
        ('AUTO', "Facing: auto", "A walk faces where it goes; a step of about a metre keeps its facing"),
        ('ALONG', "Faces where it goes", "Turn to the direction of travel, go, then turn to the final facing"),
        ('KEEP', "Keeps its facing", "Turn straight from the old facing to the new one: a sidestep, backing away")])


class BBST_SetEdit(bpy.types.PropertyGroup):
    """One set edit of a staging (0.19, Take into Staging): the set piece it took in, the staging's own copy,
    and the piece's lasting id (the wrappers that hide the original carry it too)."""
    set_id: bpy.props.StringProperty(default="")
    original: bpy.props.PointerProperty(type=bpy.types.Object)
    copy: bpy.props.PointerProperty(type=bpy.types.Object)


def _beat_index_update(self, context):
    """Clicking a beat row jumps the whole scene to that beat. Unsaved moves on the beat being
    left are saved first: the jump re-reads the keys and would wipe them."""
    st = self
    scene = self.id_data if isinstance(self.id_data, bpy.types.Scene) else context.scene
    if 0 <= st.beat_index < len(st.beats):
        save_unsaved(scene)            # also when re-clicking the active beat: frame_set re-reads the keys
        scene.frame_set(st.beats[st.beat_index].frame)
        apply_path_focus(scene)        # the paths of the beat we land on, and only those
        settle_unsaved(scene)


def _use_floors_update(self, context):
    """Floors on: detect this set's floors (first time) and stand the studio on one, with levels
    and the plan cut. Off: the studio stays where it is and moves freely, up and down too."""
    scene = self.id_data
    if not (isinstance(scene, bpy.types.Scene) and is_staging(scene)):
        return
    st = scene.bb_st
    b = boundary_of(scene)
    if st.use_floors:
        fs = floor_state(scene)
        if fs is not None and not floors_known(fs):
            store_floors(fs, scene)
        if b is not None:
            refresh_floor(scene)
            st.bound_z = b.location.z
    elif b is not None:
        st.bound_z = st.floor_z = b.location.z
        st.active_level = 'ALL'
    request_sync(0.0)


def _play_level_update(self, context):
    """Settings › Plays on: the studio floor follows the level."""
    scene = self.id_data
    if _QUIET["floor"] or not (isinstance(scene, bpy.types.Scene) and is_staging(scene)):
        return
    if boundary_of(scene) is not None:      # New Staging sets the floor itself
        refresh_floor(scene)
        request_sync(0.0)


# ------------------------------------------------------------------ the cast library (0.19)
#
# Aman, 15 Oct 2026: the core cast is built into the add-on (it ships to the team with it), a personal library on
# this PC holds the characters he adds or edits, and every .blend keeps a copy of the ones it uses, so a file
# opens right on any machine. Fixed colours: Jai blue, Shefali purple, Shemda yellow, Shaan Daar black. Adding a
# character = typing a name: the field offers the library's characters, and picking one brings its colour,
# height and width. Characters can be added, edited, saved to the library and LOCKED: a locked character can not
# be edited, and every file's copy follows the library (on load and on every sync); an unlocked copy keeps its
# own values until Revert to Library.

CAST_KEY = "bb_st_cast"             # on a character: the id of its cast entry ("" = deliberately none)
CAST_NAME_KEY = "bb_st_cast_name"   # and its cast name, so a lost cast copy can be rebuilt (cast_heal)
CAST_ENV = "BBST_CAST_LIBRARY"      # the personal library's path, when set (tests, or another library file)
CAST_FILE = "cast_library.json"
CAST_LIB_V = 2                      # 2 (s7): widths are the uniform peg's (side to side); 1 (0.19): the shoulder line
_CAST_W_UNSET = 0.33                # BBST_Cast.width's default: what an entry 0.19 never wrote a width for reads


def _srgb(r, g, b):
    """A colour as a colour picker shows it (display sRGB) -> the linear value an object's colour stores."""
    f = lambda c: c / 12.92 if c <= 0.04045 else ((c + 0.055) / 1.055) ** 2.4
    return (round(f(r), 4), round(f(g), 4), round(f(b), 4), 1.0)


# (id, name, colour, height m, width m side to side, notes, lock). Heights and widths are defaults for a NEW
# character, which Aman can change: adult men 1.72-1.78 m, women 1.58-1.65, teens about 1.60, children about 1.30.
# Width None: the standard peg's for the height (s7 review: 0.19's guessed builds made pegs of one height come out
# in six widths; Aman, 15 Oct 2026: "Make the body uniform like before"). Aman sets a build in Configure. The colours were picked apart from each other (CIE94 distance 13 or more for every pair) and from the
# studio's own colour code (white shell, grey kit, magenta props, pink stand-ins). Lock 'COLOR': Aman fixed these
# four colours (15 Oct 2026), so every file follows the library's colour, but the heights are guesses and stay
# each file's own (review of 15 Oct: opening Gossip Maze must not shrink Shefali by 12 cm).
CAST_BUILTIN = (
    ("jai", "Jai", _srgb(0.16, 0.40, 0.95), 1.76, None, "Lead. Blue is fixed (Aman, 15 Oct 2026)", 'COLOR'),
    ("shefali", "Shefali", _srgb(0.60, 0.25, 0.88), 1.63, None, "Lead. Purple is fixed (Aman, 15 Oct 2026)", 'COLOR'),
    ("shemda", "Shemda", _srgb(0.98, 0.86, 0.12), 1.70, None, "Jai's friend, slight. Yellow is fixed (Aman, 15 Oct 2026)",
     'COLOR'),
    ("shaan_daar", "Shaan Daar", _srgb(0.20, 0.20, 0.22), 2.13, None,
     "Ishaan's HomeGame avatar (2.13 m). Black is fixed (Aman, 15 Oct 2026), lifted a touch so it reads in solid view",
     'COLOR'),
    ("riya", "Riya", _srgb(0.96, 0.42, 0.40), 1.62, None, "Influencer", None),
    ("namrata", "Namrata", _srgb(0.05, 0.62, 0.60), 1.60, None, "", None),
    ("dwijal", "Dwijal", _srgb(0.55, 0.86, 0.15), 1.72, None, "Taken as a young man: change if not", None),
    ("mr_dubey", "Mr Dubey", _srgb(0.55, 0.34, 0.16), 1.70, None, "Dubey Computer Classes", None),
    ("kailash", "Kailash", _srgb(0.58, 0.08, 0.16), 1.74, None, "Shefali's father", None),
    ("ajit", "Ajit", _srgb(0.48, 0.50, 0.10), 1.72, None, "Jai's father", None),
    ("zarine", "Zarine", _srgb(0.98, 0.56, 0.08), 1.58, None, "Jai's mother", None),
    ("aunty", "Aunty", _srgb(0.80, 0.70, 0.45), 1.58, None, "Any aunty", None),
    ("student", "Student", _srgb(0.12, 0.45, 0.22), 1.60, None, "Extra, a teenager", None),
    ("gamer_boy", "Gamer Boy", _srgb(0.15, 0.80, 0.95), 1.55, None, "Extra", None),
    ("gamer_teen", "Gamer Teen", _srgb(0.60, 0.95, 0.75), 1.65, None, "Extra", None),
    ("footballer", "Footballer", _srgb(0.86, 0.10, 0.08), 1.60, None, "Extra, a teenager", None),
    ("extra", "Extra", _srgb(0.36, 0.30, 0.26), 1.72, None, "Extra, an adult", None),
    ("child", "Child", _srgb(0.98, 0.62, 0.66), 1.30, None, "Extra, about ten", None),
)
_CAST_FIELDS = ("name", "color", "height", "width", "sit_at", "lie_at", "notes", "locked", "colour_only", "updated")
_LOCKABLE = ("name", "color", "height", "width", "sit_at", "lie_at")     # what a full lock holds to the library
_LIB = {"path": None, "mtime": None, "data": None, "gen": 0}


def cast_library_path():
    """The personal library: env BBST_CAST_LIBRARY, else (a test run: env BBST_WORK, or a --factory-startup
    Blender) a file per Blender process under BBST_WORK (or the temp folder)/cast_libraries, else the extension's
    user folder when BB Stage is installed as an extension, else Blender's config/bb_stage."""
    p = os.environ.get(CAST_ENV)
    if p:
        return p
    work = os.environ.get("BBST_WORK")
    if not work and getattr(bpy.app, "factory_startup", False):
        import tempfile             # a --factory-startup Blender (tests, fuzzing, UI checks) is not Aman's session
        work = os.path.join(tempfile.gettempdir(), "bb_stage_tests")
    if work:            # test and fuzz runs never write the real library, and parallel runs never share one
        return os.path.join(work, "cast_libraries", f"cast_library.{os.getpid()}.json")
    base = None
    pkg = __package__ or ""
    if pkg.startswith("bl_ext."):
        try:
            base = bpy.utils.extension_path_user(pkg, create=True)
        except Exception:
            base = None
    if not base:
        try:
            base = bpy.utils.user_resource('CONFIG', path="bb_stage", create=True)
        except Exception:
            base = os.path.join(os.path.expanduser("~"), ".bb_stage")
    return os.path.join(base, CAST_FILE)


def _read_library(path, strict=False):
    try:
        with open(path, encoding="utf-8") as fh:
            data = json.load(fh)
    except FileNotFoundError:
        return []
    except Exception as e:
        if strict:
            raise ValueError(str(e))
        print("BB Stage cast library: could not read", path, "-", e)
        return []
    chars = data.get("characters", []) if isinstance(data, dict) else []
    chars = [c for c in chars if isinstance(c, dict) and c.get("id") and c.get("name")]
    try:
        v = int(data.get("bb_stage_cast_library", 1))
    except Exception:
        v = 1
    for c in chars:     # written by 0.19 (a version 1 file, no width_v mark): its widths were the shoulder line of
        try:            # the human-shaped peg. Marked one by one, so when a 0.19 Blender still open rewrites the file
            if v < 2 and c.get("width_v") != WIDTH_V and c.get("width"):    # as version 1, nothing converts twice
                c["width"] = round(width_from_019(c["width"], c.get("height", 1.72), str(c["id"])), 4)
        except Exception:
            c.pop("width", None)
        c["width_v"] = WIDTH_V
    return chars


def library_personal(force=False):
    """The personal library's characters, {id: dict}; read again only when the file changed."""
    path = cast_library_path()
    try:
        mt = os.path.getmtime(path)
    except OSError:
        mt = None
    if force or _LIB["data"] is None or _LIB["path"] != path or _LIB["mtime"] != mt:
        _LIB.update(path=path, mtime=mt, data={str(c["id"]): c for c in _read_library(path)}, gen=_LIB["gen"] + 1)
    return _LIB["data"]


def _cast_defaults(cid, name):
    return dict(id=cid, name=name, color=[0.5, 0.5, 0.5, 1.0], height=1.72, width=default_width(1.72),
                sit_at=SIT_AT, lie_at=LIE_AT, notes="", locked=False, colour_only=False, updated="", source='PERSONAL')


def library_entries(force=False):
    """The cast library: the built-in cast with the personal library on top (an edited built-in keeps its id).
    {id: dict(id, name, color, height, width, sit_at, lie_at, notes, locked, colour_only, updated, source)},
    source BUILTIN, EDITED (a built-in changed in the personal library) or PERSONAL. locked + colour_only: only
    the colour follows the library (the four fixed colours); locked alone: everything does."""
    out = {}
    for cid, name, col, h, w, notes, lock in CAST_BUILTIN:
        out[cid] = dict(id=cid, name=name, color=list(col), height=h, width=w or default_width(h), sit_at=SIT_AT,
                        lie_at=LIE_AT,
                        notes=notes, locked=bool(lock), colour_only=lock == 'COLOR', updated="", source='BUILTIN')
    for cid, c in library_personal(force).items():
        e = dict(out[cid]) if cid in out else _cast_defaults(cid, str(c["name"]))
        for k in _CAST_FIELDS:
            if k in c:
                e[k] = c[k]
        if "locked" in c and "colour_only" not in c:
            e["colour_only"] = False        # a lock Aman set himself holds everything
        e["source"] = 'EDITED' if cid in out else 'PERSONAL'
        out[cid] = e
    return out


def locked_fields(e):
    """The fields of a cast entry (the file's copy or a library dict) that follow the library: none, the colour
    alone, or all of them."""
    get = (lambda k, d=None: e.get(k, d)) if isinstance(e, dict) else (lambda k, d=None: getattr(e, k, d))
    if not get("locked", False):
        return ()
    return ("color",) if get("colour_only", False) else _LOCKABLE


def fully_locked(e):
    return e is not None and len(locked_fields(e)) > 1


def library_write(d):
    """Add or replace one character in the personal library (read fresh first: another Blender may have
    written it since). Returns the path, or raises OSError."""
    path = cast_library_path()
    try:
        chars = _read_library(path, strict=True)
    except ValueError:                  # a file nobody can read is kept aside, never overwritten
        import shutil
        shutil.copy2(path, f"{path}.unreadable-{_stamp().replace(':', '').replace(' ', '-')}")
        chars = []
    chars = [c for c in chars if str(c.get("id")) != d["id"]]
    chars.append(dict({k: d[k] for k in ("id",) + _CAST_FIELDS if k in d}, width_v=WIDTH_V))
    chars.sort(key=lambda c: str(c.get("name", "")).lower())
    folder = os.path.dirname(path)
    if folder:
        os.makedirs(folder, exist_ok=True)
    tmp = path + ".tmp"
    with open(tmp, "w", encoding="utf-8") as fh:
        json.dump({"bb_stage_cast_library": CAST_LIB_V,
                   "about": "BB Stage personal cast library: characters added or edited on this computer. "
                            "Colours are linear RGBA, heights and widths in metres (height: floor to the top of "
                            "the head; width: side to side at the widest).",
                   "characters": chars}, fh, indent=1, ensure_ascii=False)
    os.replace(tmp, path)
    library_personal(force=True)
    return path


def _stamp():
    import time
    return time.strftime("%Y-%m-%d %H:%M")


def _slug(name):
    s = re.sub(r"[^a-z0-9]+", "_", name.lower()).strip("_")
    return s or "character"


def file_cast():
    fs = fstate()
    return fs.cast if fs is not None else None


def _other_casts():
    """Cast copies left on set scenes that are not the file-level one (a set scene added that sorts first, or
    the one holding the cast deleted: fstate() moves). cast_heal brings them home."""
    m = master_scene()
    return [s.bb_st.cast for s in set_scenes(offered=False)
            if s != m and getattr(s, "bb_st", None) is not None and len(s.bb_st.cast)]


def cast_entry(cid):
    if not cid:
        return None
    for e in (file_cast() or []):
        if e.cid == cid:
            return e
    for cast in _other_casts():     # read-only fallback until the next sync moves it (drawing must not write)
        for e in cast:
            if e.cid == cid:
                return e
    return None


def _new_entry(cast):
    """A new entry in a cast copy: its width is today's (side to side), never 0.19's shoulder line."""
    e = cast.add()
    e.width_v = WIDTH_V
    return e


def cast_width_upgrade(cast):
    """s7: a cast copy written by 0.19 held the shoulder width of the human-shaped peg. Carry it over to the
    uniform peg once (width_from_019: 0.19's defaults and its built-in guesses become the default for the height,
    a typed width keeps its build), and give every entry its build. Returns how many entries changed."""
    n = 0
    _QUIET["cast"] = True
    try:
        for e in cast:
            if e.width_v < WIDTH_V:
                e.width = width_from_019(e.width, e.height, e.cid, unset=_CAST_W_UNSET)
                e.width_v = WIDTH_V
                e.build = 0.0
                n += 1
            if e.build <= 0.0:
                e.build = e.width / default_width(e.height)
    finally:
        _QUIET["cast"] = False
    return n


def _copy_entry(dst, src):
    _QUIET["cast"] = True
    try:
        for k in ("cid", "name", "notes", "updated"):
            setattr(dst, k, getattr(src, k))
        for k in ("height", "width", "sit_at", "lie_at", "width_v", "build"):
            setattr(dst, k, getattr(src, k))
        dst.color = tuple(src.color)
        dst.locked, dst.colour_only, dst.in_library = src.locked, src.colour_only, src.in_library
    finally:
        _QUIET["cast"] = False


def cast_heal():
    """Keep the file's cast copy whole when the scene holding it changes (review of 15 Oct): entries left on
    another set scene move to the file-level one, and a character whose cast id is in no copy any more (its
    scene was deleted, as the Dubey interior split deletes 'Dubey Kit') gets its entry back from the library
    and from the character itself (colour, height, width, seat heights: every character carries them).
    Writes data: never call it while drawing. Returns how many entries it brought back."""
    fs = fstate()
    if fs is None:
        return 0
    n = 0
    have = {e.cid for e in fs.cast}
    for cast in _other_casts():
        for src in cast:
            if src.cid and src.cid not in have:
                _copy_entry(_new_entry(fs.cast), src)
                have.add(src.cid)
                n += 1
        cast.clear()
    cast_width_upgrade(fs.cast)         # s7: a 0.19 copy's widths, once (before any character takes them)
    lost = {}
    for s in stagings():
        for ob in stage_objects(s, roles=("char",)):
            cid = ob.get(CAST_KEY)
            if cid and cid not in have and cid not in lost:
                lost[cid] = ob
    if lost:
        lib = library_entries()
        for cid, ob in lost.items():
            le = lib.get(cid)
            name = str(ob.get(CAST_NAME_KEY) or "") or (le["name"] if le is not None else
                                                         (" ".join(re.sub(r"\.\d{3}$", "", ob.name).split()) or cid))
            own = dict(name=name, color=list(ob.color), height=peg_height_of(ob), width=peg_width_of(ob),
                       sit_at=float(ob.get("bbst_sit_at", SIT_AT)), lie_at=float(ob.get("bbst_lie_at", LIE_AT)))
            e = _new_entry(fs.cast)
            _QUIET["cast"] = True
            try:
                e.cid = cid
            finally:
                _QUIET["cast"] = False
            if le is not None:
                _entry_set(e, le)
                for k in locked_fields(le):
                    own.pop(k, None)    # what the library holds comes from the library
            _entry_set(e, own)
            e.in_library = le is not None
            have.add(cid)
            n += 1
    if n:
        print(f"BB Stage cast: {n} cast entr{'y' if n == 1 else 'ies'} brought back to '{master_scene().name}'")
    return n


def cast_of(ob):
    """This character's cast entry in the file, or None."""
    return cast_entry(ob.get(CAST_KEY)) if ob is not None else None


def cast_name(ob):
    """The name the panels show for a character: its cast name, else the object's own name."""
    e = cast_of(ob)
    return e.name if e is not None else ob.name


def who_label(ob, scene=None):
    """The name a menu or a camera tag shows for somebody: the cast name ("Jai"), not the object's ("Jai.001", a
    split's or a copy's). When two characters of this staging share it, the object's name follows in brackets
    (0.19 integration: the Eyes of / Looks at / Travels with menus and the plan tags still showed Jai.001)."""
    if ob is None:
        return ""
    try:
        if ob.get(ROLE_KEY) != "char":
            return ob.name
        n = cast_name(ob)
    except Exception:
        return ob.name
    if n == ob.name:
        return n
    if scene is not None and is_staging(scene):
        if any(o != ob and cast_name(o) == n for o in stage_objects(scene, roles=("char",))):
            return f"{n} ({ob.name})"
    return n


def cast_by_name(name):
    """(the file's entry, the library's entry) with this name, ignoring case and spacing; either may be None."""
    k = " ".join(name.split()).lower()
    fe = next((e for e in (file_cast() or []) if e.name.lower() == k), None)
    le = next((e for e in library_entries().values() if e["name"].lower() == k), None)
    return fe, le


def entry_dict(e):
    return dict(id=e.cid, name=e.name, color=[round(float(c), 4) for c in e.color], height=round(e.height, 3),
                width=round(e.width, 3), sit_at=round(e.sit_at, 3), lie_at=round(e.lie_at, 3), notes=e.notes,
                locked=bool(e.locked), colour_only=bool(e.colour_only), updated=e.updated)


def _entry_set(e, d, fields=None):
    """Copy a library entry's values (all of them, or only these fields) into the file's copy without the
    per-field updates. True when a value changed."""
    changed = False
    want = (lambda k: k in d) if fields is None else (lambda k: k in d and k in fields)
    _QUIET["cast"] = True
    try:
        for k in ("name", "notes", "updated"):
            if want(k) and getattr(e, k) != str(d[k]):
                setattr(e, k, str(d[k]))
                changed = changed or k == "name"
        for k in ("height", "width", "sit_at", "lie_at"):
            if want(k) and abs(getattr(e, k) - float(d[k])) > 1e-5:
                setattr(e, k, float(d[k]))
                changed = True
        if want("width") or e.build <= 0.0:         # the build follows a width given; a height alone keeps it
            e.build = e.width / default_width(e.height)
        elif want("height") and abs(e.width - e.build * default_width(e.height)) > 1e-6:
            e.width = e.build * default_width(e.height)
            changed = True
        if want("color"):
            col = (list(d["color"]) + [1.0] * 4)[:4]
            if _rgba_differs(e.color, col):
                e.color = col
                changed = True
        if fields is None:
            if "locked" in d and e.locked != bool(d["locked"]):
                e.locked = bool(d["locked"])
            if "colour_only" in d and e.colour_only != bool(d["colour_only"]):
                e.colour_only = bool(d["colour_only"])
    finally:
        _QUIET["cast"] = False
    return changed


def _entry_differs(e, d, fields=_LOCKABLE):
    a = entry_dict(e)
    return (any(abs(a[k] - float(d.get(k, a[k]))) > 1e-4 for k in ("height", "width", "sit_at", "lie_at") if k in fields)
            or ("color" in fields and _rgba_differs(a["color"], (list(d.get("color", a["color"])) + [1.0] * 4)[:4]))
            or ("name" in fields and a["name"] != d.get("name", a["name"])))


def ensure_file_cast(le):
    """The file's copy of a library character, made from the library the first time the file uses it."""
    cast_heal()
    e = cast_entry(le["id"])
    if e is None:
        fs = fstate()
        e = _new_entry(fs.cast)
        _QUIET["cast"] = True
        try:
            e.cid = le["id"]
        finally:
            _QUIET["cast"] = False
        _entry_set(e, le)
        e.in_library = True
    return e


def new_file_cast(name, color, height, width):
    """A character the library does not have yet: it lives in this file until Save to Library."""
    cast_heal()
    fs = fstate()
    taken = {e.cid for e in fs.cast} | set(library_entries())
    base = _slug(name)
    cid, k = base, 2
    while cid in taken:
        cid, k = f"{base}_{k}", k + 1
    e = _new_entry(fs.cast)
    _QUIET["cast"] = True
    try:
        e.cid = cid
    finally:
        _QUIET["cast"] = False
    _entry_set(e, dict(name=name, color=list(color), height=height, width=width or default_width(height),
                       sit_at=SIT_AT, lie_at=LIE_AT, notes="", locked=False, colour_only=False, updated=_stamp()))
    e.in_library = False
    return e


def _recolor_material(ob):
    mat = _peg_mat(ob)
    if mat is None or not mat.name.startswith("BB Peg") or mat.users > 1:
        return
    if _rgba_differs(mat.diffuse_color, ob.color):
        mat.diffuse_color = tuple(ob.color)
    bsdf = next((n for n in mat.node_tree.nodes if n.type == 'BSDF_PRINCIPLED'), None) if mat.use_nodes else None
    if bsdf and _rgba_differs(bsdf.inputs['Base Color'].default_value, ob.color):
        bsdf.inputs['Base Color'].default_value = tuple(ob.color)


def apply_cast_to(ob, e):
    """One character takes its cast entry's colour, height, width and pose defaults. True when it changed."""
    if ob is None or e is None or ob.get(ROLE_KEY) != "char":
        return False
    changed = False
    if _rgba_differs(ob.color, e.color):
        ob.color = tuple(e.color)
        changed = True
    for k, v in (("bbst_sit_at", e.sit_at), ("bbst_lie_at", e.lie_at)):
        if abs(float(ob.get(k, -1.0)) - v) > 1e-6:
            ob[k] = float(v)
    if ob.get(CAST_NAME_KEY) != e.name:
        ob[CAST_NAME_KEY] = e.name
    if set_char_size(ob, e.height, e.width):     # only a peg is rebuilt: a hand-made body keeps its mesh
        changed = True
    if changed and ob.type == 'MESH':
        _recolor_material(ob)
    return changed


def apply_cast(e):
    """Every character of this cast entry, in every staging of the file, takes its values."""
    n = 0
    for ob in bpy.data.objects:
        if ob.get(CAST_KEY) == e.cid:
            n += bool(apply_cast_to(ob, e))
    if n:
        request_sync(0.0)
    return n


def _cast_height_update(self, context):
    """A new Height for a cast character: the whole model scales, his build (Width for the height) stays."""
    if not _QUIET.get("cast") and self.build > 0.0:
        _QUIET["cast"] = True
        try:
            self.width = self.build * default_width(self.height)
        finally:
            _QUIET["cast"] = False
    _cast_update(self, context)


def _cast_width_update(self, context):
    """A new Width: his build from now on (a later Height keeps it)."""
    if not _QUIET.get("cast"):
        self.build = self.width / default_width(self.height)
    _cast_update(self, context)


def _cast_update(self, context):
    if _QUIET.get("cast"):
        return
    fields = locked_fields(self)
    if fields:                              # locked: the library's values, whatever was typed
        le = library_entries().get(self.cid)
        if le is not None:
            _entry_set(self, le, fields)
    apply_cast(self)


def cast_sync_from_library(force=False):
    """Locked characters follow the library (all their values, or only the colour for the four fixed colours):
    on file load and whenever the library file changed. Unlocked copies keep their values. Returns how many
    characters changed."""
    cast_heal()
    fs = fstate()
    if fs is None or not len(fs.cast):
        return 0
    lib = library_entries(force)
    n = 0
    for e in fs.cast:
        le = lib.get(e.cid)
        if e.in_library != (le is not None):
            e.in_library = le is not None
        if le is None:
            continue
        if e.locked != bool(le.get("locked")) or e.colour_only != bool(le.get("colour_only")):
            _QUIET["cast"] = True
            try:
                e.locked = bool(le.get("locked"))
                e.colour_only = bool(le.get("colour_only"))
            finally:
                _QUIET["cast"] = False
        fields = locked_fields(e)
        if fields and _entry_differs(e, le, fields):
            _entry_set(e, le, fields)
            n += apply_cast(e)
    return n


_CAST_SEEN = {"gen": None}


def sync_cast(scene):
    """Run by every sync: the cast copy is kept whole, a changed library reaches the locked characters, and
    characters out of step with their entry (a colour set on the object, an undo) are brought back to it."""
    try:
        healed = cast_heal()
        library_personal()
        if healed or _CAST_SEEN["gen"] != _LIB["gen"]:
            _CAST_SEEN["gen"] = _LIB["gen"]
            cast_sync_from_library()
        for ob in stage_objects(scene, roles=("char",)):
            e = cast_of(ob)
            if e is not None:
                apply_cast_to(ob, e)
    except Exception as ex:
        print("BB Stage cast:", ex)


def cast_save(e):
    """Save the file's copy to the personal library (it is then offered in every file). A colour-fixed
    character keeps its fixed colour and stays colour-fixed."""
    e.updated = _stamp()
    library_write(entry_dict(e))
    e.in_library = True


def cast_revert(e):
    le = library_entries(force=True).get(e.cid)
    if le is None:
        return False
    _entry_set(e, le)
    apply_cast(e)
    return True


def cast_lock(e, on):
    """Lock (or unlock) a character in the library. Locking saves the file's copy first and holds every value;
    unlocking frees every value, the fixed colours too."""
    d = entry_dict(e)
    if not on:
        le = library_entries(force=True).get(e.cid)
        if le is not None:
            d = {k: le[k] for k in ("id",) + _CAST_FIELDS if k in le}
    d["locked"] = bool(on)
    d["colour_only"] = False
    d["updated"] = _stamp()
    library_write(d)
    _QUIET["cast"] = True
    try:
        e.locked = bool(on)
        e.colour_only = False
        e.updated = d["updated"]
    finally:
        _QUIET["cast"] = False
    e.in_library = True


_CAST_SEARCH = []      # Blender keeps only pointers into search results: hold on to them


def _lock_word(e):
    f = locked_fields(e)
    return "" if not f else (" · colour fixed" if f == ("color",) else " · locked")


def _cast_name_search(self, context, edit_text):
    """Add Character's name field: the cast as you type (this file's own characters first, then the library)."""
    q = " ".join((edit_text or "").split()).lower()
    rows, seen = [], set()
    # who is in this staging already: the suggestion says so (UX review of s5: a second Riya came without a word)
    here = set()
    scene = getattr(context, "scene", None)
    if scene is not None and is_staging(scene):
        here = {cast_name(o).lower() for o in stage_objects(scene, roles=("char",))}

    def mark(name):
        return " · already here" if name.lower() in here else ""
    for e in (file_cast() or []):
        rows.append((e.name, f"{e.height:.2f} m · in this file" + _lock_word(e) + mark(e.name)))
    for le in sorted(library_entries().values(), key=lambda d: d["name"].lower()):
        src = {"BUILTIN": "built in", "EDITED": "your library", "PERSONAL": "your library"}[le["source"]]
        rows.append((le["name"], f"{le['height']:.2f} m · {src}" + _lock_word(le) + mark(le["name"])))
    out = []
    for name, info in rows:
        k = name.lower()
        if k in seen or (q and q not in k):
            continue
        seen.add(k)
        out.append((name, info))
    _CAST_SEARCH[:] = out
    return out


def _cast_items(self, context):
    """Every cast character this file or the library has, for a character's cast link."""
    items = [("NONE", "None (this character only)", "Not a cast character: its own colour, height and width")]
    seen = set()
    for e in (file_cast() or []):
        items.append((e.cid, e.name, f"{e.height:.2f} m · in this file"))
        seen.add(e.cid)
    for le in sorted(library_entries().values(), key=lambda d: d["name"].lower()):
        if le["id"] not in seen:
            items.append((le["id"], le["name"], f"{le['height']:.2f} m · library"))
    _CAST_ITEMS[:] = items
    return _CAST_ITEMS


_CAST_ITEMS = []


def link_cast(ob, cid):
    """Make a character this cast character (or nobody: cid None/'NONE'). It takes the entry's values."""
    if cid in (None, "", "NONE"):
        ob[CAST_KEY] = ""
        return None
    e = cast_entry(cid)
    if e is None:
        le = library_entries().get(cid)
        if le is None:
            return None
        e = ensure_file_cast(le)
    ob[CAST_KEY] = e.cid
    apply_cast_to(ob, e)
    request_sync(0.0)
    return e


CAST_MIGRATED = "bbst_cast_v"      # on a staging: its characters were linked to the cast (0.19), once
CAST_NOTE = "BB Stage · cast upgrade (0.19)"   # a text in the file: what the upgrade linked and what it left alone


def cast_base_name(name):
    """The cast name inside an object name: Blender's suffix first ('Jai.001'), then a number ('Gamer Boy 2',
    'Gamer Boy 1.001')."""
    return " ".join(re.sub(r"\s+\d+$", "", re.sub(r"\.\d{3}$", "", name)).split())


def _note_upgrade(scene, lines):
    if not lines:
        return
    for ln in lines:
        print("BB Stage cast upgrade:", ln)
    try:
        t = bpy.data.texts.get(CAST_NOTE) or bpy.data.texts.new(CAST_NOTE)
        if not t.as_string().strip():
            t.write("BB Stage 0.19 linked the characters of older stagings to the cast library. Nothing changed\n"
                    "colour, height or width except the fixed colours of Jai, Shefali, Shemda and Shaan Daar; characters\n"
                    "that would have changed were left unlinked (link them in Configure Character > cast).\n\n")
        t.write(f"{staging_label(scene)}\n" + "".join(f"  {ln}\n" for ln in lines))
    except Exception:
        pass


def _migrate_v11_s3(scene):
    """0.19 cast, once per staging (at load, before DATA_VERSION 11): characters made before the cast library are
    linked to it by name ('Jai', 'Jai.001', 'Jai 2' alone in a staging are all Jai). Opening an old file changes
    nobody (review of 15 Oct), except the four colours Aman fixed:
    * The file's copy starts from the character as the file has him (colour, height as drawn, width); only what the
      library locks (the fixed colour; everything for a character Aman locked himself) comes from the library.
    * Several characters of one name in one staging ('Gamer Boy 1' green and 'Gamer Boy 2' red) are different
      people unless they look the same: when their colours or heights differ they stay unlinked, each his own.
    * A character that would have to change colour or height to join the entry another staging already made
      stays unlinked too. Everything left alone is listed in the text 'BB Stage · cast upgrade (0.19)'.
    A character added later is never linked behind Aman's back (a 'Character 5' renamed to 'Shefali' stays his)."""
    st = scene.bb_st
    if fstate() is None or st.data_version >= 11 or scene.get(CAST_MIGRATED):
        return
    cast_heal()
    groups = {}
    for ob in stage_objects(scene, roles=("char",)):
        if CAST_KEY in ob:
            continue
        fe, le = cast_by_name(cast_base_name(ob.name))
        if fe is None and le is None:
            continue
        key = fe.cid if fe is not None else le["id"]
        groups.setdefault(key, [fe, le, []])[2].append(ob)
    notes = []
    for key, (fe, le, obs) in groups.items():
        names = ", ".join(o.name for o in obs)
        hs = [peg_height_of(o) for o in obs]
        ws = [peg_width_of(o) for o in obs]     # s7: a 0.18 peg's width is its own too (the 0.18 peg's for its height)
        if len(obs) > 1 and (any(_rgba_differs(obs[0].color, o.color, 0.01) for o in obs[1:])
                             or max(hs) - min(hs) > 0.005 or max(ws) - min(ws) > 0.005):
            for o in obs:
                o[CAST_KEY] = ""
            notes.append(f"{names}: different people (colours or heights differ), kept apart and unlinked")
            continue
        lockf = locked_fields(fe if fe is not None else le)
        if fe is None:
            fe = ensure_file_cast(le)
            own = dict(color=list(obs[0].color), height=hs[0], width=ws[0])
            for k in lockf:
                own.pop(k, None)
            _entry_set(fe, own)
            what = [w for k, w in (("color", "colour"), ("height", "height"), ("width", "width")) if k in lockf]
            notes.append(f"{names}: linked to {fe.name}" + (f" (the library's {' and '.join(what)})" if what else ""))
        else:
            clash = [k for k, bad in (("colour", "color" not in lockf and _rgba_differs(fe.color, obs[0].color, 0.01)),
                                      ("height", "height" not in lockf and abs(fe.height - hs[0]) > 0.005),
                                      ("width", "width" not in lockf and abs(fe.width - ws[0]) > 0.005)) if bad]
            if clash:
                for o in obs:
                    o[CAST_KEY] = ""
                notes.append(f"{names}: {' and '.join(clash)} {'differ' if len(clash) > 1 else 'differs'} from "
                             f"{fe.name} in another staging, kept as is and unlinked")
                continue
            notes.append(f"{names}: linked to {fe.name}")
        for o in obs:
            o[CAST_KEY] = fe.cid
            apply_cast_to(o, fe)
    scene[CAST_MIGRATED] = 1
    _note_upgrade(scene, notes)


def _next_free_color(scene):
    """A colour for a new character that is not a cast character: the next palette colour that is not one of
    the four fixed hues (blue, purple, yellow, black) and not worn by somebody in this staging already."""
    import colorsys
    st = scene.bb_st
    fixed = [colorsys.rgb_to_hsv(*c[:3]) for _i, _n, c, *_r in CAST_BUILTIN[:4]]
    used = [tuple(o.color)[:3] for o in stage_objects(scene, roles=("char",))]
    n = len(PEG_COLORS)
    for strict in (True, False):
        for k in range(n):
            c = PEG_COLORS[(st.next_color + k) % n]
            hh, ss, vv = colorsys.rgb_to_hsv(*c[:3])
            if any(fs > 0.3 and ss > 0.3 and min(abs(hh - fh), 1 - abs(hh - fh)) < 0.06 for fh, fs, _fv in fixed):
                continue                        # a fixed cast colour
            if strict and any(math.dist(c[:3], u) < 0.12 for u in used):
                continue
            st.next_color += k + 1
            return c
    c = PEG_COLORS[st.next_color % n]
    st.next_color += 1
    return c


class BBST_Cast(bpy.types.PropertyGroup):
    """The file's copy of one cast character (fstate().cast): every character linked to it follows it."""
    cid: bpy.props.StringProperty()
    name: bpy.props.StringProperty(name="Name", update=_cast_update,
                                   description="The character's name in the panels (each staging's object keeps its own)")
    color: bpy.props.FloatVectorProperty(name="Colour", subtype='COLOR', size=4, min=0.0, max=1.0,
                                         default=(0.5, 0.5, 0.5, 1.0), update=_cast_update,
                                         description="The peg's colour: who is who in every pane and in the "
                                                     "Seedance references")
    height: bpy.props.FloatProperty(name="Height (m)", default=1.72, min=0.5, max=2.6, step=1, precision=2,
                                    update=_cast_height_update,
                                    description="Floor to the top of the head: the whole model scales with it")
    # the default stays 0.33 (0.19's, _CAST_W_UNSET): an entry whose width was never written reads it, and 0.19
    # skipped writing a width equal to it (Aunty), so changing it would change what old files hold
    width: bpy.props.FloatProperty(name="Width (m)", default=0.33, min=0.08, max=0.9, step=1, precision=2,
                                   update=_cast_width_update,
                                   description="Side to side at the widest: the whole peg, head included, gets wider "
                                               "or narrower. 0.27 m is the standard peg at 1.75 m")
    width_v: bpy.props.IntProperty(default=0, options={'HIDDEN'},
                                   description="What the width means: 2 = side to side (s7); 0 = 0.19's shoulder line")
    build: bpy.props.FloatProperty(default=0.0, options={'HIDDEN'},
                                   description="The Width as a part of the standard peg's for the Height (1 = "
                                               "standard): a new Height keeps it. 0 = not known yet")
    sit_at: bpy.props.FloatProperty(name="Usual seat (m)", default=SIT_AT, min=0.0, max=3.0, step=1, precision=2,
                                    update=_cast_update, description="Seat height a Sit starts from (a chair: 0.45)")
    lie_at: bpy.props.FloatProperty(name="Usual bed (m)", default=LIE_AT, min=0.0, max=3.0, step=1, precision=2,
                                    update=_cast_update, description="Where a Lie puts the body: 0 the floor, about 0.55 a bed")
    notes: bpy.props.StringProperty(name="Notes")
    locked: bpy.props.BoolProperty(name="Locked", default=False)
    colour_only: bpy.props.BoolProperty(name="Colour fixed", default=False,
                                        description="Locked for the colour only: the height and the rest are this "
                                                    "file's own (Jai, Shefali, Shemda and Shaan Daar)")
    updated: bpy.props.StringProperty()
    in_library: bpy.props.BoolProperty(default=False)


def _row_view_layer(scene):
    """The view layer a staging's lists read the picked object from: the window's, else the scene's first."""
    ctx = bpy.context
    vl = getattr(ctx, "view_layer", None)
    if vl is not None and getattr(ctx, "scene", None) == scene:
        return vl
    return scene.view_layers[0] if len(scene.view_layers) else None


def _row_get(st, kind):
    """Characters / Props / Cameras list: the highlighted row is the picked object's (-1: it is not in this list).
    Read only, so the draw code that asks for it writes nothing."""
    try:
        scene = st.id_data
        if not (isinstance(scene, bpy.types.Scene) and is_staging(scene)):
            return -1
        c = sub_coll(scene, "STAGE", kind)
        vl = _row_view_layer(scene)
        ob = vl.objects.active if vl is not None else None
        if c is None or ob is None:
            return -1
        return c.objects.find(ob.name)
    except Exception:
        return -1


def _row_set(st, kind, idx):
    """Clicking a character, prop or camera row picks it (only it), so Turn and drags act on it."""
    try:
        scene = st.id_data
        c = sub_coll(scene, "STAGE", kind) if (isinstance(scene, bpy.types.Scene) and is_staging(scene)) else None
        if c is None or not (0 <= idx < len(c.objects)) or c.objects[idx].hide_select:
            return
        ob = c.objects[idx]
        vl = _row_view_layer(scene)
        if vl is None or vl.objects.get(ob.name) != ob:
            return
        for o in list(vl.objects.selected):
            o.select_set(False, view_layer=vl)
        ob.select_set(True, view_layer=vl)
        vl.objects.active = ob
    except (ReferenceError, RuntimeError) as e:
        print("BB Stage list pick:", e)


def _handles_update(self, context):
    """Edit Studio (Easy) or Easy handles (Artist) changed: new tool, studio (un)locked."""
    for w in stage_windows():
        apply_mode_tool(w)
    request_sync(0.0)


# ------------------------------------------------------------------ the sidebar's modules (0.19)
#
# Aman, 14 Oct 2026: "figure out a way to make the ui cleaner and modular so that when we add functionality later on
# as well, it is easier for me to set it up. there could be a camera control mode as well"; "for some of these
# settings i feel it's not necessary to put them in the main ui. there could be a button that pops up a dialogue";
# 15 Oct: a "checklist" that switches features on and off per staging.
#
# Every part of the sidebar is ONE entry below: the mode tab it lives in, the function that draws it (by name, looked
# up when it draws), the line the Switchboard shows for it, and how to tell that a staging already uses it. One panel
# class is made per entry (BBST_PT_mod_<id>; the BBST prefix keeps BB Crowd's tab rule: panels whose class name starts
# with BBST survive Stage Mode) and one Switchboard tick per switchable entry (BBST_Features). A new feature is one more
# entry and its draw function. A module whose data a staging already has is never hidden silently: switched off, its
# panel stays with a line saying so and a button to switch it back on.

TABS = (
    ('BLOCK', "Block", "Characters, props and beats: who stands where, and when", 'POSE_HLT'),
    ('CAMERA', "Camera", "Cameras, how they move and the cuts. People and props can't be clicked in the panes "
                         "here, so framing a shot never nudges them", 'OUTLINER_OB_CAMERA'),
    ('STUDIO', "Studio", "The grey studio: its size, floor and walls, kit pieces, floors and levels", 'MOD_BUILD'),
    ('OUTPUT', "Output", "Playblasts, the staging pack and the top map", 'RENDER_ANIMATION'),
)
ARTIST_TABS = {'STUDIO', 'OUTPUT'}        # Easy Mode shows Block and Camera only


class Module:
    """One module of the sidebar. tabs: the mode tabs it shows in; draw / in_use: names of functions in this file
    (draw(layout, context[, compact=True]) and in_use(scene) -> bool); compact: tabs where it draws its short form;
    parent: the module whose panel it sits in (a sub-panel); always: no Switchboard tick; artist: Artist Mode only."""
    __slots__ = ("id", "label", "tabs", "draw", "what", "icon", "always", "default", "in_use", "artist", "parent",
                 "compact")

    def __init__(self, id, label, tabs, draw, what, icon='NONE', always=False, default=True, in_use="",
                 artist=False, parent="", compact=()):
        self.id, self.label, self.tabs, self.draw, self.what, self.icon = id, label, tuple(tabs), draw, what, icon
        self.always, self.default, self.in_use, self.artist = always, default, in_use, artist
        self.parent, self.compact = parent, tuple(compact)


MODULES = (
    Module("beats", "Beats", ("BLOCK", "CAMERA"), "draw_beats", "The beat list, Save Beat, play",
           icon='KEYFRAME_HLT', always=True, compact=("CAMERA",)),
    Module("cast", "Characters", ("BLOCK",), "draw_cast", "Who is in the scene, from the cast library",
           icon='COMMUNITY', always=True),
    Module("poses", "Poses", ("BLOCK",), "draw_poses", "Stand, sit or lie on a beat", icon='POSE_HLT',
           parent="cast", in_use="poses_in_use"),
    Module("props", "Props", ("BLOCK",), "draw_props", "Prop blocks that move and key like the characters",
           icon='MESH_CUBE', in_use="props_in_use"),
    Module("set_edits", "Set edits", ("BLOCK",), "draw_set_edits",
           "Take set pieces into this staging to move them (Edit Set)", icon='RESTRICT_SELECT_OFF',
           in_use="set_edits_in_use"),
    Module("paths", "Paths", ("BLOCK",), "draw_paths", "Draw the route somebody walks into a beat",
           icon='CURVE_BEZCURVE', in_use="paths_in_use"),
    Module("natural", "Natural moves", ("BLOCK",), "draw_natural",
           "People walk at their own pace and turn where they go; timing by hand", icon='IPO_EASE_IN_OUT',
           in_use="natural_in_use"),
    Module("cameras", "Cameras", ("CAMERA",), "draw_cams", "The staging's cameras and their lenses",
           icon='OUTLINER_OB_CAMERA', always=True),
    Module("cam_rigs", "Camera moves", ("CAMERA",), "draw_cam_moves",
           "Looks at, Travels with, Eyes of, Zoom, Handheld, a path", icon='CON_TRACKTO',
           in_use="cam_rigs_in_use"),
    Module("cuts", "Cuts", ("CAMERA",), "draw_cuts", "Which camera the preview shows from when (timeline markers)",
           icon='MARKER_HLT', in_use="cuts_in_use"),
    Module("studio", "Studio space", ("STUDIO",), "draw_studio", "Where the studio stands, its size, floor and walls",
           icon='OBJECT_ORIGIN', always=True, artist=True),
    # 0.19.1 (Aman, 15 Oct 2026): walls he could not find, and the real props of the shoot day; never switched off
    Module("walls", "Walls & doors", ("STUDIO",), "draw_walls",
           "Add Wall and Add Door Flat: studio walls placed, moved and sized by hand", icon='MOD_SOLIDIFY',
           always=True, artist=True),
    Module("studio_props", "Studio props", ("STUDIO",), "draw_studio_props",
           "Real props in the studio on the shoot day (a set chair or table made a studio contact prop): sizes, notes",
           icon='FAKE_USER_ON', always=True, artist=True),
    Module("kit", "Kit & stand-ins", ("STUDIO",), "draw_kit",
           "Wall flats, tables, boxes; grey boxes, placeholders", icon='MOD_BUILD',
           default=False, artist=True, in_use="kit_in_use"),
    # no "in use": the plan pane's header always shows the level a staging works on, so hiding this panel hides no
    # data (review of s5: with Floors counted as in use, every Dubey staging kept it, and its tick did nothing)
    Module("levels", "Floors & levels", ("STUDIO",), "draw_levels",
           "The set's floors: which one the scene plays on, and the plan cut", icon='CON_FLOOR', artist=True),
    Module("outputs", "Outputs", ("OUTPUT",), "draw_outputs", "Playblasts, the staging pack and the top map",
           icon='RENDER_ANIMATION', artist=True),
    # The caption switch is one checkbox and lives in Settings only (UX review of s5: it had three homes, and its
    # Switchboard tick could hide nothing, because a caption that is on counted as "in use").
)
MODULE_BY_ID = {m.id: m for m in MODULES}


def _feature_update(self, context):
    _caption_redraw(self, context)          # the sidebar shows or hides the module at once


def _features_class():
    """BBST_Features: one tick per switchable module, made from MODULES (a new module gets its tick by itself)."""
    ann = {m.id: bpy.props.BoolProperty(name=m.label, default=m.default, description=m.what, update=_feature_update)
           for m in MODULES if not m.always}
    return type("BBST_Features", (bpy.types.PropertyGroup,),
                {"__annotations__": ann, "__module__": __name__,
                 "__doc__": "The Switchboard: which modules a staging shows (on the set scene: the file's defaults "
                            "for new stagings)"})


BBST_Features = _features_class()


class BBST_Props(bpy.types.PropertyGroup):
    mode: bpy.props.EnumProperty(name="Mode", items=[
        ('EASY', "Easy", "Characters, beats and cameras only"),
        ('ARTIST', "Artist", "Full control: studio build, stand-ins, outputs")],
        default='ARTIST')
    studio_w: bpy.props.FloatProperty(name="Width", default=12.0, min=2, max=60, update=_studio_dims_update)
    studio_d: bpy.props.FloatProperty(name="Depth", default=10.0, min=2, max=60, update=_studio_dims_update)
    studio_h: bpy.props.FloatProperty(name="Height", default=4.0, min=2, max=20, update=_studio_dims_update)
    wall_count: bpy.props.IntProperty(name="Studio walls", default=4, min=0, max=12, update=_shell_update,
                                      description="Wall flats standing along the back of the studio")
    wall_width: bpy.props.FloatProperty(name="Wall width (m)", default=2.4, min=0.3, max=10, update=_shell_update)
    wall_height: bpy.props.FloatProperty(name="Wall height (m)", default=3.0, min=0.5, max=10, update=_shell_update)
    wall_new_len: bpy.props.FloatProperty(name="Length (m)", default=2.4, min=0.5, max=30.0, step=10, precision=2,
                                          description="How long the next Add Wall or Add Door Flat is")
    wall_new_h: bpy.props.FloatProperty(name="Height (m)", default=3.0, min=0.5, max=12.0, step=10, precision=2,
                                        description="How high the next Add Wall or Add Door Flat is")
    shell_built: bpy.props.BoolProperty(default=False)
    beat_spacing: bpy.props.FloatProperty(name="Default move time (s)", default=3.0, min=0.0, max=60, precision=1,
                                          description="How long the move into a new beat takes")
    beat_hold: bpy.props.FloatProperty(name="Default hold time (s)", default=1.0, min=0.0, max=60, step=50,
                                       precision=1,
                                       description="How long a new beat holds its pose before the next move "
                                                   "starts. Beats already made keep their own Hold")
    key_cameras: bpy.props.BoolProperty(name="Key cameras on beats", default=False)
    natural: bpy.props.BoolProperty(
        name="Natural moves", default=False, update=_natural_update,
        description="Everybody takes the time their own move needs instead of the whole Move time: they set off a "
                    "little after each other, walk at the walking pace, turn to where they go and settle before the "
                    "beat. Off: everybody eases over the whole move together (0.15 and earlier)")
    pace: bpy.props.FloatProperty(
        name="Walking pace (m/s)", default=1.3, min=0.3, max=6.0, step=10, precision=1, update=_natural_update,
        description="Natural moves: how fast people walk when the Move time leaves them the choice (a stroll is 1, "
                    "a brisk walk 1.6). A move too short for the distance still makes them hurry")
    alive: bpy.props.FloatProperty(
        name="Life in the holds", default=0.0, min=0.0, max=3.0, step=10, precision=1, update=_alive_update,
        description="Characters never stand like statues: their facing drifts a little, each in its own slow rhythm. "
                    "0 is off, 1 is subtle, 3 is restless")
    path_focus: bpy.props.BoolProperty(
        name="Paths: this beat only", default=True, update=_path_focus_update,
        description="Show only the drawn moves that lead into the beat the playhead is on — everybody's, cameras "
                    "included. Off: every path in the staging is drawn at once")
    carry_set: bpy.props.BoolProperty(
        name="Retime the set animation too", default=False,
        description="A change of a Move or Hold time also moves the keys of animated set objects (a collapsing "
                    "building timed to a beat). Leave off when other stagings share that animation")
    moves: bpy.props.CollectionProperty(type=BBST_Move)
    show_captions: bpy.props.BoolProperty(name="Caption in the preview pane", default=True, update=_caption_redraw,
                                          description="Show the label and note of the beat at the playhead along the bottom of the "
                                                      "preview pane. On screen only, never in a playblast")
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
    # ---- 0.19: the beat model
    beat_marks: bpy.props.StringProperty(default="")      # {beat uid: [marker name, frame]}: the markers it owns
    carry_memo: bpy.props.StringProperty(default="")      # where retimed markers really are (sub-frame, parked)
    unsaved_between: bpy.props.BoolProperty(default=False)   # something moved while the playhead is between beats
    paths: bpy.props.CollectionProperty(type=BBST_Path)
    next_uid: bpy.props.IntProperty(default=1)
    beat_index: bpy.props.IntProperty(default=0, update=_beat_index_update)
    stage_mode: bpy.props.BoolProperty(default=False)   # the kiosk layout is active
    prev_workspace: bpy.props.StringProperty(default="")
    # the lists' highlighted row IS the picked object (UX review of s5: the Characters list kept Jai highlighted
    # while the card showed Riya); clicking a row picks that object
    char_index: bpy.props.IntProperty(default=-1, get=lambda self: _row_get(self, "Characters"),
                                      set=lambda self, v: _row_set(self, "Characters", v))
    prop_index: bpy.props.IntProperty(default=-1, get=lambda self: _row_get(self, "Props"),
                                      set=lambda self, v: _row_set(self, "Props", v))
    cam_index: bpy.props.IntProperty(default=-1, get=lambda self: _row_get(self, "Cameras"),
                                     set=lambda self, v: _row_set(self, "Cameras", v))
    new_char_name: bpy.props.StringProperty(
        name="Name", default="", search=_cast_name_search, search_options={'SUGGESTION', 'SORT'},
        description="Type a name: the cast library's characters are offered as you type (picking one brings its "
                    "colour, height and width); a new name makes a new character")
    next_color: bpy.props.IntProperty(default=0)
    # ---- v0.19: the file's copy of the cast (file level, read from the set scene through fstate())
    cast: bpy.props.CollectionProperty(type=BBST_Cast)
    cast_index: bpy.props.IntProperty(default=0)
    # ---- v0.8: robust references (per staging)
    set_coll: bpy.props.PointerProperty(type=bpy.types.Collection)
    studio_coll: bpy.props.PointerProperty(type=bpy.types.Collection)
    stage_coll: bpy.props.PointerProperty(type=bpy.types.Collection)
    chars_coll: bpy.props.PointerProperty(type=bpy.types.Collection)
    props_coll: bpy.props.PointerProperty(type=bpy.types.Collection)
    cams_coll: bpy.props.PointerProperty(type=bpy.types.Collection)
    boundary: bpy.props.PointerProperty(type=bpy.types.Object)
    set_scene: bpy.props.PointerProperty(type=bpy.types.Scene)      # staging: the set scene it plays in
    stageable: bpy.props.BoolProperty(
        name="Offer for staging", default=False,
        description="New Staging offers this scene as a set to stage in (none ticked: every scene)")
    data_version: bpy.props.IntProperty(default=0)
    play_level: bpy.props.EnumProperty(name="Plays on", items=LEVEL_ITEMS, default='GROUND',
                                       update=_play_level_update)
    floor_z: bpy.props.FloatProperty(name="Studio floor height (m)", default=0.0, soft_min=-5, soft_max=30,
                                     description="Where characters stand and cameras measure eye level from")
    needs_place: bpy.props.BoolProperty(default=False)
    bound_xy: bpy.props.FloatVectorProperty(size=2)      # where the studio space was: moves carry the rest
    bound_xy_set: bpy.props.BoolProperty(default=False)
    bound_z: bpy.props.FloatProperty(default=0.0)
    use_floors: bpy.props.BoolProperty(
        name="Floors", default=False, update=_use_floors_update,
        description="Detect the set's floors: levels, the plan cut and a studio that stands on a floor. "
                    "Off (a city, an exterior): no floors are worked out and the studio moves freely, up and down too")
    # ---- v0.10: handles (file level, read from the set scene)
    artist_handles: bpy.props.BoolProperty(
        name="Easy handles in Artist Mode", default=False, update=_handles_update,
        description="Click and drag to move, with turn and move handles on whatever you click, "
                    "like Easy Mode. Off: select, then use the shortcuts (G, R, S, Tab)")
    edit_studio: bpy.props.BoolProperty(
        name="Edit Studio", default=False, update=_handles_update,
        description="Easy Mode: unlock the studio space, its floor, walls and pieces so they can be "
                    "moved (and the studio resized). Off, clicks go through to the characters")
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
    floors_detected: bpy.props.BoolProperty(default=False)
    has_upper: bpy.props.BoolProperty(name="This set has an upper floor", default=True)
    ground_z: bpy.props.FloatProperty(name="Ground floor height (m)", default=-999.0)   # -999 = not detected yet
    upper_z: bpy.props.FloatProperty(name="Upper floor height (m)", default=-999.0)
    # ---- 0.19: set edits (per staging)
    set_edits: bpy.props.CollectionProperty(type=BBST_SetEdit)
    edit_set: bpy.props.BoolProperty(
        name="Edit Set", default=False, update=lambda self, ctx: _edit_set_update(self, ctx),
        description="Let the set be clicked in this staging, to take pieces of it into the staging "
                    "(Take into Staging). The set itself is never changed from here")
    # ---- 0.19 (s5): the Switchboard (per staging; on the set scene, the defaults for new stagings)
    features: bpy.props.PointerProperty(type=BBST_Features)


# ------------------------------------------------------------------ staging builder

def _evaluated_matrix(ob, dg):
    """World matrix as evaluated: what a file stores for objects in a scene nobody has opened
    (or in a collection the scene excludes) can be a stale identity."""
    if dg is not None:
        try:
            return ob.evaluated_get(dg).matrix_world.copy()
        except Exception:
            pass
    return ob.matrix_world.copy()


def set_bounds_center(scene):
    """Where the set's things are: the median of mesh positions (a giant ground plane or a
    stray object far away does not drag it off the building)."""
    xs, ys = [], []
    dg = _scene_depsgraph(scene)
    for c in layer_colls(scene, "SET"):
        for ob in coll_objects(c):
            if ob.type == 'MESH':
                p = _evaluated_matrix(ob, dg).translation
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
    fs = floor_state(scene)
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
    set_names |= {o.name for o in instanced_objects(scene)}     # a house placed by instance
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
    if not st.use_floors:           # no floors: the studio stands wherever its box is
        if b is not None:
            st.floor_z = b.location.z
        return
    c = studio_center(scene)
    old = st.floor_z
    st.floor_z = detect_floor_z(scene, c.x, c.y, st.play_level)
    if b is not None:
        b.location.z = st.floor_z
    if carry:      # what stands on the studio floor moves with it
        carry_with_studio(scene, Vector((0.0, 0.0, st.floor_z - old)))


def _carried_objects(scene, skip_selected=False):
    b = boundary_of(scene)
    obs = set(stage_objects(scene, roles=("char", "prop", "cam"))) | set(stage_cams(scene))
    for c in layer_colls(scene, "STUDIO"):
        obs |= {o for o in coll_objects(c) if o != b}
    for c in layer_colls(scene, "STAGE"):       # drawn paths travel with their walkers
        obs |= {o for o in coll_objects(c) if o.get(ROLE_KEY) == PATH_ROLE}
    # stand-ins / matched pieces sit where their set object is: they never move with the studio
    return [o for o in obs if o.parent is None and o.get(SOURCE_KEY) is None]


def _shift_location_keys(ob, d):
    ad = ob.animation_data
    for fc in (channelbag_fcurves(ad.action) if ad and ad.action else []):
        if fc.data_path == "location" and fc.array_index in (0, 1, 2) and abs(d[fc.array_index]) > 1e-6:
            k = d[fc.array_index]
            for kp in fc.keyframe_points:
                kp.co.y += k
                kp.handle_left.y += k
                kp.handle_right.y += k
            _settle_curve(fc)           # never update(): it merges keys a retime squeezed together


def carry_with_studio(scene, d, skip_selected=False):
    """Move the studio's pieces, pegs and cameras by d, their beat keys included. skip_selected (the space moved in
    the panes): a selected object that moved with it (a drag of the whole selection) is already there, so only its
    keys follow; one that was only selected (the space's location typed) is carried like the rest (0.19.1; before,
    every selected object was taken as dragged and kept its keys behind, VERIFY_0.19 #2)."""
    if d.length < 1e-5:
        return
    obs = _carried_objects(scene)
    dragged = []
    if skip_selected:
        for ob in obs:
            try:
                if ob.select_get() and _was_dragged(scene, ob, d):
                    dragged.append(ob)
            except RuntimeError:
                pass
        for ob in dragged:          # before save_unsaved: the drag is the studio's move, never a move on this beat
            _shift_location_keys(ob, d)
    save_unsaved(scene)     # shifting the keys re-reads them: unsaved moves would be lost
    for ob in obs:
        if ob in dragged:
            continue
        ob.location += d
        _shift_location_keys(ob, d)


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
    lock_floor(floor)
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


def lock_floor(ob):
    """The studio floor and the studio space are one thing (Aman, 5 Oct 2026): clicking the
    floor selects the space, and the floor itself never moves on its own."""
    ob.lock_location = (True, True, True)
    ob.lock_rotation = (True, True, True)
    ob.lock_scale = (True, True, True)


def is_studio_floor(ob):
    return ob is not None and ob.get(SHELL_KEY) and ob.get("bb_st_kind") == "Studio floor"


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


def next_camera_name(scene):
    """The name a new camera of this staging gets: STG Cam A, B, C..."""
    cams = sub_coll(scene, "STAGE", "Cameras")
    n = len([o for o in cams.objects if o.type == 'CAMERA']) if cams is not None else 0
    return unique_object_name(f"STG Cam {chr(ord('A') + min(25, n))}")


def make_stage_camera(scene, lens=35.0, animated=None, name=""):
    """A camera in the middle of the studio at eye level, level, looking along +Y.
    animated: True keys it on the beats, False makes it Static (no keys, out of the beats), None (the default)
    leaves it unflagged, which moves on the beats as before 0.19.1. The add-on's own Add Camera and New Staging pass
    False (Aman, 15 Oct 2026: a new camera is not keyframed unless he chooses so). Build scripts in the toolchain
    (bb_gossip_maze/build_sequence.py, bb_peddar_30/build30.py) call this helper and only ever ADD the Static flag
    to shots that stay put, so the helper itself must keep the old default (review of s8-studio #1)."""
    cams = sub_coll(scene, "STAGE", "Cameras")
    if cams is None:
        return None
    n = len([o for o in cams.objects if o.type == 'CAMERA'])
    name = unique_object_name(" ".join(name.split())) if name and name.strip() else next_camera_name(scene)
    data = bpy.data.cameras.new(name)
    data.lens = lens
    ob = bpy.data.objects.new(name, data)
    ob[ROLE_KEY] = "cam"
    if animated is True:
        ob[CAM_KEY] = True
    elif animated is False:
        ob[STATIC_KEY] = True
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


_SET_ITEMS = []      # Blender keeps only pointers into dynamic enum items: hold on to them


def _set_scene_items(self, context):
    _SET_ITEMS.clear()
    for i, sc in enumerate(set_scenes()):
        n = len(stagings_of(sc))
        _SET_ITEMS.append((sc.name, sc.name, f"Stage in {sc.name} ({n} staging{'' if n == 1 else 's'} so far)",
                           'SCENE_DATA', i))
    return _SET_ITEMS or [("", "No set scene", "", 'ERROR', 0)]


def link_set(sc, src):
    """The set scene's collections and loose objects, linked (never copied) under the staging's
    one unselectable SET wrapper: the model can only be edited in its own scene."""
    st = sc.bb_st
    roots = layer_colls(sc, "SET")
    if roots:
        wrapper = roots[0]
    else:
        wrapper = bpy.data.collections.new(f"SET · {staging_label(sc)}")
        wrapper[LAYER_KEY] = "SET"
        sc.collection.children.link(wrapper)
        st.set_coll = wrapper
    wrapper.hide_select = not st.edit_set
    for c in list(wrapper.children):
        wrapper.children.unlink(c)
    for ob in list(wrapper.objects):
        wrapper.objects.unlink(ob)
    for coll in src.collection.children:
        if coll.get(LAYER_KEY) in ("SET", "STUDIO", "STAGE"):
            continue
        wrapper.children.link(coll)
    for ob in src.collection.objects:
        if ob.get(ROLE_KEY) is None:
            wrapper.objects.link(ob)
    st.set_scene = src
    exclude_set_edits(sc)               # a re-link brings the set edits' wrappers back in: keep them out
    return wrapper


class BBST_OT_new_staging(bpy.types.Operator):
    """Create a new staging: one studio setup for one scene of the script, in one of this file's set scenes"""
    bl_idname = "bbst.new_staging"
    bl_label = "New Staging"
    bl_options = {'REGISTER', 'UNDO'}

    set_name: bpy.props.EnumProperty(name="Stage in", items=_set_scene_items,
                                     description="The set scene this staging plays in (Settings: which scenes are offered)")
    label: bpy.props.StringProperty(name="Staging name", default="")
    use_floors: bpy.props.BoolProperty(name="Floors", default=False,
                                       description="Work out the set's floors now (levels and plan cut). "
                                                   "Can be switched on later in Settings")
    level: bpy.props.EnumProperty(name="Plays on", items=LEVEL_ITEMS, default='GROUND',
                                  description="Which floor this scene plays on — everything above it hides")

    def invoke(self, context, event):
        cur = set_scene_of(context.scene)
        if cur is not None and cur.name in {sc.name for sc in set_scenes()}:
            self.set_name = cur.name
        return context.window_manager.invoke_props_dialog(self, width=380)

    def draw(self, context):
        lay = self.layout
        lay.prop(self, "set_name")
        lay.prop(self, "label")
        lay.prop(self, "use_floors")
        src = bpy.data.scenes.get(self.set_name)
        fs = getattr(src, "bb_st", None)
        if self.use_floors and (fs is None or not floors_known(fs) or fs.has_upper):
            lay.prop(self, "level")

    def execute(self, context):
        label = fit_label(self.label)      # Blender cuts scene names at 63 bytes: never a silent ".001" name
        if not label:
            self.report({'ERROR'}, "Give the staging a name")
            return {'CANCELLED'}
        src = bpy.data.scenes.get(self.set_name) if self.set_name else None
        if src is None or is_staging(src):
            offered = set_scenes()
            src = offered[0] if offered else None
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
        wrapper = link_set(sc, src)
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
        fs = floor_state(sc)
        st["use_floors"] = self.use_floors
        if self.use_floors and fs is not None and not floors_known(fs):
            store_floors(fs, sc)        # first floors staging of this set scene: find its floors and plan cuts
        level = self.level if self.use_floors else 'GROUND'
        if not self.use_floors:
            st.active_level = "ALL"
        if level == 'L1' and fs is not None and not fs.has_upper:
            level = 'GROUND'
            self.report({'WARNING'}, "This set has one floor: the staging plays on the ground floor")
        _QUIET["floor"] = True
        try:
            st.play_level = level
        finally:
            _QUIET["floor"] = False
        if self.use_floors:
            st.active_level = level
        st.data_version = DATA_VERSION
        features_from_defaults(sc)      # the Switchboard's ticks: the file's defaults (0.19)
        st["natural"] = True            # new stagings move naturally (0.16); older ones keep how they were made
        st["alive"] = 1.0
        # studio space: middle of the set, standing on this level's floor
        centre = set_bounds_center(sc)
        bound = build_boundary_object(label, st.studio_w, st.studio_d, st.studio_h)
        studio.objects.link(bound)
        st.boundary = bound
        bound.location = (centre.x, centre.y, 0.0)
        st.floor_z = detect_floor_z(sc, centre.x, centre.y, level) if self.use_floors else 0.0
        bound.location.z = st.floor_z
        st.bound_xy = (centre.x, centre.y)
        st.bound_z = st.floor_z
        st.bound_xy_set = True
        build_studio_shell(sc)
        cam = make_stage_camera(sc, animated=False)     # Static until he puts it on the beats (0.19.1)
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
        self.report({'INFO'}, f"Staging '{label}' in {src.name} — now drag the studio space where the scene plays")
        return {'FINISHED'}


class BBST_OT_staging_set(bpy.types.Operator):
    """Change the set scene this staging plays in. Its studio, characters, cameras and beats stay; place the studio space again"""
    bl_idname = "bbst.staging_set"
    bl_label = "Plays In"
    bl_options = {'REGISTER', 'UNDO'}

    scene_name: bpy.props.StringProperty()
    set_name: bpy.props.EnumProperty(name="Set scene", items=_set_scene_items)

    def invoke(self, context, event):
        sc = bpy.data.scenes.get(self.scene_name) or context.scene
        cur = set_scene_of(sc)
        if cur is not None and cur.name in {x.name for x in set_scenes()}:
            self.set_name = cur.name
        return context.window_manager.invoke_props_dialog(self, width=360)

    def execute(self, context):
        sc = bpy.data.scenes.get(self.scene_name) or context.scene
        src = bpy.data.scenes.get(self.set_name)
        if not is_staging(sc) or src is None or is_staging(src):
            return {'CANCELLED'}
        if src == set_scene_of(sc) and sc.bb_st.set_scene == src:
            return {'FINISHED'}
        untint_everything()             # the old set's ghost tint
        link_set(sc, src)
        st = sc.bb_st
        sc.world = src.world
        fs = floor_state(sc)
        if st.use_floors and fs is not None and not floors_known(fs):
            store_floors(fs, sc)
        if st.play_level == 'L1' and fs is not None and not fs.has_upper:
            _QUIET["floor"] = True
            try:
                st.play_level = 'GROUND'
            finally:
                _QUIET["floor"] = False
            st.active_level = 'GROUND'
        refresh_floor(sc)
        st.needs_place = True
        normalize_view_layer(sc)
        request_sync(0.0)
        self.report({'INFO'}, f"{staging_label(sc)} now plays in {src.name}: place the studio space")
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
        others = [s for s in stagings() if s != sc]
        for win in context.window_manager.windows:
            if win.scene == sc:
                win.scene = others[0] if others else (set_scene_of(sc) or master_scene())
        kept = delete_staging_data(sc)      # B3/B4: what another scene uses stays
        try:
            heal_set_wrappers()         # its set edits: the pieces no other staging took go back into the set (s4)
        except Exception as e:          # never half a delete: the screen below must still be rebuilt
            print("BB Stage set edits after Delete Staging:", e)
        if stage_on():
            if others:
                cur = context.window.scene
                _build_stage_screen(cur.name if is_staging(cur) else others[0].name)
            else:
                exit_stage_mode(context)
        if kept:        # one report: the status bar shows the last one (review s6 #9 hid this warning behind INFO)
            self.report({'WARNING'}, f"Staging deleted · kept {kept} collection(s) or object(s) another scene uses")
        else:
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
            try:
                if set_edits_need_repair(sc):   # the set was edited since: its own undo step (review s4 #7)
                    bpy.ops.bbst.set_repair(scene_name=sc.name)
            except Exception as e:
                print("BB Stage set edits on Go to:", e)
            if stage_on() and context.window.workspace.name == WS_NAME:
                _build_stage_screen(sc.name)
        return {'FINISHED'}


# ------------------------------------------------------------------ split, duplicate, safe delete (0.19)
#
# Aman, 15 Oct 2026, the Dubey Computer Den: "split the Dubey stagings: one staging per script scene, except scenes
# that play continuously stay together" — one staging had grown to 26 beats and eleven script scenes. Split off Beats
# takes a run of beats out into a staging of its own on the same set. Whoever takes part in those beats comes along
# with every key they have there, copied frame by frame (hand keys between the beats, drawn paths and their
# followers, a camera's look, eyes and zoom), shifted so the first beat of the run lands on frame 1. Somebody parked
# offstage for the whole run (outside the studio space and the set: the Dubey pegs not in a scene wait outside the
# front wall) stays behind. The source staging is only read. Duplicate Staging is the same copy of every beat, with
# everybody.
#
# The audit of the same night (audit_r3) found four ways of losing work around stagings, fixed here: Delete Staging
# deleted collections the set or another staging shares (B3); Blender's own scene copy shares everything with its
# original (B4: Duplicate Staging, and Make Independent for a staging copied that way); New Staging took a renamed
# staging's studio space (B11, in build_boundary_object); a label that is no folder name broke Playblast and Export
# (B12, safe_folder_name).

_FOLDER_DROP = re.compile(r'[<>"?*\x00-\x1f]')
_WIN_RESERVED = {"CON", "PRN", "AUX", "NUL"} | {f"COM{i}" for i in range(1, 10)} | {f"LPT{i}" for i in range(1, 10)}
SPLIT_KEY = "bb_st_made_from"       # on a staging scene made by Split or Duplicate: where it came from (for people)
_FOOTPRINT = {}                     # scene name: (time, footprint): the Split dialog redraws often, the set stays put
_PLAN_CACHE = {}                    # the Split dialog's preview of who comes along


def safe_folder_name(text, fallback="Staging"):
    """A label as a folder or file name that Windows and macOS both take (B12): "Sc 102: Arrival" -> "Sc 102 -
    Arrival", "Jai/Shefali" -> "Jai-Shefali", "Take 2?" -> "Take 2". The label itself stays as it was typed."""
    s = re.sub(r"\s*:\s*", " - ", str(text))
    s = re.sub(r"[/\\|]", "-", s)
    s = _FOLDER_DROP.sub("", s)
    s = " ".join(s.split()).strip(" .-")
    if not s:
        s = fallback
    if s.split(".")[0].strip().upper() in _WIN_RESERVED:
        s = "_" + s
    return s[:100].rstrip(" .")


def fit_label(label, prefix=STG_PREFIX):
    """A staging label with its spaces tidied, shortened on a whole character so that prefix + label fits Blender's
    63-byte names: a longer name was cut by Blender, and the new staging then looked like a copy of another."""
    label = " ".join(str(label).split())
    while label and len((prefix + label).encode("utf-8")) > 63:
        label = label[:-1].rstrip()
    return label


def unique_label(base):
    """base, or "base 2", "base 3"... whichever no staging has yet."""
    base = fit_label(base)
    label, k = base, 2
    while bpy.data.scenes.get(STG_PREFIX + label) is not None:
        tail = f" {k}"
        label = fit_label(base, prefix=STG_PREFIX + tail) + tail
        k += 1
    return label


def shared_with(scene):
    """Other scenes that hold this staging's own SET, STUDIO or STAGE collection: what Blender's New Scene > Linked
    Copy makes (B4). Moving a character in one moves it in the other, and deleting one used to empty the other."""
    roots = [c for k in ("SET", "STUDIO", "STAGE") for c in layer_colls(scene, k)]
    if not roots:
        return []
    return [s for s in bpy.data.scenes if s != scene and any(s.collection.children.get(c.name) == c for c in roots)]


def studio_owns(scene, ob):
    """True when this object lives in this staging's STUDIO tree only: it is this staging's to rebuild. An object
    that also sits in another staging's tree (the B11 steal, or a file damaged by it) is not. A tree that Blender's
    Linked Copy shares between two scenes is one studio for both until Make Independent: rebuilt in place."""
    roots = layer_colls(scene, "STUDIO")
    if not roots:
        return False
    tree = {c.as_pointer() for r in roots for c in [r] + list(r.children_recursive)}
    return all(c.as_pointer() in tree for c in ob.users_collection)


def _windows_off(context, sc, to=None):
    """Windows showing this scene show another one: the given one, another staging or its set scene."""
    others = [s for s in stagings() if s != sc]
    for win in context.window_manager.windows:
        if win.scene == sc:
            win.scene = to or (others[0] if others else (set_scene_of(sc) or master_scene()))


def delete_staging_data(sc):
    """Remove a staging: its scene and, of its own collections (STUDIO, STAGE and any other one it holds outside the
    SET wrapper: a hologram blockout, a light rig of its own), only what no other scene uses. A collection another
    scene reaches (a crowd linked into STAGE that lives in the set scene too, a light rig two stagings share, a whole
    tree that Blender's Linked Copy shares, a collection another scene places as an instance) stays, with everything
    in it (B3, B4). The SET wrapper only links the set: the set model is never touched. Returns how many collections
    and objects were kept for other scenes."""
    elsewhere = set()
    for s in bpy.data.scenes:
        if s != sc:
            elsewhere.add(s.collection.as_pointer())
            elsewhere.update(c.as_pointer() for c in s.collection.children_recursive)
    tree, seen = [], set()
    set_roots = {c.as_pointer() for c in layer_colls(sc, "SET")}
    for root in [c for c in sc.collection.children if c.as_pointer() not in set_roots]:
        for c in [root] + list(root.children_recursive):
            if c.as_pointer() not in seen:
                seen.add(c.as_pointer())
                tree.append(c)
    for ob in bpy.data.objects:         # placed as an instance by something that is not part of this staging
        ic = ob.instance_collection if ob.instance_type == 'COLLECTION' else None
        if ic is not None and ic.as_pointer() in seen and any(u.as_pointer() not in seen for u in ob.users_collection):
            elsewhere.update(c.as_pointer() for c in [ic] + list(ic.children_recursive))
    wrappers = layer_colls(sc, "SET")
    doomed = [c for c in tree if c.as_pointer() not in elsewhere]
    kept = len(tree) - len(doomed)
    gone = {c.as_pointer() for c in doomed} | {sc.collection.as_pointer()}
    obs, seen_obs = [], set()
    for c in doomed + [sc.collection]:
        for ob in c.objects:
            if ob.as_pointer() not in seen_obs:
                seen_obs.add(ob.as_pointer())
                obs.append(ob)
    # users_collection leaves out scene master collections: an object linked straight into another scene is in
    # users_scene only
    doomed_obs = [ob for ob in obs if all(u.as_pointer() in gone for u in ob.users_collection)
                  and all(s == sc for s in ob.users_scene)]
    kept += len(obs) - len(doomed_obs)
    loose = {}                          # what the doomed objects used: removed once nothing else does
    for ob in doomed_obs:
        for idb in (ob, ob.data, getattr(ob.data, "shape_keys", None) if ob.data is not None else None):
            ad = getattr(idb, "animation_data", None) if idb is not None else None
            if ad is not None and ad.action is not None:
                loose[ad.action.as_pointer()] = ad.action
        if ob.data is not None:
            loose[ob.data.as_pointer()] = ob.data
            for m in getattr(ob.data, "materials", ()):
                if m is not None:
                    loose[m.as_pointer()] = m
        for slot in ob.material_slots:
            if slot.link == 'OBJECT' and slot.material is not None:
                loose[slot.material.as_pointer()] = slot.material
        for m in ob.modifiers:          # a crowd's own node tree and peg material (copied with it by copy_staging)
            if m.type != 'NODES':
                continue
            cands = [m.node_group] if m.node_group is not None else []
            try:
                inp = m.properties.inputs
                for p in inp.bl_rna.properties:
                    sock = getattr(inp, p.identifier, None) if p.identifier != "rna_type" else None
                    cands.append(getattr(sock, "value", None) if sock is not None else None)
            except Exception:
                pass
            for d in cands:
                if isinstance(d, (bpy.types.Material, bpy.types.NodeTree)) and ob.name in d.name:
                    loose[d.as_pointer()] = d
            if m.name == POSE_MOD and m.node_group is not None and m.node_group.name.startswith(POSE_GROUP):
                loose[m.node_group.as_pointer()] = m.node_group     # s3's shared pose group: gone with the last peg
    for ob in doomed_obs:
        bpy.data.objects.remove(ob)
    for _round in range(2):             # a mesh first, then the material only it used
        dead = []
        for d in list(loose.values()):  # the pegs' meshes, the cameras' lenses, the paths' curves: theirs alone
            try:
                if d.users == 0 and d.library is None:
                    dead.append(d)
            except ReferenceError:
                pass
        for d in dead:
            loose.pop(d.as_pointer(), None)
        if dead:
            bpy.data.batch_remove(dead)
    for c in doomed:
        try:
            bpy.data.collections.remove(c)
        except (ReferenceError, RuntimeError):
            pass
    for w in wrappers:
        if w.as_pointer() in elsewhere:
            kept += 1
            continue
        try:
            bpy.data.collections.remove(w)
        except (ReferenceError, RuntimeError):
            pass
    bpy.data.scenes.remove(sc)
    return kept


# ---- who comes along

def set_footprint(scene, fresh=False, evaluate=True):
    """(x0, x1, y0, y1): where the set's things stand: the origins of its meshes and placed instances, the outer 2 %
    on each side left out, so a 200 m ground plane or a stray object far away does not swallow the street. None when
    the set has no meshes. Cached for half a minute (the Split dialog asks on every redraw)."""
    import time
    hit = _FOOTPRINT.get(scene.name)
    if hit is not None and not fresh and time.time() - hit[0] < 30.0:
        return hit[1]
    dg = _scene_depsgraph(scene) if evaluate else None
    xs, ys = [], []
    for c in (layer_colls(scene, "SET") if is_staging(scene) else [scene.collection]):
        for ob in coll_objects(c):
            if ob.type == 'MESH' or (ob.type == 'EMPTY' and ob.instance_type == 'COLLECTION'
                                     and ob.instance_collection is not None):
                p = _evaluated_matrix(ob, dg).translation
                xs.append(p.x)
                ys.append(p.y)
    fp = None
    if xs:
        xs.sort()
        ys.sort()
        k = len(xs) // 50
        fp = (xs[k], xs[-1 - k], ys[k], ys[-1 - k])
    _FOOTPRINT[scene.name] = (time.time(), fp)
    return fp


def _studio_box(scene):
    b = boundary_of(scene)
    if b is None:
        return None
    st = scene.bb_st
    return b.location.x, b.location.y, b.rotation_euler.z, st.studio_w / 2, st.studio_d / 2


def offstage_for(scene, ob, f0, f1, footprint=None):
    """True when this character (or prop) stays offstage on every frame f0..f1, by its keys: outside the studio space
    and outside the set's footprint. Moving around out there (the Dubey group nudge outside the door) is still
    offstage; one frame on the set and it takes part."""
    box = _studio_box(scene)
    rot = Matrix.Rotation(-box[2], 2) if box is not None else None
    fcs = {fc.array_index: fc for fc in id_fcurves(ob) if fc.data_path == "location" and fc.array_index in (0, 1)}
    step = max(1, (int(f1) - int(f0)) // 400)
    frames = set(range(int(f0), int(f1) + 1, step)) | {int(f1)}
    for fc in fcs.values():
        frames |= {int(round(k.co.x)) for k in fc.keyframe_points if f0 <= k.co.x <= f1}
    for f in sorted(frames):
        x = fcs[0].evaluate(f) if 0 in fcs else ob.location.x
        y = fcs[1].evaluate(f) if 1 in fcs else ob.location.y
        if box is not None:
            d = rot @ Vector((x - box[0], y - box[1]))
            if abs(d.x) <= box[3] and abs(d.y) <= box[4]:
                return False
        if footprint is not None and footprint[0] <= x <= footprint[1] and footprint[2] <= y <= footprint[3]:
            return False
    return True


def _looks_in_range(st0, cam, first, last):
    """The look table a copy of beats first..last needs: what the camera looks at on the first beat (inherited from
    the beats before it, the way look_at_beat reads it) and every change after it within the run."""
    table = look_table(cam)
    if not table:
        return {}
    beats = list(st0.beats)
    out, cur = {}, None
    for b in beats[:first + 1]:
        if b.uid in table:
            cur = table[b.uid]
    if cur is not None:
        out[beats[first].uid] = cur
    for b in beats[first + 1:last + 1]:
        if b.uid in table:
            out[b.uid] = table[b.uid]
    return out


def _eyes_in_range(st0, cam, first, last):
    """None when the camera is out of the eyes for the whole run (it stepped off before it); else the step-off beat
    uid the copy keeps (0: it stays in the eyes to the end of the run)."""
    if cam.constraints.get(EYES_CON) is None or eyes_helper(cam) is None:
        return None
    uid, _secs = step_off(cam)
    i = beat_index_of(st0, uid) if uid else None
    if i is None:
        return 0
    if i < first:
        return None
    return uid if i <= last else 0


def _cam_needs(st0, cam, first, last):
    """(object, why) for the characters and props a camera of the run cannot do without."""
    out = []
    t = ride_target(cam)
    if t is not None:
        out.append((t, "travels with"))
    t = eyes_target(cam) if _eyes_in_range(st0, cam, first, last) is not None else None
    if t is not None:
        out.append((t, "is in the eyes of"))
    for v in _looks_in_range(st0, cam, first, last).values():
        t = bpy.data.objects.get(v) if v not in ("", LOOK_OFF) else None
        if t is not None:
            out.append((t, "looks at"))
    return out


def cams_in_run(src, f0, f1, cams=None):
    """The cameras a run of beats (frames f0..f1) shows: the one live when it starts, every one a cut or beat marker
    switches to inside it, and every camera no marker ever names (a setup camera of the whole staging: the Dubey
    stagings have no cuts, so all their cameras come along). PLAN 0.19: "cameras that appear in the range"."""
    cams = stage_cams(src) if cams is None else cams
    bound = {}
    for m in src.timeline_markers:
        if m.camera is not None:
            bound.setdefault(m.camera.as_pointer(), []).append(m.frame)
    live = _camera_at(src, f0)
    return [c for c in cams if not bound.get(c.as_pointer()) or c == live
            or any(f0 <= f <= f1 for f in bound[c.as_pointer()])]


# ---- what a staging is made of, and what a copy of it takes

# Set edits (s4, Take into Staging): PART_KEY marks a copied part of a taken set piece (refresh_set_edits rebuilds
# them in a copy), PARTS_KEY the Props sub-collection that holds them, SETPIECE_KEY a copied set object whose
# mesh and materials stay shared with the set. The keys are defined with the set-edit section below.
_HELPER_ROLES = (AIM_ROLE, EYES_ROLE, RIDE_ROLE, PATH_ROLE, FOLLOWER_ROLE)
_BB_RIG_CONS = (LOOK_CON, AIM_CON, EYES_CON, RIDE_CON, PATH_CON)     # BB Stage's own rigs: the copy rebuilds them
_WALK_COLLS = frozenset(("constraints", "modifiers", "targets", "drivers", "variables"))
_WALK_SKIP = frozenset(("rna_type", "original", "id_data", "data", "parent", "pose", "override_library", "library",
                        "library_weak_reference", "asset_data", "preview", "bl_rna", "shape_keys"))


def _walk_ids(s, visit, rigs=True, depth=0):
    """Every data-block pointer this struct reaches through its own settings, constraints, modifiers (hooks,
    geometry-nodes inputs: mod.properties.inputs.<socket>.value), drivers and nested settings (a camera's focus
    object). visit(owner, identifier, value) may return a replacement, which is set. rigs=False skips BB Stage's own
    rig constraints (Looks at, Eyes of, Travels with, paths): a copy rebuilds those from its tables."""
    if s is None or depth > 6:
        return
    try:
        props = list(s.bl_rna.properties)
    except (AttributeError, ReferenceError):
        return
    for p in props:
        k = p.identifier
        if k in _WALK_SKIP:
            continue
        if p.type == 'POINTER':
            try:
                v = getattr(s, k)
            except Exception:
                continue
            if v is None:
                continue
            if isinstance(v, bpy.types.ID):
                new = visit(s, k, v)
                if new is not None and new != v and not p.is_readonly:
                    try:
                        setattr(s, k, new)
                    except Exception:
                        pass
            else:
                _walk_ids(v, visit, rigs, depth + 1)
        elif p.type == 'COLLECTION' and k in _WALK_COLLS:
            try:
                items = list(getattr(s, k))
            except Exception:
                continue
            for it in items:
                if not rigs and k == "constraints" and it.name.startswith(_BB_RIG_CONS):
                    continue
                _walk_ids(it, visit, rigs, depth + 1)


def _id_refs(ob):
    """[(data-block, why)] an object depends on: its parent, its own constraints' targets (not BB Stage's rigs),
    hooks, geometry-nodes inputs, drivers, and what its data points at (a camera's focus object)."""
    out = []
    if ob.parent is not None:
        out.append((ob.parent, "is parented to"))

    def see(owner, k, v):
        if isinstance(v, (bpy.types.Object, bpy.types.Collection)):
            out.append((v, "follows" if isinstance(owner, bpy.types.Constraint) else "uses"))
        return None
    _walk_ids(ob, see, rigs=False)
    if ob.data is not None:
        _walk_ids(ob.data, see, rigs=False)
    return out


def _idprop_groups(owner):
    """The id-property groups of a data-block or struct: its custom properties and, from Blender 5, the separate
    system properties that add-ons' registered properties live in (BB Stage's bb_st, BB Crowd's cues)."""
    out = []
    try:
        owner.keys()
        out.append(owner)
    except Exception:
        pass
    get = getattr(owner, "bl_system_properties_get", None)
    if get is not None:
        try:
            g = get()
            if g is not None:
                out.append(g)
        except Exception:
            pass
    return out


def _remap_props(owner, idmap, drop=(), depth=0):
    """Point every data-block an id-property holds at its copy (idmap); one in drop (the source staging's own, not
    copied) is cleared rather than left pointing into the source."""
    if depth > 8:
        return
    for g in (_idprop_groups(owner) if depth == 0 else [owner]):
        try:
            keys = list(g.keys())
        except Exception:
            continue
        for k in keys:
            try:
                v = g[k]
            except Exception:
                continue
            if isinstance(v, bpy.types.ID):
                p = v.as_pointer()
                if p in idmap:
                    g[k] = idmap[p]
                elif p in drop:
                    del g[k]
            elif hasattr(v, "keys") and hasattr(v, "__getitem__"):
                _remap_props(v, idmap, drop, depth + 1)
            elif isinstance(v, (list, tuple)) or type(v).__name__ == "IDPropertyArray":
                try:
                    items = list(v)
                except Exception:
                    continue
                for it in items:
                    if hasattr(it, "keys") and hasattr(it, "__getitem__"):
                        _remap_props(it, idmap, drop, depth + 1)


def copy_scope(src):
    """What belongs to this staging, as a copy sees it. Its collections outside the SET wrapper are its own, except
    one another scene also holds (a light rig two stagings share, a crowd that lives in the set too) or that
    something outside it places as an instance: those are linked into a copy, never copied (B3). A scene made from
    it with Blender's Linked Copy (B4) does not count as another scene here: Make Independent copies what the two
    share. Returns {"tree": [(collection, parent)] parents first, "own", "shared", "parts": pointer sets, "objects":
    the candidates (objects in its own collections and its scene collection), "shared_obs": those another scene
    shows too, "partners": the scene pointers that count as itself}."""
    partners = {src.as_pointer()} | {s.as_pointer() for s in shared_with(src)}
    holders = {}
    for s in bpy.data.scenes:
        for c in [s.collection] + list(s.collection.children_recursive):
            holders.setdefault(c.as_pointer(), set()).add(s.as_pointer())
    outside_inst = set()
    for ob in bpy.data.objects:
        ic = ob.instance_collection if ob.instance_type == 'COLLECTION' else None
        if ic is not None and not (ob.users_scene and all(s.as_pointer() in partners for s in ob.users_scene)):
            outside_inst.add(ic.as_pointer())
    set_roots = {c.as_pointer() for c in layer_colls(src, "SET")}
    tree, own, shared, parts, order = [], set(), set(), set(), []
    stack = [(c, src.collection) for c in reversed(list(src.collection.children)) if c.as_pointer() not in set_roots]
    while stack:
        c, parent = stack.pop()
        p = c.as_pointer()
        if c.get(PARTS_KEY):
            parts.add(p)
            continue
        if (c.library is not None or (holders.get(p, set()) - partners) or p in outside_inst) and p not in own:
            shared.add(p)
            tree.append((c, parent))
            continue
        tree.append((c, parent))
        if p in own:
            continue
        own.add(p)
        order.append(c)
        stack.extend((ch, c) for ch in reversed(list(c.children)))
    objects, seen = [], set()
    for c in [src.collection] + order:
        for ob in c.objects:
            if ob.as_pointer() not in seen:
                seen.add(ob.as_pointer())
                objects.append(ob)
    shared_obs = {ob.as_pointer() for ob in objects
                  if ob.library is not None or any(s.as_pointer() not in partners for s in ob.users_scene)}
    return {"tree": tree, "own": own, "shared": shared, "parts": parts, "objects": objects,
            "shared_obs": shared_obs, "partners": partners}


def split_plan(src, first, last, leave_offstage=True, keep=(), leave=(), footprint=None, every_camera=False):
    """Who and what a copy of beats first..last (0-based) of this staging takes along:
    {"cast": characters and props, "cams": cameras (cams_in_run, or all of them with every_camera), "cams_left",
    "left": left out (with whatever is parented to them), "needed": {name: why it came along anyway}, "paths": drawn
    paths into the beats after the first, "others": everything else of the staging that comes along (Aman's own
    objects, a BB Crowd, a hand prop without a role, lights), "helpers": BB Stage's rig helpers that come along,
    "scope": copy_scope, "frames": (f0, f1), "inner": beat uids after the first}. Anything a copied object points at
    (a parent, a constraint target, a hook, a geometry-nodes input, a driver) comes along too, so a copy never
    depends on its source. keep / leave: names taken along / left out whatever the check says."""
    st0 = src.bb_st
    beats = list(st0.beats)
    n = len(beats)
    if n:
        f0, f1 = beats[first].frame, beat_out(beats[last])
        inner = {b.uid for b in beats[first + 1:last + 1]}
    else:
        f0 = f1 = None
        inner = set()
    whole = not n or (first == 0 and last == n - 1)
    all_cams = stage_cams(src)
    cams = all_cams if (every_camera or whole) else cams_in_run(src, f0, f1, all_cams)
    cam_set = {c.as_pointer() for c in cams}
    cast = stage_objects(src, roles=("char", "prop"))
    paths = [r for r in st0.paths if r.beat_uid in inner
             and all(o is not None and src.objects.get(o.name) == o for o in (r.owner, r.curve, r.follower))]
    movers = {r.owner.as_pointer() for r in paths}
    keep, leave = set(keep or ()), set(leave or ())
    out = set()
    for ob in cast:
        if ob.name in keep or ob.as_pointer() in movers:
            continue
        if ob.name in leave or (leave_offstage and n and offstage_for(src, ob, f0, f1, footprint)):
            out.add(ob.as_pointer())
    needed = {}
    scope = copy_scope(src)
    owned = {o.as_pointer(): o for o in scope["objects"]}
    cast_ptrs = {o.as_pointer() for o in cast}
    cam_all = {c.as_pointer() for c in all_cams}
    base = {p for p, o in owned.items() if o.get(ROLE_KEY) in ("studio", "boundary")}
    extra_helpers = {}

    def rig_helpers():
        hs = {}
        for cam in all_cams:
            if cam.as_pointer() not in cam_set:
                continue
            for h in (aim_of(cam), ride_helper(cam)):
                if h is not None:
                    hs[h.as_pointer()] = h
            e = _eyes_in_range(st0, cam, first, last) if n else (0 if eyes_helper(cam) is not None else None)
            eh = eyes_helper(cam) if e is not None else None
            if eh is not None:
                hs[eh.as_pointer()] = eh
        for r in paths:
            for h in (r.curve, r.follower):
                hs[h.as_pointer()] = h
        return hs

    others, held_back, helpers = [], {}, {}
    for _round in range(len(owned) + 3):          # until nothing new comes along
        grew = False
        for cam in (all_cams if n else ()):
            if cam.as_pointer() not in cam_set:
                continue
            for t, why in _cam_needs(st0, cam, first, last):
                if t.as_pointer() in out:
                    out.discard(t.as_pointer())
                    needed[t.name] = f"{cam.name} {why} {t.name}"
        helpers = rig_helpers()
        helpers.update(extra_helpers)
        taken = base | {p for p in cast_ptrs if p not in out} | cam_set | set(helpers)

        def excluded(o):
            p = o.as_pointer()
            return p in owned and p not in taken and (p in cast_ptrs or p in cam_all
                                                      or o.get(ROLE_KEY) in _HELPER_ROLES)
        others, held_back = [], {}
        for ob in scope["objects"]:
            p = ob.as_pointer()
            if p in cast_ptrs or p in cam_all or ob.get(ROLE_KEY) in _HELPER_ROLES + ("studio", "boundary") \
                    or ob.get(PART_KEY):
                continue
            up = ob.parent
            while up is not None and not excluded(up):
                up = up.parent
            if up is not None:          # parented to somebody who stays behind: stays behind with them
                held_back[p] = up
            else:
                others.append(ob)
                taken.add(p)
        for p in list(taken):
            ob = owned.get(p)
            if ob is None:
                continue
            for t, why in _id_refs(ob):
                tp = t.as_pointer()
                if not isinstance(t, bpy.types.Object) or tp not in owned or tp in taken:
                    continue
                chain, up = [t], t.parent
                while up is not None and tp in held_back:
                    chain.append(up)
                    up = up.parent
                for x in chain:
                    xp = x.as_pointer()
                    if xp in out:
                        out.discard(xp)
                    elif xp in cam_all and xp not in cam_set:
                        cam_set.add(xp)
                    elif x.get(ROLE_KEY) in _HELPER_ROLES and xp not in taken:
                        extra_helpers[xp] = x
                    else:
                        continue
                    needed.setdefault(x.name, f"{ob.name} {why} {t.name}")
                    grew = True
        if not grew:
            break
    left = [o for o in cast if o.as_pointer() in out]
    left += [o for o in scope["objects"] if o.as_pointer() in held_back]
    return {"cast": [o for o in cast if o.as_pointer() not in out], "left": left,
            "cams": [c for c in all_cams if c.as_pointer() in cam_set],
            "cams_left": [c for c in all_cams if c.as_pointer() not in cam_set],
            "needed": needed, "paths": paths, "others": others, "helpers": list(helpers.values()),
            "extra_helpers": list(extra_helpers.values()),
            "scope": scope, "frames": (f0, f1), "inner": inner, "whole": whole}


# ---- keys, copied frame by frame

_ENDS_PATHS = ("location", "rotation_euler", "lens")      # the blocking: keyed on the first beat and the last


def _copy_anim(src_idb, new_idb, acts):
    """Give a copied data-block its own copy of the source's action (copied once when two share one), on its slot."""
    sad = getattr(src_idb, "animation_data", None)
    if sad is None or sad.action is None or new_idb is None:
        return
    act = sad.action
    new_act = acts.get(act.as_pointer())
    if new_act is None:
        new_act = act.copy()
        acts[act.as_pointer()] = new_act
    nad = new_idb.animation_data or new_idb.animation_data_create()
    slot = getattr(sad, "action_slot", None)
    ident = slot.identifier if slot is not None else None
    nad.action = new_act
    if ident is not None and hasattr(new_act, "slots"):
        want = next((s for s in new_act.slots if s.identifier == ident), None)
        if want is not None and nad.action_slot != want:
            try:
                nad.action_slot = want
            except Exception:
                pass


def _lerp2(a, b, t):
    return (a[0] + (b[0] - a[0]) * t, a[1] + (b[1] - a[1]) * t)


def _correct_bezpart(v1, v2, v3, v4):
    """Blender's BKE_fcurve_correct_bezpart: two handles that reach past each other are shortened in proportion
    before the segment is evaluated, so a subdivision starts from the same corrected points."""
    h1 = (v1[0] - v2[0], v1[1] - v2[1])
    h2 = (v4[0] - v3[0], v4[1] - v3[1])
    span = v4[0] - v1[0]
    l1, l2 = abs(h1[0]), abs(h2[0])
    if l1 + l2 == 0.0 or l1 + l2 <= span:
        return v2, v3
    fac = span / (l1 + l2)
    return (v1[0] - fac * h1[0], v1[1] - fac * h1[1]), (v4[0] - fac * h2[0], v4[1] - fac * h2[1])


def _bez_t(x0, x1, x2, x3, x):
    """The parameter at which a key segment's Bezier reaches frame x (its x only grows along a segment)."""
    lo, hi = 0.0, 1.0
    for _ in range(64):
        t = (lo + hi) / 2
        u = 1.0 - t
        if u * u * u * x0 + 3 * u * u * t * x1 + 3 * u * t * t * x2 + t * t * t * x3 < x:
            lo = t
        else:
            hi = t
    return (lo + hi) / 2


def _key_row(x, y, interp, like=None):
    g = like or {}
    return dict(x=float(x), y=float(y), hl=(x - 1.0, y), hr=(x + 1.0, y), hlt='FREE', hrt='FREE', interp=interp,
                kind='KEYFRAME', easing=g.get("easing", 'AUTO'), back=g.get("back", 1.70158),
                amp=g.get("amp", 0.8), period=g.get("period", 4.1), mod=True)


def _insert_exact(rows, x, fc):
    """Put a key on frame x (source frames) that leaves the curve exactly as it was: inside a Bezier segment the
    segment is split in two (de Casteljau, from Blender's own corrected handles), on a straight or stepped segment the
    key sits on it, past the ends it holds the extrapolated value (and the segment to it is flat or straight). An
    eased segment (Sine, Back...) cannot be split exactly: it is keyed on every frame instead (straight in between).
    Keys whose handles change get Free handles. Review s6 #5: an end key with slope handles drifted 4.4 cm."""
    eps = 1e-4
    for r in rows:
        if abs(r["x"] - x) <= eps:
            return r
    i = next((k for k in range(len(rows)) if rows[k]["x"] > x), len(rows))
    lin = fc.extrapolation == 'LINEAR'
    if i == 0 or i == len(rows):
        k = rows[0] if i == 0 else rows[-1]
        y = fc.evaluate(x) if lin else k["y"]
        e = _key_row(x, y, 'LINEAR' if lin else 'CONSTANT', k)
        if i == 0:
            rows.insert(0, e)
        else:
            k["interp"] = 'LINEAR' if lin else 'CONSTANT'
            k["mod"] = True
            rows.append(e)
        return e
    a, b = rows[i - 1], rows[i]
    ip = a["interp"]
    if ip == 'BEZIER':
        v1, v4 = (a["x"], a["y"]), (b["x"], b["y"])
        v2, v3 = _correct_bezpart(v1, a["hr"], b["hl"], v4)
        t = _bez_t(v1[0], v2[0], v3[0], v4[0], x)
        p01, p12, p23 = _lerp2(v1, v2, t), _lerp2(v2, v3, t), _lerp2(v3, v4, t)
        p012, p123 = _lerp2(p01, p12, t), _lerp2(p12, p23, t)
        s = _lerp2(p012, p123, t)
        a["hr"], b["hl"] = p01, p23
        a["mod"] = b["mod"] = True
        e = _key_row(x, s[1], 'BEZIER', a)
        e["hl"], e["hr"] = p012, p123
        rows.insert(i, e)
        return e
    if ip == 'LINEAR':
        e = _key_row(x, a["y"] + (b["y"] - a["y"]) * (x - a["x"]) / max(b["x"] - a["x"], 1e-9), 'LINEAR', a)
        rows.insert(i, e)
        return e
    if ip == 'CONSTANT':
        e = _key_row(x, a["y"], 'CONSTANT', a)
        rows.insert(i, e)
        return e
    a["interp"] = 'LINEAR'                  # an eased segment: on every frame, straight in between
    a["mod"] = True
    xs = sorted({x} | {float(f) for f in range(int(math.floor(a["x"])) + 1, int(math.ceil(b["x"])))
                       if a["x"] + eps < f < b["x"] - eps})
    made = [_key_row(f, fc.evaluate(f), 'LINEAR', a) for f in xs]
    rows[i:i] = made
    return next(r for r in made if abs(r["x"] - x) <= eps)


def _cut_fcurve(fc, off, lo, hi, ends=False):
    """Keep what this curve does on frames lo..hi of the copy (lo + off .. hi + off of the source), shifted back by
    off: every key in there as it was (hand keys between the beats too, keys off the beats like Shemda's in Scene 55),
    and a key on an end where the curve goes on past it, put there so the shape stays exactly the source's
    (_insert_exact). ends: always key both ends (the blocking channels start on the first beat and end on the last)."""
    kps = fc.keyframe_points
    if not len(kps):
        return
    eps = 1e-3
    live = [m for m in fc.modifiers if not m.mute]
    for m in live:
        m.mute = True               # the keys hold the curve's own values: a noise rides on top again
    try:
        rows = [dict(x=k.co.x, y=k.co.y, hl=tuple(k.handle_left), hr=tuple(k.handle_right),
                     hlt=k.handle_left_type, hrt=k.handle_right_type, interp=k.interpolation, kind=k.type,
                     easing=k.easing, back=k.back, amp=k.amplitude, period=k.period, mod=False) for k in kps]
        a, b = lo + off, hi + off
        if ends or rows[0]["x"] < a - eps:
            _insert_exact(rows, a, fc)
        if ends or rows[-1]["x"] > b + eps:
            _insert_exact(rows, b, fc)
    finally:
        for m in live:
            m.mute = False
    idx = [j for j, r in enumerate(rows) if a - eps <= r["x"] <= b + eps]
    new = []
    for j in idx:
        r = rows[j]
        if (j and j - 1 not in idx) or (j + 1 < len(rows) and j + 1 not in idx) or \
                (j == idx[0] and j) or (j == idx[-1] and j + 1 < len(rows)):
            r["mod"] = True         # a neighbour was cut away: an automatic handle would bend to the new one
        new.append(r)
    while len(kps):
        kps.remove(kps[-1], fast=True)
    kps.add(len(new))
    for kp, r in zip(kps, new):
        kp.co = (r["x"] - off, r["y"])
        kp.interpolation = r["interp"]
        kp.type = r["kind"]
        kp.easing = r["easing"]
        kp.back, kp.amplitude, kp.period = r["back"], r["amp"], r["period"]
        kp.handle_left_type, kp.handle_right_type = ('FREE', 'FREE') if r["mod"] else (r["hlt"], r["hrt"])
        kp.handle_left = (r["hl"][0] - off, r["hl"][1])
        kp.handle_right = (r["hr"][0] - off, r["hr"][1])
    for m in fc.modifiers:
        if m.type == 'NOISE':
            m.offset -= off             # the noise reads the same frames it read in the source
        if getattr(m, "use_restricted_range", False):
            m.frame_start -= off
            m.frame_end -= off
    fc.update()


def _cut_action(act, off, lo, hi):
    for fc in channelbag_fcurves(act):
        _cut_fcurve(fc, off, lo, hi, ends=fc.data_path in _ENDS_PATHS)


def _fit_beat_times(scene):
    """Make the Move and Hold times say exactly where the copied beats are (a staging from before 0.9, or a frame
    edited by hand, can disagree with its own times): the keys were copied by frame, so the times follow the frames."""
    st = scene.bb_st
    f = fps(scene)
    for _round in range(len(st.beats) + 1):
        lay = beat_layout(scene)
        bad = next((i for i, (b, ad) in enumerate(zip(st.beats, lay)) if (b.frame, beat_out(b)) != ad), None)
        if bad is None:
            return
        b = st.beats[bad]
        if bad:
            b["move_s"] = max(0.0, (b.frame - beat_out(st.beats[bad - 1])) / f)
        b["hold_s"] = max(0.0, (beat_out(b) - b.frame) / f)


def _camera_at(scene, frame):
    """The camera Blender shows on this frame: the last camera marker at or before it, else the first marker of all,
    else the scene camera (Blender's own rule, BKE_scene_camera_switch_find)."""
    best = first = None
    for m in scene.timeline_markers:
        if m.camera is None or m.camera.hide_render:
            continue
        if m.frame <= frame and (best is None or m.frame > best.frame):
            best = m
        if first is None or m.frame < first.frame:
            first = m
    m = best or first
    return m.camera if m is not None else scene.camera


_COPY_SKIP = {"rna_type", "name", "beats", "paths", "moves", "next_uid", "beat_index", "stage_mode", "prev_workspace",
              "char_index", "prop_index", "cam_index", "new_char_name", "bound_xy", "bound_xy_set", "bound_z",
              "needs_place",
              # merged 0.19: s1's marker ownership and retime memo describe the SOURCE's markers; s1's between-beats
              # flag and s4's Edit Set mode are per-session states of the source
              "beat_marks", "carry_memo", "unsaved_between", "edit_set"}


def _reset_staging_props(st):
    """A Scene.copy() carries the source's whole bb_st: its lists (beats, paths, Move records, and whatever list
    another stream adds) are emptied for the copy to fill, and the per-session values go back to their defaults."""
    for p in st.bl_rna.properties:
        k = p.identifier
        if k in ("rna_type", "name"):
            continue
        if p.type == 'COLLECTION':
            getattr(st, k).clear()
        elif k in _COPY_SKIP and not p.is_readonly:
            try:
                st.property_unset(k)
            except Exception:
                pass


def _base_name(name):
    """A name without Blender's own ".001": the copy takes the next free number of the same name."""
    return re.sub(r"\.\d{3,}$", "", name)


def _relabel(name, old, new):
    """"Characters · Scene 67.001" -> "Characters · Sc 067", "BB Crowd · influencers · STG Jenga" -> "... · STG
    <new>": a name that carries the staging's label carries the copy's. None when it does not."""
    for pre in ("· ", STG_PREFIX):
        k = name.find(pre + old)
        if k < 0:
            continue
        rest = name[k + len(pre + old):]
        rest = re.sub(r"^\.\d{3,}$", "", rest)
        if rest == "" or rest.startswith(" · "):
            return name[:k] + pre + new + rest
    return None


def _sys_props(owner):
    """The system id-properties of a data-block (Blender 5: where registered add-on properties live), or None."""
    get = getattr(owner, "bl_system_properties_get", None)
    try:
        return get() if get is not None else None
    except Exception:
        return None


def copy_staging(src, label, first=None, last=None, leave_offstage=True, keep=(), leave=(), name=None,
                 every_camera=False, settle=True):
    """A new staging on src's set scene from beats first..last (0-based, inclusive) of src, or from all of it, and
    (scene, info) back. The scene is a copy of the source's (Scene.copy: colour management, render and output
    settings, film, EEVEE / Cycles, view layers, custom and other add-ons' scene properties all carried; review s6
    #6), emptied and filled with copies: never shared, so either one can be changed or deleted on its own. What
    comes along (split_plan): the characters, props and cameras of the run, BB Stage's rig helpers, and everything
    else the staging holds (Aman's own objects, a BB Crowd with its cues and influencers, a hand prop, lights), each
    in a copy of the collection it was in, with every pointer between them (parents, constraints, hooks,
    geometry-nodes inputs, drivers, add-on properties) pointing at the copies. A collection another scene also
    holds stays shared and is linked. A run of beats: every key on the stretch from the first beat's arrival to the
    last beat's leaving is copied frame by frame, shifted so the first beat lands on frame 1, the curves cut on the
    ends without changing their shape. The whole staging (Duplicate, Make Independent): every key as it is, on its
    own frames. The source staging is only read. Its studio space and studio pieces are copied too, and the new
    staging is a normal one: Go to, Save Beat, Add Beat, Delete all work on it.

    leave_offstage: leave out characters and props that stay offstage for the whole stretch (offstage_for). keep /
    leave: names to take along / leave out whatever that check says. every_camera: every camera, not only the run's
    (cams_in_run). settle: put everybody on their keys (an unsaved move is not copied); Make Independent keeps it.
    name: the scene name (default "STG <label>"). Raises ValueError with a message for the user when it cannot be
    done."""
    if not is_staging(src):
        raise ValueError(f"{src.name} is not a staging")
    st0 = src.bb_st
    beats = list(st0.beats)
    n = len(beats)
    if n:
        first = 0 if first is None else int(first)
        last = n - 1 if last is None else int(last)
        if not 0 <= first <= last < n:
            raise ValueError(f"{staging_label(src)} has beats B1-B{n}: pick a run of them")
    else:
        first, last = 0, -1
    label = fit_label(label)
    if not label:
        raise ValueError("Give the new staging a name")
    scene_name = name or STG_PREFIX + label
    if bpy.data.scenes.get(scene_name) is not None:
        raise ValueError(f"A staging called '{staging_label(bpy.data.scenes[scene_name])}' already exists")
    set_sc = set_scene_of(src)
    if set_sc is None or set_sc == src or is_staging(set_sc):
        raise ValueError(f"{src.name} plays in no set scene")
    fp = set_footprint(src) if (n and leave_offstage) else None
    plan = split_plan(src, first, last, leave_offstage, keep, leave, fp, every_camera=every_camera)
    whole = plan["whole"]
    f0, f1 = plan["frames"]
    off = 0 if (whole or not n) else f0 - 1
    lo, hi = (f0 - off, f1 - off) if n else (None, None)
    inner = plan["inner"]
    scope = plan["scope"]
    old_label = staging_label(src)
    made = []                       # every new data-block: removed again if the copy fails half way

    sc = src.copy()
    made.append(sc)
    try:
        sc.use_extra_user = True    # ID.copy() from Python hands back 0 users: the file would drop the scene on save
        # (scenes.new() gives a scene this same extra user)
        sc.name = scene_name
        if sc.name != scene_name:
            raise ValueError(f"Blender would not name the copy '{scene_name}'")
        info = _fill_copy(src, sc, plan, label, old_label, first, last, f0, f1, off, lo, hi, inner, scope,
                          set_sc, whole, settle, made)
    except BaseException:
        gone = set()
        for idb in reversed(made):
            try:
                p = idb.as_pointer()
                if p in gone:           # removed already: batch_remove on a freed ID crashes Blender
                    continue
                gone.add(p)
                if isinstance(idb, bpy.types.Scene):
                    bpy.data.scenes.remove(idb)
                elif isinstance(idb, bpy.types.Object):
                    bpy.data.objects.remove(idb)
                elif isinstance(idb, bpy.types.Collection):
                    bpy.data.collections.remove(idb)
                else:
                    bpy.data.batch_remove([idb])
            except (ReferenceError, RuntimeError, TypeError):
                pass
        raise
    return sc, info


def _fill_copy(src, sc, plan, label, old_label, first, last, f0, f1, off, lo, hi, inner, scope, set_sc, whole,
               settle, made):
    st0 = src.bb_st
    beats = list(st0.beats)
    n = len(beats)

    # ---- the scene: Scene.copy() links everything of the source; unlink it all, keep the settings
    for c in list(sc.collection.children):
        sc.collection.children.unlink(c)
    for ob in list(sc.collection.objects):
        sc.collection.objects.unlink(ob)
    sc.timeline_markers.clear()
    sc.camera = None                # the source's camera: the copy picks its own once its cameras exist
    st = sc.bb_st
    _reset_staging_props(st)
    st.beat_marks = "{}"            # synced by 0.19 from the start: a marker of yours called "B7" is never a beat's
    if sc.animation_data is not None and sc.animation_data.action is not None:
        sc.animation_data.action = sc.animation_data.action.copy()       # scene-level keys: its own
        made.append(sc.animation_data.action)
    wrapper = link_set(sc, set_sc)
    made.append(wrapper)

    # ---- its collections: copies of the source's own (settings and tags kept), the shared ones linked
    cmap = {}                   # source collection pointer: its copy
    pairs_c = []
    for c, parent in scope["tree"]:
        p = c.as_pointer()
        new_parent = sc.collection if parent == src.collection else cmap.get(parent.as_pointer())
        if new_parent is None:
            continue
        if p in scope["shared"]:
            if new_parent.children.get(c.name) != c:
                new_parent.children.link(c)
            continue
        newc = cmap.get(p)
        if newc is None:
            newc = c.copy()
            made.append(newc)
            for o in list(newc.objects):
                newc.objects.unlink(o)
            for ch in list(newc.children):
                newc.children.unlink(ch)
            newc.name = _relabel(c.name, old_label, label) or _base_name(c.name)
            cmap[p] = newc
            pairs_c.append((c, newc))
        if new_parent.children.get(newc.name) != newc:
            new_parent.children.link(newc)
    studio_root = next((cmap.get(c.as_pointer()) for c in layer_colls(src, "STUDIO")), None)
    stage_root = next((cmap.get(c.as_pointer()) for c in layer_colls(src, "STAGE")), None)
    if studio_root is None:
        studio_root = bpy.data.collections.new(f"STUDIO · {label}")
        made.append(studio_root)
        studio_root[LAYER_KEY] = "STUDIO"
        sc.collection.children.link(studio_root)
    if stage_root is None:
        stage_root = bpy.data.collections.new(f"STAGE · {label}")
        made.append(stage_root)
        stage_root[LAYER_KEY] = "STAGE"
        sc.collection.children.link(stage_root)
    st.set_coll, st.studio_coll, st.stage_coll = wrapper, studio_root, stage_root
    subs = {}
    for child, attr in (("Characters", "chars_coll"), ("Props", "props_coll"), ("Cameras", "cams_coll")):
        c0 = sub_coll(src, "STAGE", child)
        c = cmap.get(c0.as_pointer()) if c0 is not None else None
        if c is None:
            c = bpy.data.collections.new(f"{child} · {label}")
            made.append(c)
            c[SUB_KEY] = child
            stage_root.children.link(c)
        subs[child] = c
        setattr(st, attr, c)

    # ---- its own studio space, where the source's is (B11)
    b0 = boundary_of(src)
    bound = build_boundary_object(label, st.studio_w, st.studio_d, st.studio_h)
    made.extend([bound, bound.data])
    home = [cmap[c.as_pointer()] for c in (b0.users_collection if b0 is not None else ()) if c.as_pointer() in cmap]
    for c in (home or [studio_root]):
        c.objects.link(bound)
    st.boundary = bound
    if b0 is not None:
        bound.location = b0.location
        bound.rotation_euler.z = b0.rotation_euler.z
    else:
        c = set_bounds_center(sc)
        bound.location = (c.x, c.y, st.floor_z)
    st.bound_xy = (bound.location.x, bound.location.y)
    st.bound_z = bound.location.z
    st.bound_xy_set = True

    # ---- the objects: copies with their own data and actions
    obmap, pairs, acts, datamap = {}, [], {}, {}
    if b0 is not None:
        obmap[b0.as_pointer()] = bound
    owned = {o.as_pointer() for o in scope["objects"]}
    in_master = {o.as_pointer() for o in src.collection.objects}

    def homes(ob, fallback):
        out = [cmap[c.as_pointer()] for c in ob.users_collection if c.as_pointer() in cmap]
        if ob.as_pointer() in in_master:
            out.append(sc.collection)
        return out or [fallback]

    def own_data(ob):
        """A role-less object's data is copied when only this staging uses it; data the set or another staging
        shares (a set piece taken into the staging, s4) stays shared."""
        d = ob.data
        if d is None or ob.get(SETPIECE_KEY):
            return False
        if ob.get(ROLE_KEY) and ob.get(ROLE_KEY) not in ("",):
            return True
        users = sum(1 for o in scope["objects"] if o.data == d)
        return d.users - (1 if d.use_fake_user else 0) <= users

    def dup(ob, fallback, new_name):
        new = ob.copy()
        made.append(new)
        if ob.data is not None and own_data(ob):
            d = datamap.get(ob.data.as_pointer())
            if d is None:
                d = ob.data.copy()
                made.append(d)
                datamap[ob.data.as_pointer()] = d
            new.data = d
        new.name = new_name
        if new.data is not None and new.data != ob.data and ob.type in ('MESH', 'CAMERA', 'CURVE') \
                and new.data.users == 1:
            new.data.name = new.name
        for c in homes(ob, fallback):
            c.objects.link(new)
        obmap[ob.as_pointer()] = new
        pairs.append((ob, new))
        _copy_anim(ob, new, acts)
        if ob.data is not None and new.data != ob.data:
            _copy_anim(ob.data, new.data, acts)
            sk = getattr(ob.data, "shape_keys", None)
            if sk is not None:
                _copy_anim(sk, getattr(new.data, "shape_keys", None), acts)
        return new

    def name_for(ob):
        return _relabel(ob.name, old_label, label) or _base_name(ob.name)

    for ob in scope["objects"]:         # the studio pieces
        if ob.get(ROLE_KEY) in ("studio",) and ob.as_pointer() not in obmap:
            dup(ob, studio_root, name_for(ob))
    for ob in plan["cast"]:
        dup(ob, subs["Characters"] if ob.get(ROLE_KEY) == "char" else subs["Props"], _base_name(ob.name))
    eyes_keep = {}
    for cam in plan["cams"]:
        new = dup(cam, subs["Cameras"], _base_name(cam.name))
        aim = aim_of(cam)
        if aim is not None and aim.as_pointer() not in obmap:
            dup(aim, subs["Cameras"], f"Aim · {new.name}")
        h = ride_helper(cam)
        if h is not None and h.as_pointer() not in obmap:
            dup(h, subs["Cameras"], f"Ride · {new.name}")
        e = _eyes_in_range(st0, cam, first, last) if n else (0 if eyes_helper(cam) is not None else None)
        eyes_keep[new.as_pointer()] = e
        eh = eyes_helper(cam) if e is not None else None
        if eh is not None and eh.as_pointer() not in obmap:
            who = obmap.get(eh.parent.as_pointer()) if eh.parent is not None else None
            dup(eh, subs["Cameras"], f"Eyes · {who.name}" if who is not None else _base_name(eh.name))
    new_index = {b.uid: k for k, b in enumerate(beats[first:last + 1])}
    path_rows = []
    for r in plan["paths"]:
        owner = obmap.get(r.owner.as_pointer())
        if owner is None:
            continue
        pcoll = paths_coll(sc)
        cname, fname = _path_names(owner, new_index[r.beat_uid])
        path_rows.append((r, owner, dup(r.curve, pcoll, cname), dup(r.follower, pcoll, fname)))
    shared_linked = []
    for ob in plan["others"]:
        if ob.as_pointer() in obmap:
            continue
        if ob.as_pointer() in scope["shared_obs"]:      # the set or another scene shows it too: linked, not copied
            for c in homes(ob, stage_root):
                if c.objects.get(ob.name) != ob:
                    c.objects.link(ob)
            shared_linked.append(ob.name)
            continue
        dup(ob, stage_root, name_for(ob))
    for h in plan["helpers"] + plan["extra_helpers"]:     # a helper something else needs (not through its camera)
        if h.as_pointer() not in obmap and h.as_pointer() in owned:
            dup(h, stage_root, _base_name(h.name))
    for a in acts.values():
        if a not in made:
            made.append(a)

    # ---- per-object data-blocks: a geometry-nodes group or material named for its object (a BB Crowd's own
    # choreography tree, its peg material) is that object's: copied with it, so syncing one crowd leaves the other
    extra = {}
    for ob, new in pairs:
        for m in new.modifiers:
            cands = []
            if m.type == 'NODES' and m.node_group is not None:
                cands.append(m.node_group)
            if m.type == 'NODES' and hasattr(m, "properties"):
                try:
                    inp = m.properties.inputs
                    for p in inp.bl_rna.properties:
                        sock = getattr(inp, p.identifier, None) if p.identifier != "rna_type" else None
                        v = getattr(sock, "value", None) if sock is not None else None
                        if isinstance(v, (bpy.types.Material, bpy.types.NodeTree)):
                            cands.append(v)
                except Exception:
                    pass
            for d in cands:
                if d.as_pointer() in extra or d.library is not None or ob.name not in d.name:
                    continue
                d2 = d.copy()
                made.append(d2)
                d2.name = d.name.replace(ob.name, new.name)
                extra[d.as_pointer()] = d2

    # ---- every reference points at the copies
    idmap = {p: o for p, o in obmap.items()}
    idmap.update({p: c for p, c in cmap.items()})
    idmap.update(extra)
    idmap[src.as_pointer()] = sc
    copied = set(obmap) | set(cmap)
    drop = ((owned - scope["shared_obs"]) | scope["own"]) - copied      # the source's own, not copied: cleared

    def remap(ob):
        return obmap.get(ob.as_pointer(), ob) if ob is not None else None

    def visit(owner, k, v):
        return idmap.get(v.as_pointer())

    for ob, new in pairs:
        if new.parent is not None and new.parent.as_pointer() in obmap:
            mpi = new.matrix_parent_inverse.copy()      # setting a parent resets it
            new.parent = obmap[new.parent.as_pointer()]
            new.matrix_parent_inverse = mpi
        _walk_ids(new, visit)
        if new.data is not None and new.data != ob.data:
            _walk_ids(new.data, visit)
            sk = getattr(new.data, "shape_keys", None)
            if sk is not None:
                _walk_ids(sk, visit)
            _remap_props(new.data, idmap, drop)
        _remap_props(new, idmap, drop)
        new.update_tag()
    for c0, newc in pairs_c:
        _remap_props(newc, idmap, drop)
    for d2 in extra.values():
        if isinstance(d2, bpy.types.NodeTree):
            for node in d2.nodes:
                _walk_ids(node, visit, depth=5)
                for sock in node.inputs:
                    v = getattr(sock, "default_value", None)
                    if isinstance(v, bpy.types.ID) and v.as_pointer() in idmap:
                        try:
                            sock.default_value = idmap[v.as_pointer()]
                        except Exception:
                            pass

    for ob, new in pairs:
        if not n:
            continue
        wins = new.get(MOVE_KEY)
        if wins is not None:
            try:
                d = wins.to_dict()
            except AttributeError:
                d = {}
            d = {k: [int(v[0]) - off, int(v[1]) - off] for k, v in d.items() if str(k).isdigit() and int(k) in inner}
            if d:
                new[MOVE_KEY] = d
            else:
                del new[MOVE_KEY]
        if new.type != 'CAMERA':
            continue
        if LOOK_KEY in new:
            # merged 0.19 (s2 review 9): an entry is a rider key, and the rider's TARGET says who is tracked (a key
            # can still carry an old name after a rename). Resolve it on the source, map it to the copy, and give the
            # copied aim its own rider for it; the old riders go (apply_look keys the influences from the table).
            src_tgts = {}
            for k, v in _looks_in_range(st0, ob, first, last).items():
                src_tgts[k] = v if v in ("", LOOK_OFF) else look_target(ob, v)
            aim = aim_of(new)
            for c in (list(aim.constraints) if aim is not None else ()):
                if c.name.startswith(AIM_CON):
                    _drop_fcurves(aim, {f'constraints["{c.name}"].influence'})
                    aim.constraints.remove(c)
            tab = {}
            for k, t in src_tgts.items():
                if isinstance(t, str):
                    tab[k] = t
                elif t is not None and aim is not None:
                    tab[k] = _ensure_rider(aim, remap(t))
            if tab:
                new[LOOK_KEY] = {str(k): v for k, v in tab.items()}
            else:
                del new[LOOK_KEY]
        e = eyes_keep.get(new.as_pointer())
        con = new.constraints.get(EYES_CON)
        if e is None and con is not None:           # it left the eyes before the run: the camera is its own
            new.constraints.remove(con)
            _drop_fcurves(new, {EYES_INF})
            if EYES_KEY in new:
                del new[EYES_KEY]
        elif e is not None and EYES_KEY in new:
            new[EYES_KEY] = [int(e), float(step_off(ob)[1])]
        aim = aim_of(new)
        for c in (list(aim.constraints) if (aim is not None and LOOK_KEY not in new) else ()):
            if c.name.startswith(AIM_CON):          # no look in the run: no rider is needed
                _drop_fcurves(aim, {f'constraints["{c.name}"].influence'})
                aim.constraints.remove(c)
    for r, owner, curve, fol in path_rows:
        rec = st.paths.add()
        rec.owner, rec.curve, rec.follower, rec.beat_uid = owner, curve, fol, r.beat_uid
        rec["face_path"] = bool(r.face_path)
    if n and not whole:
        for act in acts.values():
            _cut_action(act, off, lo, hi)
        if sc.animation_data is not None and sc.animation_data.action is not None:
            _cut_action(sc.animation_data.action, off, lo, hi)
        for ob, new in pairs:          # BB Crowd: the frames a cue reads its source on and walks between
            for g in [x for x in (_sys_props(new),) if x is not None]:
                try:
                    cues = list(g.get("bb_crowd_cues") or ())
                except Exception:
                    cues = []
                for cue in cues:
                    for k in ("frame", "win_a", "win_b", "key_a", "key_b"):
                        try:
                            if k in cue and int(cue[k]):
                                cue[k] = int(cue[k]) - off
                        except Exception:
                            pass

    # ---- beats, timings, markers, cuts
    for i in range(first, last + 1):
        b0_ = beats[i]
        b = st.beats.add()
        for k, v in b0_.items():                    # every field, whichever stream added it
            try:
                b[k] = v.to_dict() if hasattr(v, "to_dict") else (v.to_list() if hasattr(v, "to_list") else v)
            except (TypeError, ValueError, KeyError):
                pass
        b.uid = b0_.uid
        b.frame = b0_.frame - off
        b.frame_out = beat_out(b0_) - off
        b["move_s"] = 0.0 if (i == first and not whole) else float(b0_.move_s)
        b["hold_s"] = float(b0_.hold_s)
        b["label"] = b0_.label
        b["note"] = b0_.note
        if settle and "dirty" in b:
            b["dirty"] = False                      # an unsaved move is not copied (settle puts the keys back)
    st["next_uid"] = max(int(st0.next_uid), max([b.uid for b in beats] + [0]) + 1)
    st["beat_index"] = int(st0.beat_index) if whole else 0
    st["needs_place"] = False
    for m0 in st0.moves:
        owner = obmap.get(m0.owner.as_pointer()) if m0.owner is not None else None
        if owner is None or m0.beat_uid not in inner:
            continue
        m = st.moves.add()
        m.owner, m.beat_uid = owner, m0.beat_uid
        for k in ("start_s", "end_s", "face"):
            if k in m0:
                m[k] = m0[k]
    cuts = 0
    if n:
        _fit_beat_times(sc)
        if whole:
            sc.frame_start, sc.frame_end = src.frame_start, src.frame_end
        else:
            sc.frame_start, sc.frame_end = 1, max(hi, 2)
        sync_markers(sc)
        for i in range(first, last + 1):
            m0 = beat_marker(src, i)
            m = beat_marker(sc, i - first)
            if m0 is not None and m0.camera is not None and m is not None:
                m.camera = remap(m0.camera)
    for m0 in src.timeline_markers:
        if _is_beat_marker(m0) or (n and not whole and not f0 <= m0.frame <= f1):
            continue
        if m0.camera is not None and m0.camera.as_pointer() not in obmap and m0.camera.as_pointer() in owned:
            continue                                # a cut to a camera the run does not take
        m = sc.timeline_markers.new(m0.name, frame=m0.frame - off)
        if m0.camera is not None:
            m.camera = remap(m0.camera)
            cuts += 1
    if n:
        want = remap(_camera_at(src, f0))
        if want is not None:
            have = _camera_at(sc, lo)
            if have is not None and have != want:   # the cut that was running when the run starts
                m = sc.timeline_markers.new(f"{CUT_PREFIX}{want.name}", frame=lo)
                m.camera = want
            sc.camera = want
    if sc.camera is None or sc.camera.as_pointer() not in {o.as_pointer() for o in obmap.values()}:
        cams = stage_cams(sc)
        sc.camera = remap(src.camera) if (src.camera is not None and src.camera.as_pointer() in obmap) else \
            (cams[0] if cams else None)
    _remap_props(sc, idmap, drop)                    # bb_st (cam0, cam1...), BB Crowd's scene pointers, any add-on's

    # ---- settle: everybody on their keys, derived rigs rebuilt from the copied tables
    sc.frame_current = (lo or 1) if not whole else src.frame_current
    if settle:
        for ob, new in pairs:
            ad = new.animation_data
            if ad is not None and ad.action is not None:
                new.location = keyed_location_at(new, sc.frame_current)
                new.rotation_euler = keyed_rotation_at(new, sc.frame_current)
                fc = lens_fcurve(new)
                if fc is not None:
                    new.data.lens = fc.evaluate(sc.frame_current)
    sync_peg_colors(sc)
    if n:
        refresh_paths(sc)           # the paths on their new beat numbers (B5 into B2...), pinned and timed
        apply_look(sc)
        apply_eyes(sc)
    else:
        _strip_stray_path_constraints(sc)
    sc[SPLIT_KEY] = f"{src.name}" + (f" B{first + 1}-B{last + 1} (frames {f0}-{f1})" if n else "")
    refresh_set_edits(sc, adopt=True, structural=True)  # s4: a taken set piece gets its record, parts, exclusion
    migrate_staging(sc)
    for vl in src.view_layers:                      # what the source's view layers hid, the copy's hide too
        nvl = sc.view_layers.get(vl.name)
        if nvl is None:
            continue
        for c0, newc in pairs_c:
            a = find_layer_collection(vl.layer_collection, c0)
            b = find_layer_collection(nvl.layer_collection, newc)
            for k in (("exclude", "hide_viewport", "holdout", "indirect_only") if a is not None and b is not None else ()):
                try:
                    if getattr(b, k) != getattr(a, k):
                        setattr(b, k, getattr(a, k))
                except Exception:
                    pass
    normalize_view_layer(sc)
    left = [o.name for o in plan["left"]]
    others = [obmap[o.as_pointer()].name for o in plan["others"] if o.as_pointer() in obmap]
    accounted = set(obmap) | {o.as_pointer() for o in plan["left"]} | {o.as_pointer() for o in plan["cams_left"]}
    not_copied = [o.name for o in scope["objects"]       # nothing of the staging may go missing silently (review s6 #4)
                  if o.as_pointer() not in accounted and o.as_pointer() not in scope["shared_obs"]
                  and o.get(ROLE_KEY) not in _HELPER_ROLES + ("boundary",) and not o.get(PART_KEY)]
    info = {"scene": sc.name, "source": src.name, "beats": [first + 1, last + 1] if n else [],
            "frames": [f0, f1] if n else [], "offset": off,
            "cast": [obmap[o.as_pointer()].name for o in plan["cast"]],
            "cameras": [obmap[c.as_pointer()].name for c in plan["cams"]],
            "cameras_left": [c.name for c in plan["cams_left"]],
            "left_out": left, "needed": dict(plan["needed"]), "others": others, "shared": shared_linked
            + [c.name for c, _p in scope["tree"] if c.as_pointer() in scope["shared"]],
            "paths": len(path_rows), "cuts": cuts, "not_copied": not_copied,
            "map": {ob.name: new.name for ob, new in pairs},
            "unsaved": [i + 1 for i in range(first, last + 1) if beats[i].dirty] if (n and settle) else []}
    return info


def split_beats(src, first, last, label, leave_offstage=True, keep=(), leave=(), every_camera=False):
    """Split off Beats for scripts: beats first..last (0-based) of the staging src into a new staging (see
    copy_staging). Returns (scene, info)."""
    return copy_staging(src, label, first, last, leave_offstage, keep, leave, every_camera=every_camera)


def _split_source(op, context):
    sc = bpy.data.scenes.get(op.scene_name) if op.scene_name else context.scene
    return sc if is_staging(sc) else None


def _auto_label(src, first, last):
    a, b = first + 1, last + 1
    return unique_label(f"{staging_label(src)} B{a}" + (f"-B{b}" if b != a else ""))


def _copy_message(info):
    bits = [f"{len(info['cast'])} cast", f"{len(info['cameras'])} camera(s)"]
    if info.get("others"):
        bits.append(f"{len(info['others'])} other object(s)")
    if info["paths"]:
        bits.append(f"{info['paths']} path(s)")
    if info["cuts"]:
        bits.append(f"{info['cuts']} cut(s)")
    msg = f"{info['scene']}: " + ", ".join(bits)
    if info["left_out"]:
        msg += " · left offstage: " + ", ".join(info["left_out"][:8])
    if info.get("shared"):
        msg += " · shared: " + ", ".join(info["shared"][:3])
    if info["not_copied"]:
        msg += f" · not copied: {', '.join(info['not_copied'][:4])}"
    if info["unsaved"]:
        msg += f" · unsaved moves on B{info['unsaved'][0]} were not copied"
    return msg


def _plan_lines(col, plan, every):
    """The preview of a copy: who and what it takes, what it leaves, what it shares."""
    cast = [o.name for o in plan["cast"]]
    col.label(text=f"Takes {len(cast)}: " + (", ".join(cast[:6]) + (" ..." if len(cast) > 6 else "") or "nobody"),
              icon='COMMUNITY')
    nc = len(plan["cams"])
    col.label(text=f"{nc} camera(s)" + ("" if every or not plan["cams_left"] else
                                        f" of {nc + len(plan['cams_left'])}: the ones this run shows")
              + f", {len(plan['paths'])} drawn path(s)", icon='OUTLINER_OB_CAMERA')
    if plan["others"]:
        oth = [o.name for o in plan["others"]]
        col.label(text=f"And {len(oth)} more: " + ", ".join(oth[:3]) + (" ..." if len(oth) > 3 else ""), icon='OBJECT_DATA')
    shared = [c.name for c, _p in plan["scope"]["tree"] if c.as_pointer() in plan["scope"]["shared"]]
    if shared:
        col.label(text="Shared, not copied: " + ", ".join(shared[:3]) + (" ..." if len(shared) > 3 else ""),
                  icon='LINKED')
    if plan["left"]:
        left = [o.name for o in plan["left"]]
        col.label(text="Leaves offstage: " + ", ".join(left[:6]) + (" ..." if len(left) > 6 else ""), icon='HIDE_ON')
    for why in list(plan["needed"].values())[:2]:
        col.label(text=f"Brought along: {why}", icon='INFO')


class BBST_OT_split_beats(bpy.types.Operator):
    """Copy a run of beats into a new staging on the same set: whoever takes part comes along with every key they
have there, and the first beat lands on frame 1. Characters parked offstage for the whole run stay behind. This
staging is not changed"""
    bl_idname = "bbst.split_beats"
    bl_label = "Split off Beats"
    bl_options = {'REGISTER', 'UNDO'}

    scene_name: bpy.props.StringProperty(options={'SKIP_SAVE'})
    from_beat: bpy.props.IntProperty(name="From beat", default=1, min=1, soft_max=60,
                                     description="The first beat of the run: it lands on frame 1 of the new staging")
    to_beat: bpy.props.IntProperty(name="To beat", default=1, min=1, soft_max=60,
                                   description="The last beat of the run")
    label: bpy.props.StringProperty(name="Name", default="", options={'SKIP_SAVE'},
                                    description="The new staging's name (empty: this staging's name and the beats)")
    leave_offstage: bpy.props.BoolProperty(
        name="Leave out who stays offstage", default=True,
        description="Characters and props that stay outside the studio space and the set for the whole run are not "
                    "copied (a camera that needs one of them brings them along)")
    every_camera: bpy.props.BoolProperty(
        name="Every camera", default=False,
        description="Take every camera of this staging. Off: only the cameras this run shows (the one live when it "
                    "starts, every one cut to inside it) and the cameras no cut names")
    open_it: bpy.props.BoolProperty(name="Open it", default=True, description="Go to the new staging once it is made")

    def invoke(self, context, event):
        src = _split_source(self, context)
        if src is None or not len(src.bb_st.beats):
            self.report({'ERROR'}, "Open a staging with beats first")
            return {'CANCELLED'}
        st0 = src.bb_st
        i = min(max(st0.beat_index, 0), len(st0.beats) - 1)
        self.scene_name = src.name
        self.from_beat = self.to_beat = i + 1
        _PLAN_CACHE.clear()
        set_footprint(src, fresh=True)
        return context.window_manager.invoke_props_dialog(self, width=460, confirm_text="Split")

    def draw(self, context):
        lay = self.layout
        src = _split_source(self, context)
        if src is None:
            lay.label(text="Not a staging", icon='ERROR')
            return
        st0 = src.bb_st
        n = len(st0.beats)
        a, b = self.from_beat - 1, self.to_beat - 1
        ok = 0 <= a <= b < n
        row = lay.row(align=True)
        row.prop(self, "from_beat")
        row.prop(self, "to_beat")
        lay.prop(self, "label", placeholder=(f"{staging_label(src)} B{a + 1}" + (f"-B{b + 1}" if b != a else ""))
                 if ok else "Name")
        row = lay.row()
        row.prop(self, "leave_offstage")
        row.prop(self, "every_camera")
        lay.prop(self, "open_it")
        col = lay.column(align=True)
        if not ok:
            col.alert = True
            col.label(text=f"Pick a run of beats between B1 and B{n}", icon='ERROR')
            return
        try:
            key = (src.name, a, b, self.leave_offstage, self.every_camera, n)
            plan = _PLAN_CACHE.get(key)
            if plan is None:
                hit = _FOOTPRINT.get(src.name)
                fp = hit[1] if hit is not None else set_footprint(src, evaluate=False)
                plan = split_plan(src, a, b, self.leave_offstage, footprint=fp, every_camera=self.every_camera)
                _PLAN_CACHE.clear()
                _PLAN_CACHE[key] = plan
            bs, be = st0.beats[a], st0.beats[b]
            f0, f1 = bs.frame, beat_out(be)
            col.label(text=f"B{a + 1} {bs.label}".strip() + (f"  to  B{b + 1} {be.label}".rstrip() if b != a else ""),
                      icon='KEYFRAME_HLT')
            col.label(text=f"Frames {f0}-{f1} ({(f1 - f0) / fps(src):.1f} s), from frame 1 in the new staging",
                      icon='TIME')
            _plan_lines(col, plan, self.every_camera)
            dirty = [k + 1 for k in range(a, b + 1) if st0.beats[k].dirty]
            if dirty:
                r = col.row()
                r.alert = True
                r.label(text=f"B{dirty[0]} has unsaved moves: they are not copied (Save Beat first)", icon='ERROR')
        except (ReferenceError, IndexError, AttributeError):
            _PLAN_CACHE.clear()

    def execute(self, context):
        src = _split_source(self, context)
        if src is None:
            self.report({'ERROR'}, "Split off Beats works on a staging")
            return {'CANCELLED'}
        n = len(src.bb_st.beats)
        a, b = self.from_beat - 1, self.to_beat - 1
        if not n or not 0 <= a <= b < n:
            self.report({'ERROR'}, f"Pick a run of beats between B1 and B{max(n, 1)}")
            return {'CANCELLED'}
        if context.mode != 'OBJECT':
            self.report({'ERROR'}, "Finish editing first (Done), then split")
            return {'CANCELLED'}
        label = fit_label(self.label) or _auto_label(src, a, b)
        try:
            sc, info = copy_staging(src, label, a, b, self.leave_offstage, every_camera=self.every_camera)
        except ValueError as e:
            self.report({'ERROR'}, str(e))
            return {'CANCELLED'}
        _PLAN_CACHE.clear()
        if self.open_it and context.window is not None:
            bpy.ops.bbst.goto_scene(scene_name=sc.name)
        self.report({'WARNING'} if (info["unsaved"] or info["not_copied"]) else {'INFO'}, _copy_message(info))
        return {'FINISHED'}


class BBST_OT_duplicate_staging(bpy.types.Operator):
    """A copy of this staging on the same set, made by BB Stage: its studio, characters, props, cameras, beats, paths
and cuts, everything else it holds (a crowd, your own objects) and its scene settings, every key as it is. Nothing
is shared but what the set or another staging shares too, so either one can be changed or deleted on its own (never
use Blender's New Scene > Linked Copy for a staging)"""
    bl_idname = "bbst.duplicate_staging"
    bl_label = "Duplicate Staging"
    bl_options = {'REGISTER', 'UNDO'}

    scene_name: bpy.props.StringProperty(options={'SKIP_SAVE'})
    label: bpy.props.StringProperty(name="Name", default="", options={'SKIP_SAVE'})
    open_it: bpy.props.BoolProperty(name="Open it", default=True, description="Go to the copy once it is made")

    def invoke(self, context, event):
        src = _split_source(self, context)
        if src is None:
            self.report({'ERROR'}, "Open a staging first")
            return {'CANCELLED'}
        self.scene_name = src.name
        self.label = unique_label(f"{staging_label(src)} copy")
        _PLAN_CACHE.clear()
        return context.window_manager.invoke_props_dialog(self, width=420, confirm_text="Duplicate")

    def draw(self, context):
        lay = self.layout
        lay.prop(self, "label")
        lay.prop(self, "open_it")
        src = _split_source(self, context)
        if src is None:
            return
        try:
            key = (src.name, "dup", len(src.bb_st.beats))
            plan = _PLAN_CACHE.get(key)
            if plan is None:
                n = len(src.bb_st.beats)
                plan = split_plan(src, 0, max(n - 1, 0) if n else -1, False, every_camera=True)
                _PLAN_CACHE.clear()
                _PLAN_CACHE[key] = plan
            _plan_lines(lay.column(align=True), plan, True)
        except (ReferenceError, IndexError, AttributeError):
            _PLAN_CACHE.clear()

    def execute(self, context):
        src = _split_source(self, context)
        if src is None:
            self.report({'ERROR'}, "Duplicate Staging works on a staging")
            return {'CANCELLED'}
        if context.mode != 'OBJECT':
            self.report({'ERROR'}, "Finish editing first (Done), then duplicate")
            return {'CANCELLED'}
        label = fit_label(self.label) or unique_label(f"{staging_label(src)} copy")
        try:
            sc, info = copy_staging(src, label, leave_offstage=False, every_camera=True)
        except ValueError as e:
            self.report({'ERROR'}, str(e))
            return {'CANCELLED'}
        _PLAN_CACHE.clear()
        if self.open_it and context.window is not None:
            bpy.ops.bbst.goto_scene(scene_name=sc.name)
        self.report({'WARNING'} if info["not_copied"] else {'INFO'}, _copy_message(info))
        return {'FINISHED'}


def _replace_with_copy(context, sc):
    """Give this staging copies of its own of everything it holds (copy_staging, whole, keys and unsaved poses as
    they are) under its own name, then delete the old scene: what another scene still uses stays theirs (B3).
    Returns (new scene, info)."""
    name, label = sc.name, staging_label(sc)
    k = 1
    while bpy.data.scenes.get(f"{STG_PREFIX}~{k}") is not None:
        k += 1
    sc.name = f"{STG_PREFIX}~{k}"           # the copy takes the name back
    try:
        new, info = copy_staging(sc, label, leave_offstage=False, name=name, every_camera=True, settle=False)
    except ValueError:
        sc.name = name
        raise
    showing = any(w.scene == sc for w in context.window_manager.windows)
    _windows_off(context, sc, to=new)
    delete_staging_data(sc)
    if showing and stage_on() and context.window is not None and context.window.workspace.name == WS_NAME:
        _build_stage_screen(new.name)
    return new, info


class BBST_OT_make_independent(bpy.types.Operator):
    """This staging shares its studio and cast with another scene: it was made with Blender's New Scene > Linked Copy,
so moving a character in one moves it in the other. After this they share nothing: the original keeps its own
objects and names, and its Linked Copy gets copies of everything the two shared (characters, cameras, crowds, your
own objects, scene settings; nothing moves)"""
    bl_idname = "bbst.make_independent"
    bl_label = "Make Independent"
    bl_options = {'REGISTER', 'UNDO'}

    scene_name: bpy.props.StringProperty()

    def execute(self, context):
        sc = bpy.data.scenes.get(self.scene_name) if self.scene_name else context.scene
        if not is_staging(sc) or not shared_with(sc):
            return {'CANCELLED'}
        if context.mode != 'OBJECT':
            self.report({'ERROR'}, "Finish editing first (Done)")
            return {'CANCELLED'}
        name = sc.name
        # Blender names a Linked Copy "<name>.001": clicked on the original, the copies get the new objects, so the
        # original keeps its own (and their names: no Jai.001 where Jai was). Review s6 #2 and #9, 15 Oct 2026.
        targets = [s.name for s in shared_with(sc) if is_staging(s) and _base_name(s.name) == name and s.name != name]
        targets = targets or [name]
        done, not_copied = [], []
        try:
            for t in targets:
                new, info = _replace_with_copy(context, bpy.data.scenes[t])
                done.append(staging_label(new))
                not_copied += info["not_copied"]
            me = bpy.data.scenes.get(name)
            if me is not None and shared_with(me):      # still shares with a scene that is not its "<name>.NNN"
                new, info = _replace_with_copy(context, me)
                done.append(staging_label(new))
                not_copied += info["not_copied"]
        except ValueError as e:
            self.report({'ERROR'}, str(e))
            return {'CANCELLED'}
        msg = f"{staging_label(bpy.data.scenes[name])} shares nothing now ({', '.join(done)}: copies of their own)"
        if not_copied:
            msg += f" · not copied: {', '.join(not_copied[:4])}"
        self.report({'WARNING'} if not_copied else {'INFO'}, msg)
        return {'FINISHED'}


def draw_split_beats(lay, context):
    """Beats panel (Artist): Split off Beats (Aman, 15 Oct 2026)."""
    scene = context.scene
    if _mode() != 'ARTIST' or not is_staging(scene) or not len(scene.bb_st.beats):
        return
    lay.operator("bbst.split_beats", text="Split off Beats…", icon='SPLIT_HORIZONTAL').scene_name = scene.name


def draw_staging_copies(lay, context):
    """Sidebar header: for stagings that share their studio and cast (Blender's Linked Copy, B4) a warning with its
    fix, in Easy and Artist alike (review s6 #9: it was Artist-only). Duplicate Staging is in the header's … menu."""
    done = set()
    for s in stagings():
        if s.as_pointer() in done:
            continue
        others = shared_with(s)
        if not others:
            continue
        group = [s] + [o for o in others if is_staging(o)]
        done.update(g.as_pointer() for g in group)
        col = lay.column(align=True)
        col.alert = True
        col.label(text=" and ".join(staging_label(g) for g in group[:3]) + " share one cast", icon='ERROR')
        col.label(text="Linked Copy: make one independent")     # the button's tooltip says the rest
        for g in group:
            col.operator("bbst.make_independent", text=f"Make {staging_label(g)} Independent",
                         icon='UNLINKED').scene_name = g.name


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


def pick_set_object(context, event, accept=None):
    """The object under the mouse in whichever 3D pane it is over — only what that pane
    actually shows (skips things hidden in the pane or cut away above the level). accept (0.19.1): a test
    accept(object, hit location) an object must pass; the click goes on through anything that fails it (the studio
    floor in front of a set chair), and ends on nothing where it answers PICK_STOP (the set's floor)."""
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
        return pick_along_ray(context.scene, context.evaluated_depsgraph_get(), context.view_layer, origin,
                              direction, cut=cut, accept=accept, viewport=sp)
    return None


def pick_along_ray(scene, dg, vl, origin, direction, cut=None, accept=None, viewport=None):
    """The first object along a ray that is shown (in that viewport, under the section cut) and that accept takes;
    through what accept refuses, and None where it answers PICK_STOP. pick_set_object's own loop (tests call it)."""
    for _ in range(64):
        hit, loc, _n, _i, ob, _m = scene.ray_cast(dg, origin, direction)
        if not hit:
            return None
        src = ob.original if getattr(ob, "original", None) else ob
        shown = True
        try:
            shown = src.visible_get(view_layer=vl, viewport=viewport) if viewport is not None else \
                src.visible_get(view_layer=vl)
        except Exception:
            pass
        if shown and (cut is None or loc.z <= cut + 1e-4):
            ok = True if accept is None else accept(src, loc)
            if ok == PICK_STOP:
                return None
            if ok:
                return src
        origin = loc + direction * 0.002
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


# ------------------------------------------------------------------ set edits: Take into Staging (0.19)
#
# Aman, 15 Oct 2026: a staging can change its set without touching the set. "Edit Set" lets the set be clicked;
# "Take into Staging" makes the picked piece this staging's own copy — the same meshes and materials, so fixes
# to the set still flow in — and hides the original IN THIS STAGING ONLY, in the panes and in renders. The copy
# is a normal staging prop: moved, keyed on the beats, carried with the studio. "Reset to set" gives the original
# back. Nothing is ever pushed back into the set.
#
# How the original hides: its objects move into small wrapper collections of their own, linked exactly where
# they were (so the set scene and every other staging still show them), and this staging's view layer excludes
# those wrappers. A piece taken by two stagings shares its wrappers; when no staging uses them any more (the last
# Reset, Delete Staging) they are dissolved and the objects go back exactly where they came from.

SET_ID_KEY = "bb_st_set_id"        # on a set piece taken into a staging: its lasting id
TAKEN_KEY = "bb_st_taken"          # on a staging's copy of a set piece: the id of the original it replaces
PART_KEY = "bb_st_part_of"         # on the copied children of a taken assembly: the id of its root
SETPIECE_KEY = "bb_st_setpiece"    # on every copied set object: real set geometry (meshes + materials shared)
SETEDIT_KEY = "bb_st_setedit"      # on a wrapper collection inside the set: the id of the piece it hides
LOOSE_KEY = "bb_st_setedit_loose"  # that wrapper stands at the set scene's top level (a loose set object)
PARTS_KEY = "bb_st_parts"          # on the Props sub-collection that holds the copied parts
PART_ROLE = "setpart"
COPY_OF_KEY = "bb_st_copy_of"      # on a Shift+D of a taken copy: the id of the set piece it was copied from
ASSEMBLY_MAX_M = 3.5               # a parent spanning more than this is a room group, not one piece of furniture
GEOM_TYPES = {'MESH', 'CURVE', 'SURFACE', 'META', 'FONT', 'CURVES', 'POINTCLOUD', 'VOLUME', 'GREASEPENCIL'}
_SET_GUARD = {"scene": "", "snap": {}, "moved": set(), "pending": False, "msg": "", "names": set(), "strays": set(),
              "left": None, "dup": False}


def set_edit_ids(scene):
    st = getattr(scene, "bb_st", None)
    return {r.set_id for r in st.set_edits if r.set_id} if st is not None else set()


def _is_local(idb):
    return idb is not None and idb.library is None and getattr(idb, "override_library", None) is None


def setedit_wrappers(sid=None):
    """This file's own set-edit wrappers. One that arrives through a linked library belongs to the other file's
    stagings and is never dissolved, healed or relinked here: Blender refuses to change linked data (the Dubey
    exterior links the interior's 'A0 | Class exterior (R02 link)', whose door or blinds an interior staging may
    have taken: review s4 #1)."""
    return [c for c in bpy.data.collections
            if c.get(SETEDIT_KEY) is not None and _is_local(c) and (sid is None or c.get(SETEDIT_KEY) == sid)]


def _local_coll(name):
    """The file's own collection of that name (a linked one may carry the same name)."""
    try:
        return bpy.data.collections.get((name, None))
    except (KeyError, TypeError):
        c = bpy.data.collections.get(name)
        return c if _is_local(c) else None


def _set_ptrs(scene):
    return {o.as_pointer() for c in layer_colls(scene, "SET") for o in coll_objects(c)}


def _in_layer(vl, ob):
    """The object is in this view layer (not in a collection it excludes)."""
    try:
        return vl.objects.get(ob.name) == ob
    except Exception:
        return False


def _span(ob, set_ptrs, dg, vl=None):
    """How far a set object and everything under it reach: the largest side of their world box, in metres.
    Only what this staging shows counts (an object it leaves out is not evaluated here: its matrix can be stale)."""
    lo = hi = None
    for o in [ob] + list(ob.children_recursive):
        if o.as_pointer() not in set_ptrs or o.type not in GEOM_TYPES or (vl is not None and not _in_layer(vl, o)):
            continue
        mw = _evaluated_matrix(o, dg)
        for c in o.bound_box:
            p = mw @ Vector(c)
            lo = p.copy() if lo is None else Vector(map(min, lo, p))
            hi = p.copy() if hi is None else Vector(map(max, hi, p))
    return 0.0 if lo is None else max(hi - lo)


def assembly_root(scene, ob, set_ptrs=None, dg=None):
    """The piece a click on a set object means: the top of its assembly (Isaac's sets build furniture as an
    EMPTY with 'optimized static parts' under it), never a parent that spans a room."""
    set_ptrs = _set_ptrs(scene) if set_ptrs is None else set_ptrs
    vl = scene.view_layers[0]
    root = ob
    while True:
        p = root.parent
        if (p is None or p.as_pointer() not in set_ptrs or p.get(ROLE_KEY) is not None
                or not _in_layer(vl, p) or _span(p, set_ptrs, dg, vl) > ASSEMBLY_MAX_M):
            return root
        root = p


def assembly_objects(scene, root, set_ptrs=None):
    """The root and every set object under it that this staging shows (a tier its view layer leaves out stays out)."""
    set_ptrs = _set_ptrs(scene) if set_ptrs is None else set_ptrs
    vl = scene.view_layers[0]
    return [root] + [o for o in root.children_recursive
                     if o.as_pointer() in set_ptrs and o.get(ROLE_KEY) is None and _in_layer(vl, o)]


def _ensure_set_id(ob):
    """The piece's lasting id (the copies and wrappers point back with it). A set object duplicated after it was
    taken carries the same id: the one inside the id's wrappers keeps it, any other gets a new one."""
    import uuid
    sid = ob.get(SET_ID_KEY)
    if sid:
        mine = any(c.get(SETEDIT_KEY) == sid for c in ob.users_collection)
        if mine or not any(o != ob and o.get(SET_ID_KEY) == sid for o in bpy.data.objects):
            return sid
    sid = uuid.uuid4().hex[:12]
    ob[SET_ID_KEY] = sid
    return sid


def _take_blocker(sid, objs):
    """Why this piece can not be taken (None: it can)."""
    for x in objs:
        if x.library is not None or x.override_library is not None:
            return f"{x.name} comes from a linked file: it can only be changed there"
        for c in x.users_collection:
            tag = c.get(SETEDIT_KEY)
            if tag is not None and tag != sid:
                return f"{x.name} is part of another piece taken elsewhere: reset that one first"
            if c.library is not None:
                return f"{x.name} sits in a linked collection ({c.name}): it can only be changed in its own file"
    return None


def _wrap_pieces(scene, sid, objs, label):
    """Move the piece's objects into wrapper collections where they live in the set: each wrapper is linked
    exactly where the object was, so the set scene and the other stagings see no change. A loose object of the
    set scene gets one wrapper standing at the set scene's top level and at the top of this staging's SET."""
    src = set_scene_of(scene)
    homes = {c.as_pointer() for c in layer_colls(scene, "SET")}
    if src is not None:
        homes |= {src.collection.as_pointer()} | {c.as_pointer() for c in src.collection.children_recursive}
    out = []
    for x in objs:
        for c in list(x.users_collection):
            tag = c.get(SETEDIT_KEY)
            if tag is not None:
                if tag == sid and c not in out:
                    out.append(c)
                continue
            if c.as_pointer() not in homes:
                continue                # another staging's own SET link of a loose object: it keeps showing there
            loose = (src is not None and c == src.collection) or c.get(LAYER_KEY) == "SET"
            w = next((ch for ch in c.children if ch.get(SETEDIT_KEY) == sid), None)
            if w is None and loose:
                w = next((ch for ch in setedit_wrappers(sid) if ch.get(LOOSE_KEY)), None)
            if w is None:
                w = bpy.data.collections.new(f"Set edit · {label}")
                w[SETEDIT_KEY] = sid
                if loose:
                    w[LOOSE_KEY] = True
            if c.children.get(w.name) != w:
                c.children.link(w)
                _note_home(w, c, src)
            if w.objects.get(x.name) != x:
                w.objects.link(x)
            c.objects.unlink(x)
            if w not in out:
                out.append(w)
    return out


def _all_layer_colls(vl):
    out, stack = [], [vl.layer_collection] if vl.layer_collection is not None else []   # a new scene has none yet
    while stack:
        lc = stack.pop()
        out.append(lc)
        stack.extend(lc.children)
    return out


def exclude_set_edits(scene):
    """This staging leaves the originals of its set edits out of its view layers (panes and renders) and shows
    every other wrapped piece. The other stagings and the set scene are never touched."""
    if not is_staging(scene) or not setedit_wrappers():
        return
    ids = set_edit_ids(scene)
    for vl in scene.view_layers:
        for _ in range(256):            # one change at a time: an exclude re-syncs the layer tree
            bad = next((lc for lc in _all_layer_colls(vl) if lc.collection.get(SETEDIT_KEY) is not None
                        and lc.exclude != (lc.collection.get(SETEDIT_KEY) in ids)), None)
            if bad is None:
                break
            bad.exclude = bad.collection.get(SETEDIT_KEY) in ids


HOMES_KEY = "bb_st_setedit_homes"  # on a wrapper: where it was linked ("scene:<name>" = a set scene's top level)


def _note_home(w, c, src):
    tok = f"scene:{src.name}" if (src is not None and c == src.collection) else c.name
    homes = list(w.get(HOMES_KEY, []))
    if tok not in homes:
        w[HOMES_KEY] = homes + [tok]


def _noted_homes(w):
    out = []
    for tok in w.get(HOMES_KEY, []):
        sc = bpy.data.scenes.get(tok[6:]) if tok.startswith("scene:") else None
        c = sc.collection if sc is not None else (None if tok.startswith("scene:") else _local_coll(tok))
        if c is not None and c.get(SETEDIT_KEY) is None and _is_local(sc or c):
            out.append(c)
    return out


def _wrapper_parents(w):
    out = [c for c in bpy.data.collections if _is_local(c) and c.children.get(w.name) == w]
    return out + [s.collection for s in bpy.data.scenes if _is_local(s) and s.collection.children.get(w.name) == w]


def _set_home_ptrs():
    """Every collection a set piece can live in: the set scenes' trees and the stagings' SET roots."""
    out = set()
    for s in set_scenes(offered=False):
        out |= {s.collection.as_pointer()} | {c.as_pointer() for c in s.collection.children_recursive}
    for s in stagings():
        out |= {c.as_pointer() for c in layer_colls(s, "SET")}
    return out


def release_set_wrappers():
    """Wrappers no staging uses any more are dissolved: their objects go back exactly where they were."""
    used = {r.set_id for s in stagings() for r in s.bb_st.set_edits}
    n = 0
    for w in setedit_wrappers():
        if w.get(SETEDIT_KEY) in used:
            continue
        parents = _wrapper_parents(w) or _noted_homes(w)
        if not parents and len(w.objects):
            print("BB Stage: kept", w.name, "— no home found for its pieces")
            continue
        for p in parents:
            for x in list(w.objects):
                if p.objects.get(x.name) != x:
                    p.objects.link(x)
            for ch in list(w.children):
                if p.children.get(ch.name) != ch:
                    p.children.link(ch)
            if p.children.get(w.name) == w:
                p.children.unlink(w)
        bpy.data.collections.remove(w)
        n += 1
    return n


def heal_set_wrappers():
    """The wrappers true to the stagings' set edits again: one no staging uses is dissolved, and a piece a staging
    uses sits in its wrapper only. A repair made between two undo steps (the pane sync dropping a dead copy's
    record) can be undone half-way: Blender keeps the home collection it thinks unchanged, so the original sits
    in its wrapper AND back home (the wrapper itself no longer linked there) — and shows in the staging next to
    its copy."""
    release_set_wrappers()
    homes = None
    for w in setedit_wrappers():
        parents = _wrapper_parents(w)
        if not parents:
            for p in _noted_homes(w):
                p.children.link(w)
                parents.append(p)
        for x in list(w.objects):
            for c in list(x.users_collection):
                if c == w or c.get(SETEDIT_KEY) is not None:
                    continue
                if homes is None:
                    homes = _set_home_ptrs()
                if c.as_pointer() not in homes:
                    continue
                if c not in parents:
                    c.children.link(w)
                    parents.append(c)
                c.objects.unlink(x)


def _parts_coll(scene, create=True):
    """Props › Set parts: the copied children of taken pieces (the Props list shows only the pieces)."""
    props_c = sub_coll(scene, "STAGE", "Props")
    if props_c is None:
        return None
    for c in props_c.children:
        if c.get(PARTS_KEY):
            return c
    if not create:
        return None
    c = bpy.data.collections.new(f"Set parts · {staging_label(scene)}")
    c[PARTS_KEY] = True
    props_c.children.link(c)
    return c


def _clean_copy(ob):
    """A copy starts with the set object's own colour and none of BB Stage's marks."""
    try:
        if TINT_KEY in ob:
            ob.color = ob[TINT_KEY]
        if DT_BACKUP_KEY in ob:
            ob.display_type = ob[DT_BACKUP_KEY]
    except Exception:
        pass
    for k in [k for k in ob.keys() if k.startswith("bb_st")]:
        del ob[k]


def _remap_refs(ob, mapping):
    """Modifiers, constraints and drivers that point inside the piece point at the copies: a copied hinge reads
    the staging's own opening control, never the set's (the workstation lid, the battery cupboard: review s4 #4)."""
    for stack in (ob.modifiers, ob.constraints):
        for m in stack:
            for p in m.bl_rna.properties:
                if p.type != 'POINTER' or p.is_readonly or getattr(p.fixed_type, "identifier", "") != 'Object':
                    continue
                v = getattr(m, p.identifier, None)
                if v is not None and v.as_pointer() in mapping:
                    try:
                        setattr(m, p.identifier, mapping[v.as_pointer()])
                    except Exception:
                        pass
    ad = ob.animation_data
    for fc in (ad.drivers if ad is not None else ()):
        for var in fc.driver.variables:
            for t in var.targets:
                try:
                    if t.id is not None and t.id.as_pointer() in mapping:
                        t.id = mapping[t.id.as_pointer()]
                except Exception:
                    pass


def _copy_pieces(scene, root, objs, dg, root_copy=None):
    """Copies of a piece's objects (meshes and materials shared), parented like the originals. The root's copy
    stands free where the original stands; root_copy: reuse an existing copy of the root (only the parts are made)."""
    sid = root.get(SET_ID_KEY, "")
    mapping = {}
    for x in objs:
        if x == root and root_copy is not None:
            mapping[x.as_pointer()] = root_copy
            continue
        y = x.copy()
        _clean_copy(y)
        mapping[x.as_pointer()] = y
    parts = None
    for x in objs:
        y = mapping[x.as_pointer()]
        if x == root:
            if root_copy is None:
                mw = _evaluated_matrix(x, dg)
                y.parent = None
                if y.rotation_mode != 'XYZ':
                    y.rotation_mode = 'XYZ'         # the beats key rotation_euler
                y.matrix_world = mw
                _remap_refs(y, mapping)
            continue
        anc = x.parent
        while anc is not None and anc.as_pointer() not in mapping:
            anc = anc.parent
        anc = anc if anc is not None else root
        if anc == x.parent:
            inv = x.matrix_parent_inverse.copy()
        else:       # its own parent stays in the set (hidden, a tier left out): ride with the nearest copied one
            try:
                inv = _evaluated_matrix(anc, dg).inverted() @ _evaluated_matrix(x, dg) @ x.matrix_basis.inverted()
            except ValueError:
                inv = Matrix.Identity(4)
        y.parent = mapping[anc.as_pointer()]
        y.matrix_parent_inverse = inv
        _remap_refs(y, mapping)
        ad = y.animation_data
        if ad is not None and ad.action is not None:
            try:        # its own copy of the action: a retime of this staging must never move the set's keys
                slot = ad.last_slot_identifier
                ad.action = ad.action.copy()
                if slot and not ad.action_slot:
                    ad.last_slot_identifier = slot
            except Exception:
                pass
        y[ROLE_KEY] = PART_ROLE
        y[PART_KEY] = sid
        y[SETPIECE_KEY] = True
        parts = parts or _parts_coll(scene)
        parts.objects.link(y)
    return mapping


_TRANSFORM_PATHS = ("location", "rotation_euler", "rotation_quaternion", "rotation_axis_angle", "scale",
                    "delta_location", "delta_rotation_euler", "delta_rotation_quaternion", "delta_scale")
_DEFAULT_NAME = re.compile(r"^(Empty|Cube|Plane|Mesh|Object|Cylinder|Sphere|Circle|Curve|Collection|Null|"
                           r"Instance|Root|Assembly|Group\d*)(\.\d+)?$", re.I)


def _free_root_anim(copy):
    """The root copy moves on the staging's beat keys: no set action, no NLA, no driver on its transform (those
    would hold it in place). Its other drivers stay (already pointing at the copied controls)."""
    ad = copy.animation_data
    if ad is None:
        return
    try:
        ad.action = None
    except Exception:
        pass
    for tr in list(ad.nla_tracks):
        ad.nla_tracks.remove(tr)
    for fc in list(ad.drivers):
        if fc.data_path in _TRANSFORM_PATHS or fc.data_path.startswith(("matrix", "parent")):
            ad.drivers.remove(fc)
    if not len(ad.drivers):
        copy.animation_data_clear()


def _piece_label(root, picked=None):
    """What Aman reads for a taken piece: the root's own name, unless it is a default one (Isaac's anonymous
    'Empty.001' holding the whole workstation: review s4 #9); then the collection the root lives in, else the
    object he clicked."""
    if not _DEFAULT_NAME.match(root.name):
        return root.name
    masters = {s.collection.as_pointer() for s in bpy.data.scenes}
    for c in root.users_collection:
        if (c.get(SETEDIT_KEY) is None and c.get(LAYER_KEY) is None and c.as_pointer() not in masters
                and not _DEFAULT_NAME.match(c.name)):
            return c.name
    if picked is not None and picked != root and not _DEFAULT_NAME.match(picked.name):
        return picked.name
    return root.name


def _take_piece(scene, root, objs, dg, label=None):
    st = scene.bb_st
    label = label or _piece_label(root)
    sid = _ensure_set_id(root)
    mapping = _copy_pieces(scene, root, objs, dg)
    copy = mapping[root.as_pointer()]
    _free_root_anim(copy)
    copy.lock_location = copy.lock_rotation = copy.lock_scale = (False, False, False)
    copy.hide_select = False
    copy[ROLE_KEY] = "prop"
    copy[TAKEN_KEY] = sid
    copy[SETPIECE_KEY] = True
    copy.name = unique_object_name(f"{label} · {staging_label(scene)}")
    sub_coll(scene, "STAGE", "Props").objects.link(copy)
    _wrap_pieces(scene, sid, objs, label)
    r = st.set_edits.add()
    r.set_id, r.original, r.copy = sid, root, copy
    return copy


def take_into_staging(scene, picks):
    """Take the picked set objects, each with its assembly, into this staging. Returns (copies, notes)."""
    st = scene.bb_st
    copies, notes = [], []
    if not layer_colls(scene, "SET") or sub_coll(scene, "STAGE", "Props") is None:
        return copies, ["This staging has no set or no Props collection"]
    set_ptrs = _set_ptrs(scene)
    dg = _scene_depsgraph(scene)
    vl = scene.view_layers[0]
    taken = {o.as_pointer() for r in st.set_edits if r.original is not None
             for o in [r.original] + list(r.original.children_recursive)}
    roots, clicked = [], {}
    for ob in picks:
        if ob is None:
            continue
        if ob.as_pointer() not in set_ptrs or ob.get(ROLE_KEY) is not None:
            notes.append(f"{ob.name} is not part of this staging's set")
            continue
        if ob.as_pointer() in taken:
            notes.append(f"{ob.name} is already this staging's own")
            continue
        if not _in_layer(vl, ob):
            notes.append(f"{ob.name} is not shown in this staging")
            continue
        root = assembly_root(scene, ob, set_ptrs, dg)
        if root.as_pointer() in taken:
            notes.append(f"{root.name} is already this staging's own")
        elif root not in roots:
            roots.append(root)
            clicked[root.as_pointer()] = ob
    for root in roots:
        objs = assembly_objects(scene, root, set_ptrs)
        if any(o.as_pointer() in taken for o in objs):
            notes.append(f"{root.name}: part of it is already this staging's own")
            continue
        sid = _ensure_set_id(root)
        why = _take_blocker(sid, objs)
        if why:
            notes.append(why)
            continue
        copies.append(_take_piece(scene, root, objs, dg, _piece_label(root, clicked.get(root.as_pointer()))))
        taken |= {o.as_pointer() for o in objs}
    if copies:
        for s in stagings():
            if s == scene or len(s.bb_st.set_edits):
                exclude_set_edits(s)
    return copies, notes


def _delete_staged(scene, ob):
    """Remove a staged object the way the list's X does (cameras that travel with it stand free)."""
    try:
        clear_rides_of(scene, ob)
    except Exception:
        pass
    bpy.data.objects.remove(ob)


def _part_top(o):
    """The staged object a copied set part rides with: up its parents while they are parts."""
    r = o
    while r.parent is not None and r.get(ROLE_KEY) == PART_ROLE:
        r = r.parent
    return r


def _part_orphan(scene, o):
    """A copied part whose piece is gone from this staging (a copy deleted by hand)."""
    top = _part_top(o)
    return top == o or top.get(ROLE_KEY) != "prop" or scene.objects.get(top.name) != top


def _piece_parts(ob):
    return [p for p in ob.children_recursive if p.get(ROLE_KEY) == PART_ROLE]


def reset_set_edit(scene, k):
    """Give one set piece back to the set: the staging's copy goes (keys, paths and parts with it) and the
    original shows again in this staging. The wrappers go when no staging uses them any more. A Shift+D of the
    copy stays, with its own parts: it is a prop of its own."""
    st = scene.bb_st
    r = st.set_edits[k]
    sid, copy = r.set_id, r.copy
    st.set_edits.remove(k)
    live = copy is not None and scene.objects.get(copy.name) == copy
    doomed = _piece_parts(copy) if live else []
    staged = [o for c in layer_colls(scene, "STAGE") for o in coll_objects(c)]
    for o in staged:
        if o.get(PART_KEY) == sid and o not in doomed and _part_orphan(scene, o):
            doomed.append(o)
        elif o != copy and o.get(TAKEN_KEY) == sid:
            o[COPY_OF_KEY] = sid
            del o[TAKEN_KEY]            # a Shift+D of the copy stays a prop of its own
    for o in doomed:
        try:
            bpy.data.objects.remove(o)
        except ReferenceError:
            pass
    if live:
        _delete_staged(scene, copy)
    prune_moves(scene)
    refresh_paths(scene)
    refresh_set_edits(scene, purge=True)        # inside an operator (undo step): wrappers no staging uses go


def reset_copy(scene, ob):
    """The X on a taken piece's row is Reset to set: the copy goes and the original comes back."""
    st = getattr(scene, "bb_st", None)
    if st is None or ob is None:
        return False
    for k, r in enumerate(st.set_edits):
        if r.copy == ob:
            reset_set_edit(scene, k)
            return True
    return False


def _find_original(scene, sid):
    return next((o for c in layer_colls(scene, "SET") for o in coll_objects(c) if o.get(SET_ID_KEY) == sid), None)


def _copy_subtree(scene, src_root, dst_root):
    """A Shift+D of a taken piece that came without its parts (only the root was copied): the parts of the piece
    it was copied from, copied under it (meshes and materials shared, parented the same way)."""
    parts = _piece_parts(src_root)
    mapping = {src_root.as_pointer(): dst_root}
    for p in parts:
        mapping[p.as_pointer()] = p.copy()
    coll = _parts_coll(scene)
    for p in parts:
        y = mapping[p.as_pointer()]
        y.parent = mapping.get(p.parent.as_pointer(), dst_root) if p.parent is not None else dst_root
        y.matrix_parent_inverse = p.matrix_parent_inverse.copy()
        _remap_refs(y, mapping)
        ad = y.animation_data
        if ad is not None and ad.action is not None:
            try:
                slot = ad.last_slot_identifier
                ad.action = ad.action.copy()
                if slot and not ad.action_slot:
                    ad.last_slot_identifier = slot
            except Exception:
                pass
        for c in list(y.users_collection):
            c.objects.unlink(y)
        coll.objects.link(y)
    return len(parts)


def _shown_originals(scene, rec, set_ptrs, vl):
    """The set objects of a live set edit that this staging shows although it took them."""
    orig = rec.original
    if orig is None or not rec.set_id or not _is_local(orig):
        return []
    return [o for o in [orig] + list(orig.children_recursive)
            if o.as_pointer() in set_ptrs and o.get(ROLE_KEY) is None and _is_local(o) and _in_layer(vl, o)]


def set_edits_need_repair(scene):
    """A taken original shows in this staging next to its copy: the set was edited behind its back (a taken
    object moved to another collection with M, its 'Set edit' collection deleted in the set's Outliner)."""
    if not is_staging(scene) or not len(scene.bb_st.set_edits):
        return False
    set_ptrs, vl = _set_ptrs(scene), scene.view_layers[0]
    return any(r.copy is not None and _shown_originals(scene, r, set_ptrs, vl) for r in scene.bb_st.set_edits)


def _rewrap_shown(scene):
    """Structural: every live set edit whose original shows again is wrapped again where it now lives
    (review s4 #7). Returns how many were repaired."""
    st = scene.bb_st
    if not len(st.set_edits):
        return 0
    set_ptrs, vl = _set_ptrs(scene), scene.view_layers[0]
    n = 0
    for r in st.set_edits:
        objs = _shown_originals(scene, r, set_ptrs, vl)
        if not objs or _take_blocker(r.set_id, objs):
            continue
        _wrap_pieces(scene, r.set_id, objs, _piece_label(r.original))
        n += 1
    return n


def refresh_set_edits(scene, adopt=True, structural=True, purge=False):
    """Keep this staging's set edits true to the file. Always (flags only): a copy deleted by hand gives its
    original back (its record goes, the wrapper is shown again here), a Shift+D of the copy loses its claim, the
    parts of a deleted copy are hidden, the originals stay out of this staging's view layers.
    structural (only inside an operator that pushes an undo step, or right after a file load): wrappers no staging
    uses are dissolved and half-undone ones healed, an original the set shows again is wrapped again, and with
    adopt a taken copy that arrived without its record (a staging copy, Split Beats) gets one, its parts and its
    wrappers, and a Shift+D that came without its parts gets them; purge also deletes the hidden parts.
    Never structural from a timer, a handler or Go to: Blender's undo keeps the data it thinks unchanged since the
    last undo step, so a collection relinked between two steps came back half-undone (a piece in two places) or
    pointing at freed data — a crash in the random walk (s4_setedit_fuzz, seed 117)."""
    if not is_staging(scene):
        return
    st = scene.bb_st
    for k in reversed(range(len(st.set_edits))):
        r = st.set_edits[k]
        live = r.copy is not None and scene.objects.get(r.copy.name) == r.copy
        if not live or not r.set_id:
            st.set_edits.remove(k)
    # set id -> the copy. Never keep a record (an item of st.set_edits) across set_edits.add(): the add can move
    # the collection in memory and an older item then reads freed memory (a crash, s4_setedit_fuzz seed 76)
    have = {r.set_id: r.copy for r in st.set_edits}
    staged = [o for c in layer_colls(scene, "STAGE") for o in coll_objects(c)]
    dg = None
    for ob in staged:
        sid = ob.get(TAKEN_KEY)
        if not sid:
            continue
        rc = have.get(sid)
        if rc is not None:
            if rc != ob:
                ob[COPY_OF_KEY] = sid
                del ob[TAKEN_KEY]       # a Shift+D of the copy: a prop of its own, never a second claim
            continue
        if not (adopt and structural) or ob.get(ROLE_KEY) != "prop" or ob.parent is not None:
            continue
        orig = _find_original(scene, sid)
        objs = assembly_objects(scene, orig) if (orig is not None and _in_layer(scene.view_layers[0], orig)) else None
        if objs is None or _take_blocker(sid, objs):
            ob[COPY_OF_KEY] = sid
            del ob[TAKEN_KEY]           # its original is not in this set (or is taken in parts elsewhere): a prop of its own
            continue
        if ob.data is not None and orig.data is not None and ob.type == orig.type and ob.data != orig.data:
            old, ob.data = ob.data, orig.data       # a staging copy that copied the mesh: shared again with the set
            if old.users == 0:
                try:
                    getattr(bpy.data, {"MESH": "meshes", "CURVE": "curves", "LIGHT": "lights",
                                       "CAMERA": "cameras"}.get(orig.type, "meshes")).remove(old)
                except Exception:
                    pass
        _wrap_pieces(scene, sid, objs, _piece_label(orig))
        r = st.set_edits.add()
        r.set_id, r.original, r.copy = sid, orig, ob
        have[sid] = ob
        if len(objs) > 1 and not _piece_parts(ob):
            dg = dg or _scene_depsgraph(scene)
            _copy_pieces(scene, orig, objs, dg, root_copy=ob)
    if adopt and structural:            # a Shift+D (or a Python duplicate) of a taken piece that left its parts behind
        for ob in staged:
            sid = ob.get(COPY_OF_KEY)
            if not sid or ob.get(ROLE_KEY) != "prop" or ob.get(TAKEN_KEY) or ob.parent is not None or ob.children:
                continue
            rc = have.get(sid)
            if rc is not None and _piece_parts(rc):
                _copy_subtree(scene, rc, ob)
                continue
            orig = _find_original(scene, sid)
            if orig is not None and _in_layer(scene.view_layers[0], orig):
                objs = assembly_objects(scene, orig)
                if len(objs) > 1:
                    dg = dg or _scene_depsgraph(scene)
                    _copy_pieces(scene, orig, objs, dg, root_copy=ob)
        staged = [o for c in layer_colls(scene, "STAGE") for o in coll_objects(c)]
    # parts left behind by a copy deleted in the Outliner: hidden at once, deleted by the next Take / Reset
    for o in staged:
        try:
            if o.get(ROLE_KEY) != PART_ROLE or not o.get(PART_KEY) or not _part_orphan(scene, o):
                continue
        except ReferenceError:
            continue                    # removed just before (listed twice)
        if purge:
            bpy.data.objects.remove(o)
        elif not (o.hide_viewport and o.hide_render):
            o.hide_viewport = o.hide_render = True
    if structural:
        if setedit_wrappers():
            heal_set_wrappers()
        if _rewrap_shown(scene):
            for s in stagings():
                if s != scene and len(s.bb_st.set_edits):
                    exclude_set_edits(s)
    exclude_set_edits(scene)


def _migrate_v11_s4_setedit(scene):
    """0.19 set edits, on every load / Enter / Go to: records true to the file, the originals kept out of this
    staging, and Edit Set off (a short mode: it never outlives leaving the staging). Flags only: the structural
    repairs run after a file load (_bbst_after_load) and inside the set-edit operators."""
    st = scene.bb_st
    if st.edit_set:
        st.edit_set = False
    refresh_set_edits(scene, adopt=False, structural=False)


def _set_tree_ptrs(scene):
    """Every collection of this staging's set (the SET root and all under it)."""
    out = set()
    for r in layer_colls(scene, "SET"):
        out.add(r.as_pointer())
        out |= {c.as_pointer() for c in r.children_recursive}
    src = set_scene_of(scene)
    if src is not None:
        out.add(src.collection.as_pointer())
    return out


def _edit_set_update(self, context):
    """Edit Set on: the set can be clicked in this staging (Take into Staging acts on what is picked).
    Off: the set is unselectable again and nothing of it stays selected."""
    scene = self.id_data
    if not (isinstance(scene, bpy.types.Scene) and is_staging(scene)):
        return
    on = bool(self.edit_set)
    roots = layer_colls(scene, "SET")
    for c in roots:
        if c.hide_select == on:
            c.hide_select = not on
        if not on and c.get(CAMLOCK_KEY):
            del c[CAMLOCK_KEY]      # Camera mode's lock on it is now the set's own: leaving Camera keeps it locked
    g = _SET_GUARD
    g["moved"].clear()
    g["msg"] = ""
    if on:
        g["scene"] = scene.name
        obs = [o for c in roots for o in coll_objects(c)]
        g["names"] = {o.name for o in obs}
        g["strays"] = set()
        g["snap"] = {o.name: o.matrix_basis.copy() for o in obs
                     if o.get(ROLE_KEY) is None
                     and not (o.animation_data and (o.animation_data.action or len(o.animation_data.drivers)))}
        return
    if g.get("strays") and g["scene"] == scene.name:
        g["left"] = (scene.name, set(g["strays"]))     # copies made inside the set: the Edit Set button (or Take) moves them out
    g["scene"], g["snap"], g["names"], g["strays"] = "", {}, set(), set()
    for vl in scene.view_layers:
        for c in roots:
            for o in coll_objects(c):
                try:
                    if o.select_get(view_layer=vl):
                        o.select_set(False, view_layer=vl)
                except RuntimeError:
                    pass
    request_sync(0.0)


def _guard_set_moves(scene, depsgraph):
    """Edit Set: a set piece dragged by mistake goes back once the drag ends — the set is never edited from a
    staging (Aman, 15 Oct 2026: no push-back to the set). Take it into the staging to move it. An object that
    turns up in the set while Edit Set is on (a copy made with a Python call: Shift+D is stopped by bbst.duplicate)
    is noted and moved out into the staging by the next Take or the Edit Set button."""
    g = _SET_GUARD
    if not g["snap"] or scene is None or g["scene"] != scene.name:
        return
    if not getattr(getattr(scene, "bb_st", None), "edit_set", False):
        g["scene"], g["snap"] = "", {}          # an undo switched Edit Set off behind our back
        return
    tree = None
    for u in depsgraph.updates:
        if not isinstance(u.id, bpy.types.Object):
            continue
        n = u.id.name
        if n in g["snap"]:
            if u.is_updated_transform:
                g["moved"].add(n)
        elif n not in g["names"] and n not in g["strays"] and u.id.get(ROLE_KEY) is None:
            ob = bpy.data.objects.get(n)
            if ob is None or not _is_local(ob):
                continue
            tree = tree if tree is not None else _set_tree_ptrs(scene)
            if any(c.as_pointer() in tree for c in ob.users_collection):
                g["strays"].add(n)
            else:
                g["names"].add(n)       # a role-less object of the staging itself: looked at once
    if g["moved"] and not g["pending"]:
        g["pending"] = True
        try:
            bpy.app.timers.register(_set_guard_timer, first_interval=0.05)
        except Exception:
            g["pending"] = False


def _set_guard_timer():
    g = _SET_GUARD
    try:
        wm = bpy.context.window_manager
        if wm is not None and _transform_running(wm):
            return 0.1                  # put it back when the drag is over
        back = []
        for n in sorted(g["moved"]):
            ob, m = bpy.data.objects.get(n), g["snap"].get(n)
            if ob is None or m is None:
                continue
            if any(abs(a - b) > 1e-5 for ra, rb in zip(ob.matrix_basis, m) for a, b in zip(ra, rb)):
                ob.matrix_basis = m
                back.append(n)
        g["moved"].clear()
        if back:
            g["msg"] = (f"{back[0]}{' and others' if len(back) > 1 else ''} went back: "
                        "the set is not moved from a staging — Take into Staging first")
            print("BB Stage:", g["msg"])
            request_sync(0.0)
    except Exception as e:
        print("BB Stage set guard:", e)
    g["pending"] = False
    return None


def strays_to_staging(scene):
    """Structural (inside an undo-pushing operator): objects that turned up inside the set while Edit Set was on
    in this staging leave the set and become this staging's props, where they stand (review s4 #2: the set is
    never changed from a staging)."""
    g = _SET_GUARD
    names = set(g.get("strays", ())) if g.get("scene") == scene.name else set()
    left = g.get("left")
    if left and left[0] == scene.name:
        names |= left[1]
    g["strays"], g["left"] = set(), None
    props_c = sub_coll(scene, "STAGE", "Props")
    if not names or props_c is None:
        return []
    tree = _set_tree_ptrs(scene)
    out = []
    for n in sorted(names):
        ob = bpy.data.objects.get(n)
        if ob is None or not _is_local(ob) or ob.get(ROLE_KEY) is not None:
            continue
        homes = [c for c in ob.users_collection if c.as_pointer() in tree and _is_local(c)]
        if not homes:
            continue
        mw = ob.matrix_world.copy()
        if ob.parent is not None:
            ob.parent = None
            ob.matrix_world = mw
        for c in homes:
            c.objects.unlink(ob)
        if props_c.objects.get(ob.name) != ob:
            props_c.objects.link(ob)
        _clean_copy(ob)
        ob[ROLE_KEY] = "prop"
        ob[SETPIECE_KEY] = True
        ob.hide_select = False
        out.append(ob)
    if out:
        print("BB Stage: moved out of the set into the staging:", [o.name for o in out])
    return out


def part_selects_piece(scene, view_layer):
    """Clicking a part of a taken piece selects the piece itself: its root carries the keys."""
    if view_layer is None or _SET_GUARD.get("dup"):
        return                          # bbst.duplicate picked the parts on purpose (bpy.ops updates the layer first)
    parts = [o for o in view_layer.objects.selected if o.get(ROLE_KEY) == PART_ROLE]
    if not parts:
        return
    was_active = view_layer.objects.active in parts
    roots = []
    for p in parts:
        r = p
        while r.parent is not None and r.get(ROLE_KEY) == PART_ROLE:
            r = r.parent
        p.select_set(False, view_layer=view_layer)
        if r.get(ROLE_KEY) == "prop" and r not in roots:
            roots.append(r)
    for r in roots:
        try:
            if not r.hide_select and r.visible_get(view_layer=view_layer):
                r.select_set(True, view_layer=view_layer)
        except RuntimeError:
            pass
    if was_active and roots:
        view_layer.objects.active = roots[0]


def _picked_set_pieces(context):
    return [o for o in getattr(context, "selected_objects", None) or [] if o.get(ROLE_KEY) is None]


class BBST_OT_set_take(bpy.types.Operator):
    """Make the picked set pieces this staging's own (Edit Set on, click them first). Each comes with the
assembly it belongs to; the copy shares the set's meshes and materials and moves and keys like a prop.
The original is hidden in this staging only: the set scene and the other stagings keep it"""
    bl_idname = "bbst.set_take"
    bl_label = "Take into Staging"
    bl_options = {'REGISTER', 'UNDO'}

    obj_name: bpy.props.StringProperty(name="Set object", default="",
                                       description="The set object to take (empty: the selected ones)")

    def execute(self, context):
        scene = context.scene
        if not is_staging(scene):
            self.report({'ERROR'}, "Open a staging first")
            return {'CANCELLED'}
        strays = strays_to_staging(scene)
        if self.obj_name:
            ob = bpy.data.objects.get(self.obj_name)
            if ob is None:
                self.report({'ERROR'}, f"No object called '{self.obj_name}'")
                return {'CANCELLED'}
            picks = [ob]
        else:
            picks = [o for o in _picked_set_pieces(context) if o not in strays]
        if not picks:
            if strays:      # changed the file: FINISHED, so the change gets its undo step
                self.report({'WARNING'}, f"{len(strays)} object(s) made inside the set moved into this staging's props")
                return {'FINISHED'}
            self.report({'ERROR'}, "Turn on Edit Set and click a set piece first")
            return {'CANCELLED'}
        try:
            refresh_set_edits(scene, purge=True)    # structural repairs belong in an undo step: this one
        except Exception as e:
            print("BB Stage set edits before Take:", e)
        copies, notes = take_into_staging(scene, picks)
        if not copies:      # still FINISHED: the repairs above changed the file and need this undo step
            self.report({'ERROR'}, notes[0] if notes else "Nothing to take")
            return {'FINISHED'}
        st = scene.bb_st
        if st.edit_set:
            st.edit_set = False         # back to staging: the set is unclickable again, the copy is picked
        vl = scene.view_layers[0] if context.view_layer is None else context.view_layer
        for o in list(vl.objects.selected):
            o.select_set(False, view_layer=vl)
        for c in copies:
            try:
                c.select_set(True, view_layer=vl)
            except RuntimeError:
                pass
        vl.objects.active = copies[-1]
        request_sync(0.0)
        text = "Took " + ", ".join(c.name for c in copies) + " into the staging (hidden in the set here only)"
        self.report({'WARNING'} if notes else {'INFO'}, text + ("; " + "; ".join(notes) if notes else ""))
        return {'FINISHED'}


def _has_keys(ob):
    ad = getattr(ob, "animation_data", None)
    act = ad.action if ad is not None else None
    return act is not None and any(len(fc.keyframe_points) for fc in id_fcurves(ob))


class BBST_OT_set_reset(bpy.types.Operator):
    """Give this piece back to the set: the staging's copy is deleted (with its beat keys and parts) and the
set's own piece shows again in this staging"""
    bl_idname = "bbst.set_reset"
    bl_label = "Give Back to the Set"
    bl_options = {'REGISTER', 'UNDO'}

    obj_name: bpy.props.StringProperty(name="Piece", default="",
                                       description="The staging's copy or the set piece it replaces (empty: the selected copies)")

    def _targets(self, context):
        st = context.scene.bb_st
        if self.obj_name:
            ob = bpy.data.objects.get(self.obj_name)
            return [r.copy for r in st.set_edits if ob is not None and ob in (r.copy, r.original) and r.copy is not None]
        sel = {o.as_pointer() for o in getattr(context, "selected_objects", None) or []}
        return [r.copy for r in st.set_edits if r.copy is not None and r.copy.as_pointer() in sel]

    def invoke(self, context, event):
        if not is_staging(context.scene):
            return self.execute(context)
        keyed = [c.name for c in self._targets(context) if _has_keys(c)]
        if not keyed:
            return self.execute(context)
        msg = f"{keyed[0]}{' and others' if len(keyed) > 1 else ''}: the staging's copy and its beat keys are deleted"
        try:
            return context.window_manager.invoke_confirm(self, event, title="Give back to the set?", message=msg,
                                                         confirm_text="Give Back", icon='WARNING')
        except TypeError:
            return context.window_manager.invoke_confirm(self, event)

    def execute(self, context):
        scene = context.scene
        if not is_staging(scene):
            self.report({'ERROR'}, "Open a staging first")
            return {'CANCELLED'}
        st = scene.bb_st
        copies = self._targets(context)     # the copies themselves, not list positions: a reset drops dead records
        if not copies:                      # and shifts the rest (review s4 #10)
            self.report({'ERROR'}, "Pick a piece taken from the set (Characters & Props › Set edits)")
            return {'CANCELLED'}
        names = []
        for c in copies:
            k = next((i for i, r in enumerate(st.set_edits) if r.copy is not None and r.copy == c), None)
            if k is None:
                continue
            r = st.set_edits[k]
            names.append(r.original.name if r.original is not None else r.set_id)
            reset_set_edit(scene, k)
        request_sync(0.0)
        self.report({'INFO'}, "Back to the set: " + ", ".join(names))
        return {'FINISHED'}


class BBST_OT_edit_set(bpy.types.Operator):
    """Edit Set: let the set be clicked in this staging, to take pieces of it into the staging. The set itself
is never changed from here"""
    bl_idname = "bbst.edit_set"
    bl_label = "Edit Set"
    bl_options = {'REGISTER', 'UNDO'}

    on: bpy.props.BoolProperty(name="On", default=True)

    def execute(self, context):
        scene = context.scene
        if not is_staging(scene):
            return {'CANCELLED'}
        st = scene.bb_st
        if st.edit_set != self.on:
            st.edit_set = self.on
        if not self.on:
            moved = strays_to_staging(scene)
            if moved:
                self.report({'WARNING'}, f"{len(moved)} object(s) made inside the set moved into this staging's "
                                         "props: the set is not changed from a staging")
        return {'FINISHED'}


class BBST_OT_set_repair(bpy.types.Operator):
    """Hide the set pieces this staging took again, where the set now keeps them (the set was edited since)"""
    bl_idname = "bbst.set_repair"
    bl_label = "Repair Set Edits"
    bl_options = {'REGISTER', 'UNDO', 'INTERNAL'}

    scene_name: bpy.props.StringProperty()

    def execute(self, context):
        scene = bpy.data.scenes.get(self.scene_name) if self.scene_name else context.scene
        if scene is None or not is_staging(scene):
            return {'CANCELLED'}
        refresh_set_edits(scene)
        return {'FINISHED'}


class BBST_OT_duplicate(bpy.types.Operator):
    """Shift+D in a staging. A piece taken from the set is copied whole, its parts with it (sharing the set's
meshes and materials); the set's own pieces are not copied from a staging (Take into Staging first)"""
    bl_idname = "bbst.duplicate"
    bl_label = "Duplicate"
    bl_options = {'INTERNAL'}

    @classmethod
    def poll(cls, context):
        if not _in_stage(context):
            return False
        sel = getattr(context, "selected_objects", None) or []
        return any(o.get(ROLE_KEY) is None or o.get(SETPIECE_KEY) for o in sel)

    def _run(self, context, interactive):
        scene = context.scene
        sel = list(context.selected_objects)
        tree = _set_ptrs(scene)
        own = [o for o in sel if o.get(ROLE_KEY) is None and o.as_pointer() in tree]
        if own:
            self.report({'WARNING'}, f"{own[0].name} belongs to the set: it is not copied from a staging. "
                                     "Take into Staging, then Shift+D the copy")
            return {'CANCELLED'} if not interactive else {'FINISHED'}
        pieces = [o for o in sel if o.get(SETPIECE_KEY) and o.get(ROLE_KEY) == "prop"]
        if not pieces:
            if interactive:
                return {'PASS_THROUGH'}         # Blender's own Shift+D
            return bpy.ops.object.duplicate()
        parts = [p for o in pieces for p in _piece_parts(o)]
        vl = context.view_layer
        for p in parts:
            try:
                p.select_set(True, view_layer=vl)
            except RuntimeError:
                pass
        linked = all(o.get(SETPIECE_KEY) for o in sel)  # set geometry stays shared with the set
        _SET_GUARD["dup"] = True
        try:
            if interactive:     # the copy is made at once; the move that follows selects the root only again
                (bpy.ops.object.duplicate_move_linked if linked else bpy.ops.object.duplicate_move)('INVOKE_DEFAULT')
                return {'FINISHED'}
            return bpy.ops.object.duplicate(linked=linked)
        finally:
            _SET_GUARD["dup"] = False
            if not interactive:
                part_selects_piece(scene, context.view_layer)   # the copies' roots stay picked, not their parts

    def invoke(self, context, event):
        return self._run(context, True)

    def execute(self, context):
        return self._run(context, False)


def _piece_controls(copy):
    """The custom properties of a taken piece that drive its own moving parts (Isaac's 'Opening angle' on the
    workstation lid's control): a staging opens its lid or cupboard on its own (review s4 #4)."""
    inside = {o.as_pointer(): o for o in [copy] + list(copy.children_recursive)}
    out, seen = [], set()
    for o in inside.values():
        ad = o.animation_data
        for fc in (ad.drivers if ad is not None else ()):
            for var in fc.driver.variables:
                if var.type != 'SINGLE_PROP':
                    continue
                for t in var.targets:
                    tid = t.id
                    path = t.data_path or ""
                    if (tid is None or tid.as_pointer() not in inside or not path.startswith('["')
                            or not path.endswith('"]')):
                        continue
                    key = (tid.as_pointer(), path)
                    if key in seen or path[2:-2] not in tid.keys():
                        continue
                    seen.add(key)
                    out.append((tid, path, path[2:-2]))
    return out


def draw_set_edits(lay, context):
    """Characters & Props › Set edits: Edit Set, Take into Staging, and the set pieces this staging made its own."""
    scene = context.scene
    if not is_staging(scene):
        return
    st = scene.bb_st
    box = lay.box()
    col = box.column(align=True)
    col.operator("bbst.edit_set", text="Edit Set", depress=st.edit_set,
                 icon='RESTRICT_SELECT_OFF' if st.edit_set else 'RESTRICT_SELECT_ON').on = not st.edit_set
    if st.edit_set:
        sub = col.row(align=True)
        sub.scale_y = 1.2
        sub.enabled = bool(_picked_set_pieces(context))
        sub.operator("bbst.set_take", text="Take into Staging", icon='IMPORT')
        col.label(text="Plan shows the studio: switch it to Set" if st.work_world == 'STUDIO'
                  else "Click set pieces, then Take", icon='INFO')
    if _SET_GUARD["msg"] and _SET_GUARD["scene"] in ("", scene.name):
        r = col.row()
        r.alert = True
        r.label(text="Moved back: Take set pieces first", icon='ERROR')
    col.separator()
    draw_contact_button(col, context)       # 0.19.1: a set chair or table becomes a real studio prop
    if _mode() != 'ARTIST':
        # Easy Mode has no Studio tab, so its walls are here too (review of s8-studio #21)
        col.separator()
        r = col.row(align=True)
        r.operator("bbst.add_wall", text="Add Wall", icon='MOD_SOLIDIFY').kind = 'WALL'
        r.operator("bbst.add_wall", text="Add Door Flat", icon='MOD_BOOLEAN').kind = 'DOOR'
        n = len(studio_walls(scene))
        _dim(col, (f"Walls: {n} · " if n else "") + "G moves, R turns")
    if len(st.set_edits):
        col.separator()
        col.label(text="Taken from the set (hidden here):")
        for rec in st.set_edits:
            if rec.copy is None:
                continue
            row = col.split(factor=0.7, align=True)
            op = row.operator("bbst.obj_action", text=rec.copy.name,
                              icon='FAKE_USER_ON' if is_contact(rec.copy) else 'OBJECT_DATAMODE')
            op.obj_name, op.action = rec.copy.name, 'SELECT'
            row.operator("bbst.set_reset", text="Give back").obj_name = rec.copy.name     # not the ↺ of the Props
            # list (back to the saved keys): this deletes the copy and its keys (review s4 #8)
            for tid, path, label in _piece_controls(rec.copy):
                sub = col.row(align=True)
                sub.separator(factor=2.0)
                sub.prop(tid, path, text=label)


# ------------------------------------------------------------------ studio contact props (0.19.1)
#
# Aman, 15 Oct 2026: "In the studio we will be using some props for real. like you did with the chair. so i need the
# ability to select a prop like a chair or a table from the set and convert it to a studio contact prop." A studio
# contact prop is a real prop that stands in the studio on the shoot day. Made from a set piece, it is Take into
# Staging (the staging's own copy with the set's meshes and materials, the original hidden in this staging only)
# plus the flag; a staging prop, or a piece taken before, is flagged as it is. It is a staging prop, so every world
# and every pane shows it: in magenta (the studio colour code's contact props, Aman, 5 Oct 2026) in the Studio and
# Ghost worlds, and with its own materials in the Set world. The Studio tab lists it with its size and a note; the
# staging pack and the top map carry it. Back to Set gives a taken piece back; Not a Studio Prop drops the flag.

CONTACT_KEY = "bb_st_contact"          # on a staging prop: a real prop that stands in the studio on the shoot day
CONTACT_C0 = "bb_st_contact_c0"        # its own colour (and its parts'), given back when it stops being one
NOTE_KEY = "bb_st_contact_note"        # what the crew should know about it ("the blue plastic chair from Dubey's")
LABEL_KEY = "bb_st_contact_label"      # the name the crew reads (typed in the list; empty: made from the object's)
CONTACT_MAX_M = 6.0                    # bigger than this across is a room, a floor or a wall: not a prop
FURNITURE_ASK_M = 2.5                  # longer or deeper than this: asked first (Isaac's merged chunks, review #11)


def is_contact(ob):
    try:
        return bool(ob is not None and ob.get(CONTACT_KEY) and ob.get(ROLE_KEY) == "prop")
    except ReferenceError:
        return False


def contact_props(scene):
    """This staging's studio contact props."""
    return [o for o in stage_objects(scene, roles=("prop",)) if is_contact(o)] if is_staging(scene) else []


def _paint_contact(ob, on):
    """The prop and its copied set parts in the contact props' magenta (their own colour kept), or back."""
    for o in [ob] + _piece_parts(ob):
        try:
            if on:
                if CONTACT_C0 not in o:
                    o[CONTACT_C0] = list(o.color)
                if _rgba_differs(o.color, PROP_MAGENTA):
                    o.color = PROP_MAGENTA
            elif CONTACT_C0 in o:
                if not _rgba_differs(o.color, PROP_MAGENTA):
                    o.color = o[CONTACT_C0]     # a colour picked by hand meanwhile stays (review of s8-studio #7)
                del o[CONTACT_C0]
        except Exception:
            pass


def sync_contact_colors(scene):
    """Parts copied after the prop was made one (a staging copy, a Shift+D that came without its parts) are painted
    too. The prop's own colour is left as it is: a colour picked by hand in the Props list stays."""
    for ob in contact_props(scene):
        for o in _piece_parts(ob):
            if CONTACT_C0 not in o:
                try:
                    o[CONTACT_C0] = list(o.color)
                    o.color = PROP_MAGENTA
                except Exception:
                    pass


def piece_size(ob):
    """(W, D, H) in metres of a staging prop with its copied set parts, along its own axes."""
    loc, rot, _s = ob.matrix_world.decompose()
    inv = Matrix.LocRotScale(loc, rot, None).inverted_safe()
    lo = hi = None
    for o in [ob] + _piece_parts(ob):
        if o.type not in GEOM_TYPES:
            continue
        mw = inv @ o.matrix_world
        for c in o.bound_box:
            p = mw @ Vector(c)
            lo = p.copy() if lo is None else Vector(map(min, lo, p))
            hi = p.copy() if hi is None else Vector(map(max, hi, p))
    return (0.0, 0.0, 0.0) if lo is None else tuple(round(v, 3) for v in (hi - lo))


def size_text(ob):
    w, d, h = piece_size(ob)
    return f"{w:.2f} × {d:.2f} × {h:.2f} m"


_CHUNK_NAME = re.compile(r"(?i)^optimi[sz]ed static parts\s*(\d*)$")


def derived_prop_label(name, scene=None):
    """A short name the crew can read, made from an object's name (review of s8-studio #13): the staging suffix a
    taken copy carries goes, Blender's .001 goes, the first meaningful part of Isaac's 'A | B' names stays,
    underscores become spaces. 'game_chair1.002 · Sc 233-236' → 'Game chair 1', 'Replacement stool 04 | seat ...'
    → 'Replacement stool 04', 'Empty | optimized static parts 0063' → 'Set piece 0063'."""
    s = name or ""
    for lab in ([staging_label(scene)] if is_staging(scene) else [staging_label(x) for x in stagings()]):
        suffix = f" · {lab}"
        k = s.rfind(suffix)
        if k > 0 and re.fullmatch(r"(\.\d+)?", s[k + len(suffix):]):
            s = s[:k]
            break
    s = re.sub(r"\.\d{3,}$", "", s.strip())
    parts = [re.sub(r"\.\d{3,}$", "", p.strip()) for p in s.split("|") if p.strip()]
    # the first part that says something: not 'Empty', not a bare number ('02 | Shops and entrance'), not a chunk
    s = next((p for p in parts if not _DEFAULT_NAME.match(p) and re.search(r"[A-Za-z]", p)
              and not _CHUNK_NAME.match(p)),
             next((p for p in parts if _CHUNK_NAME.match(p)), parts[0] if parts else s))
    m = _CHUNK_NAME.match(s)
    if m:
        s = ("Set piece " + m.group(1)).strip()
    s = re.sub(r"[_]+", " ", s)
    s = re.sub(r"(?<=[A-Za-z])(\d+)$", r" \1", s)
    s = " ".join(s.split())
    return (s[:1].upper() + s[1:]) if s else (name or "")


def contact_label(ob, scene=None):
    """What a studio prop is called in the list, the Studio Props sheet and the top map: the name typed for it,
    else one made from its object name."""
    try:
        typed = str(ob.get(LABEL_KEY, "")).strip()
    except ReferenceError:
        return ""
    return typed or derived_prop_label(ob.name, scene)


def _contact_oversize(scene, picks):
    """[(label, (W, D, H))] of the set pieces picked that are longer or deeper than furniture (but not refused as a
    room; a tall shelf or a pillar is not asked about), measured with the assembly a take would copy. Asked before taking: one click on a desk in Isaac's set took
    a 5.19 m merged chunk of unrelated pieces (review of s8-studio #11). Staging props are his own: never asked."""
    out = []
    tree = None
    dg = None
    vl = scene.view_layers[0]
    for ob in picks:
        if ob is None or ob.get(ROLE_KEY) is not None:
            continue
        tree = _set_ptrs(scene) if tree is None else tree
        if ob.as_pointer() not in tree or _taken_copy_of(scene, ob) is not None:
            continue
        dg = dg or _scene_depsgraph(scene)
        root = assembly_root(scene, ob, tree, dg)
        lo = hi = None
        for o in [root] + list(root.children_recursive):
            if o.as_pointer() not in tree or o.type not in GEOM_TYPES or not _in_layer(vl, o):
                continue
            mw = _evaluated_matrix(o, dg)
            for c in o.bound_box:
                p = mw @ Vector(c)
                lo = p.copy() if lo is None else Vector(map(min, lo, p))
                hi = p.copy() if hi is None else Vector(map(max, hi, p))
        if lo is None:
            continue
        size = tuple(round(v, 2) for v in (hi - lo))
        if max(size[0], size[1]) > FURNITURE_ASK_M and max(size) <= CONTACT_MAX_M:
            out.append((derived_prop_label(_piece_label(root, ob)), size))
    return out


def _taken_copy_of(scene, ob):
    """The staging's copy of the taken set piece this set object belongs to (None: not taken here)."""
    for r in scene.bb_st.set_edits:
        o = r.original
        if o is not None and r.copy is not None and (o == ob or ob in o.children_recursive):
            return r.copy
    return None


def make_contact(scene, picks):
    """Make the picked things studio contact props: a set piece is taken into the staging first (with its assembly,
    as Take into Staging does), a staging prop or a taken piece is flagged as it is. Returns (props, notes)."""
    st = scene.bb_st
    tree = _set_ptrs(scene)
    flag, take, notes = [], [], []
    dg = None
    for ob in picks:
        if ob is None:
            continue
        role = ob.get(ROLE_KEY)
        if role == PART_ROLE:
            ob, role = _part_top(ob), _part_top(ob).get(ROLE_KEY)
        if role == "prop":
            if ob.get(STANDIN_KEY):
                notes.append(f"{ob.name} is a placeholder stand-in (banned from every output), not a real prop")
            elif ob not in flag:
                flag.append(ob)
        elif role is None and ob.as_pointer() in tree:
            copy = _taken_copy_of(scene, ob)
            if copy is not None:
                if copy not in flag:
                    flag.append(copy)
                continue
            dg = dg or _scene_depsgraph(scene)
            root = assembly_root(scene, ob, tree, dg)
            span = _span(root, tree, dg, scene.view_layers[0])
            if span > CONTACT_MAX_M:
                notes.append(f"{_piece_label(root, ob)} is {span:.1f} m across: a room, a floor or a wall, not a prop")
            elif ob not in take:
                take.append(ob)
        else:
            notes.append(f"{who_label(ob, scene) or ob.name} is not a prop or a set piece")
    if take:
        try:
            refresh_set_edits(scene, purge=True)    # structural repairs belong in an undo step: this one
        except Exception as e:
            print("BB Stage set edits before a studio prop:", e)
        copies, more = take_into_staging(scene, take)
        notes += more
        flag += [c for c in copies if c not in flag]
    for ob in flag:
        ob[CONTACT_KEY] = True
        _paint_contact(ob, True)
    if flag and st.edit_set:
        st.edit_set = False         # back to staging: the set is unclickable again, the new prop is picked
    return flag, notes


def drop_contact(ob):
    """Not a studio prop any more: the flag and the magenta go, the prop stays in the staging."""
    if CONTACT_KEY in ob:
        del ob[CONTACT_KEY]
    _paint_contact(ob, False)


def _contact_candidates(context):
    """What Make Studio Contact Prop would take from the selection (cheap: draw code calls it): set pieces (only
    clickable with Edit Set on), parts of taken pieces, and staging props that are not studio props yet. An object
    with no role that is not in this staging's set (a Kimodo body, a light) is none of these (review of s8-studio
    #5: a selected body took over the button)."""
    out = []
    set_ptrs = None
    scene = getattr(context, "scene", None)
    for o in getattr(context, "selected_objects", None) or []:
        role = o.get(ROLE_KEY)
        if role == PART_ROLE:
            o, role = _part_top(o), _part_top(o).get(ROLE_KEY)
        if role is None:
            if scene is None:
                continue
            set_ptrs = _set_ptrs(scene) if set_ptrs is None else set_ptrs
            if o.as_pointer() not in set_ptrs:
                continue
        elif not (role == "prop" and not o.get(STANDIN_KEY) and not is_contact(o)):
            continue
        if o not in out:
            out.append(o)
    return out


PICK_STOP = "STOP"      # an accept test's answer: the click ends here, on nothing


def _contact_pickable(scene):
    """What a click of the eyedropper may land on: a set piece of this staging or a staging prop. Only the studio's
    own pieces, pegs, cameras and bodies let the click through to what lies behind them. A set surface refused for
    its size (a floor, a building slab, a wall) or anything below this staging's floor stops it: on an upper floor
    a click on bare floor went through the slab and took a piece of the ground floor (review of s8-studio #3)."""
    tree = []
    floor = scene.bb_st.floor_z - 0.05

    def ok(o, loc=None):
        if loc is not None and loc.z < floor:
            return PICK_STOP
        role = o.get(ROLE_KEY)
        if role in ("prop", PART_ROLE):
            return not o.get(STANDIN_KEY)
        if role is not None:
            return False
        if not tree:
            tree.extend((_set_ptrs(scene), _scene_depsgraph(scene)))
        if o.as_pointer() not in tree[0]:
            return False                # not the set (a Kimodo body): through it
        root = assembly_root(scene, o, tree[0], tree[1])
        if _span(root, tree[0], tree[1], scene.view_layers[0]) > CONTACT_MAX_M:
            return PICK_STOP            # the floor or a wall: nothing to make a prop of here
        return True
    return ok


def _select_objects(context, obs):
    vl = context.view_layer
    try:
        for o in list(vl.objects.selected):
            o.select_set(False, view_layer=vl)
        for o in obs:
            o.select_set(True, view_layer=vl)
        if obs:
            vl.objects.active = obs[-1]
    except Exception:
        pass


class BBST_OT_contact_prop(bpy.types.Operator):
    """Make Studio Contact Prop: a real prop that stands in the studio on the shoot day (a chair, a table).
A set piece becomes this staging's own copy (as Take into Staging does, the set itself is not changed); a staging
prop is marked as it is. It shows in magenta in the Studio and Ghost worlds and as itself in the Set world, and the
Studio tab lists its size. Nothing picked: click one in a pane"""
    bl_idname = "bbst.contact_prop"
    bl_label = "Make Studio Contact Prop"
    bl_options = {'REGISTER', 'UNDO'}

    obj_name: bpy.props.StringProperty(name="Object", default="", options={'SKIP_SAVE'},
                                       description="The set piece or prop (empty: the selected ones, or click one)")
    on: bpy.props.BoolProperty(name="Studio prop", default=True, options={'SKIP_SAVE'},
                               description="Off: it is not a studio prop any more (it stays in the staging)")

    _world0 = None          # the plan's world before the eyedropper switched it (given back after the pick or Esc)
    _pending = None         # the object clicked, taken on the next timer tick (so the status line shows first)
    _timer = None

    @classmethod
    def description(cls, context, properties):
        if not properties.on:
            ob = bpy.data.objects.get(properties.obj_name)
            who = ob.name if ob is not None else "it"
            return f"Not a Studio Prop: {who} stays in the staging as a plain prop, and leaves the studio props list"
        return cls.__doc__

    def _finish_pick(self, context):
        """Status line, cursor and timer back; the plan back in the world he had chosen (review of s8-studio #6, #14)."""
        try:
            context.workspace.status_text_set(None)
        except Exception:
            pass
        try:
            context.window.cursor_modal_restore()
        except Exception:
            pass
        if self._timer is not None:
            try:
                context.window_manager.event_timer_remove(self._timer)
            except Exception:
                pass
            self._timer = None
        w0, self._world0 = self._world0, None
        scene = context.scene
        if w0 is not None and is_staging(scene) and scene.bb_st.work_world != w0:
            scene.bb_st.work_world = w0
            request_sync(0.0)

    def _ask(self, context, event, big):
        """A piece far bigger than furniture: its size, and a question, before it is taken (review of s8-studio #11)."""
        label, (w, d, h) = big[0]
        more = f" (and {len(big) - 1} more)" if len(big) > 1 else ""
        return context.window_manager.invoke_confirm(
            self, event, title=f"{label}{more} is {w:.2f} × {d:.2f} × {h:.2f} m",
            message="Bigger than a chair or a table. The set merges pieces from across the room into one mesh: all of "
                    "it would become one studio prop. Esc, then click a smaller piece, or take it anyway",
            confirm_text="Take It Anyway", icon='WARNING')

    def invoke(self, context, event):
        scene = context.scene
        if not self.on or not is_staging(scene):
            return self.execute(context)
        if self.obj_name:
            ob = bpy.data.objects.get(self.obj_name)
            picks = [ob] if ob is not None else []
            if not picks:
                return self.execute(context)        # it reports the missing name
        else:
            picks = _contact_candidates(context)
        if picks:
            big = _contact_oversize(scene, picks)
            return self._ask(context, event, big) if big else self.execute(context)
        if context.window is None or not stage_panes(context.window):
            return self.execute(context)
        st = scene.bb_st
        self._world0 = st.work_world
        if st.work_world == 'STUDIO':
            st.work_world = 'GHOST'     # the studio view hides the set: the set's chairs could not be seen to click
            request_sync(0.0)
        context.workspace.status_text_set("Click a chair, a table or a prop in a pane to make it a studio contact "
                                          "prop · right-click or Esc to stop")
        context.window.cursor_modal_set('EYEDROPPER')
        context.window_manager.modal_handler_add(self)
        return {'RUNNING_MODAL'}

    def modal(self, context, event):
        if self._pending is not None:
            if event.type == 'TIMER':
                name, self._pending = self._pending, None
                self._finish_pick(context)
                ob = bpy.data.objects.get(name)
                if ob is None:
                    return {'CANCELLED'}
                return self._run(context, [ob])
            return {'RUNNING_MODAL'}            # one more tick: a second click must not take a second piece
        if event.type == 'LEFTMOUSE' and event.value == 'PRESS':
            scene = context.scene
            ob = pick_set_object(context, event, accept=_contact_pickable(scene))
            if ob is None:
                context.workspace.status_text_set("Nothing to make a prop of there: click a chair or a table "
                                                  "(the set shows in the Set and Ghost views) · Esc stops")
                return {'RUNNING_MODAL'}
            if _contact_oversize(scene, [ob]):
                name = ob.name
                self._finish_pick(context)
                try:            # asked in a dialog of its own: this eyedropper ends here, nothing taken yet
                    bpy.ops.bbst.contact_prop('INVOKE_DEFAULT', obj_name=name)
                except Exception as e:
                    print("BB Stage contact prop ask:", e)
                return {'CANCELLED'}
            # the first take on a big file can take seconds: say so before the work starts (review of s8-studio #19)
            context.workspace.status_text_set(f"Taking {derived_prop_label(ob.name, scene)} into the staging…")
            context.window.cursor_modal_set('WAIT')
            self._pending = ob.name
            self._timer = context.window_manager.event_timer_add(0.02, window=context.window)
            return {'RUNNING_MODAL'}
        if event.type in ('RIGHTMOUSE', 'ESC'):
            self._finish_pick(context)
            return {'CANCELLED'}
        return {'PASS_THROUGH'}

    def execute(self, context):
        scene = context.scene
        if not is_staging(scene):
            self.report({'ERROR'}, "Open a staging first")
            return {'CANCELLED'}
        if self.obj_name:
            ob = bpy.data.objects.get(self.obj_name)
            if ob is None:
                self.report({'ERROR'}, f"No object called '{self.obj_name}'")
                return {'CANCELLED'}
            picks = [ob]
        else:
            picks = _contact_candidates(context) if self.on else [
                o for o in getattr(context, "selected_objects", None) or [] if is_contact(o)]
        if not self.on:
            return _drop_contacts(self, picks)
        if not picks:
            self.report({'ERROR'}, "Pick a set piece (Edit Set) or a prop first, or press the button and click one")
            return {'CANCELLED'}
        return self._run(context, picks)

    def _run(self, context, picks):
        scene = context.scene
        win = getattr(context, "window", None)
        try:
            if win is not None:
                win.cursor_set('WAIT')
            made, notes = make_contact(scene, picks)
        finally:
            if win is not None:
                win.cursor_set('DEFAULT')
        if not made:
            self.report({'ERROR'}, notes[0] if notes else "Nothing to make a studio prop of")
            return {'FINISHED'}         # still FINISHED: a set repair made on the way needs its undo step
        _select_objects(context, made)
        request_sync(0.0)
        text = "Studio contact prop: " + ", ".join(f"{contact_label(o, scene)} ({size_text(o)})" for o in made)
        self.report({'WARNING'} if notes else {'INFO'}, text + ("; " + "; ".join(notes) if notes else ""))
        return {'FINISHED'}


def _drop_contacts(op, picks):
    done = [o for o in picks if is_contact(o)]
    for o in done:
        drop_contact(o)
    if not done:
        op.report({'WARNING'}, "That is not a studio prop")
        return {'CANCELLED'}
    request_sync(0.0)
    op.report({'INFO'}, "Not studio props any more (still in the staging): " + ", ".join(o.name for o in done))
    return {'FINISHED'}


class BBST_OT_contact_drop(bpy.types.Operator):
    """It stays in this staging as a plain prop, where it stands, and leaves the studio props list (Back to Set,
below it, gives a piece taken from the set back to the set instead)"""
    bl_idname = "bbst.contact_drop"
    bl_label = "Not a Studio Prop"
    bl_options = {'REGISTER', 'UNDO'}

    obj_name: bpy.props.StringProperty(name="Object", default="", options={'SKIP_SAVE'},
                                       description="The studio prop (empty: the selected ones)")

    def execute(self, context):
        if not is_staging(context.scene):
            self.report({'ERROR'}, "Open a staging first")
            return {'CANCELLED'}
        if self.obj_name:
            ob = bpy.data.objects.get(self.obj_name)
            picks = [ob] if ob is not None else []
        else:
            picks = list(getattr(context, "selected_objects", None) or [])
        return _drop_contacts(self, picks)


def draw_contact_button(lay, context):
    """The one button, named for what it will do: the picked piece, or a click to come."""
    scene = context.scene
    cands = _contact_candidates(context)
    row = lay.row(align=True)
    row.scale_y = 1.3
    if len(cands) == 1:
        row.operator("bbst.contact_prop", text=f"Make {derived_prop_label(cands[0].name, scene)} a Studio Prop",
                     icon='FAKE_USER_ON')
    elif cands:
        row.operator("bbst.contact_prop", text=f"Make the {len(cands)} Picked Studio Props", icon='FAKE_USER_ON')
    else:
        row.operator("bbst.contact_prop", text="Make Studio Contact Prop", icon='EYEDROPPER')
        _dim(lay, "Then click a chair or a table in a pane")


def _mirrored(ob):
    try:
        return any(o.matrix_world.determinant() < 0 for o in [ob] + _piece_parts(ob) if o.type in GEOM_TYPES)
    except Exception:
        return False


def draw_studio_props(lay, context):
    """Studio › Studio props: the real props in the studio on the shoot day, with their names, sizes and notes."""
    scene = context.scene
    if not is_staging(scene):
        return
    draw_contact_button(lay, context)
    props = contact_props(scene)
    if not props:
        _dim(lay, "None yet. They show in magenta in every world", 'INFO')
        return
    taken = {r.copy.as_pointer() for r in scene.bb_st.set_edits if r.copy is not None}
    lay.label(text=f"In the studio ({len(props)}):")
    for ob in props:
        box = lay.box()
        col = box.column(align=True)
        r = col.row(align=True)
        op = r.operator("bbst.obj_action", text="", icon='RESTRICT_SELECT_OFF')
        op.obj_name, op.action = ob.name, 'SELECT'
        r.prop(ob, "bbst_contact_label", text="")         # the name the crew reads (type to change it)
        r.operator("bbst.contact_drop", text="", icon='X').obj_name = ob.name
        r = col.row()
        r.enabled = False
        r.label(text=f"W × D × H  {size_text(ob)}")
        col.prop(ob, "bbst_contact_note", text="", icon='TEXT', placeholder="note for the crew")
        if _mirrored(ob):
            _dim(col, "Mirrored in the set: Blender's 'negative scale' note is fine", 'INFO')
        if ob.as_pointer() in taken:
            col.operator("bbst.set_reset", text="Back to Set", icon='LOOP_BACK').obj_name = ob.name


# ------------------------------------------------------------------ studio walls (0.19.1)
#
# Aman, 15 Oct 2026: "I also couldnt find the functionality to add walls in the studio." In 0.19.0 a wall was the Kit's
# "Wall flat" button, and the Kit & stand-ins panel is off in the Switchboard by default (the Studio tab itself is
# Artist Mode's); the Studio space panel's "Studio walls" only counts the run along the back. Walls now have their
# own panel near the top of the Studio tab, always shown: Add Wall and Add Door Flat with a length and a height, put
# on the studio floor in the middle of what can be seen of the plan. Each is moved (G) and turned (R) like anything
# else, keeps a Length and a Height you can type, and is listed with its size. They are the Kit's dark grey (the 5 Oct
# colour code's pieces built on the studio, as the Kit's own wall flats): in the studio's light white they vanished
# into the white floor of the plan once deselected (review of s8-studio #9).

WALL_KEY = "bb_st_wall"        # on a wall added with Add Wall / Add Door Flat: 'WALL' or 'DOOR'
WALL_LEN = "bb_st_wall_len"
WALL_HGT = "bb_st_wall_h"
WALL_T = 0.10                  # thickness (m), as the back walls
DOOR_OPENING = (0.90, 2.10)    # a door flat's doorway (m)
LINTEL_T = 0.03                # a door flat's lintel is thinner than the wall: from above the doorway reads as a gap


def wall_bmesh(kind, length, height):
    """A wall of this length (along X) and height, standing on its origin; a door flat has a doorway in the middle,
    under a thin lintel so the plan shows where the door is (review of s8-studio #18)."""
    bm = bmesh.new()
    t = WALL_T
    if kind == 'DOOR':
        length = max(0.5, length)
        ow = min(DOOR_OPENING[0], max(0.3, length - 0.2))
        oh = min(DOOR_OPENING[1], max(0.5, height - 0.15))
        side = (length - ow) / 2.0
        _box_bmesh(bm, (side, t, height), (-(ow + side) / 2.0, 0.0, height / 2.0))
        _box_bmesh(bm, (side, t, height), ((ow + side) / 2.0, 0.0, height / 2.0))
        _box_bmesh(bm, (ow, LINTEL_T, height - oh), (0.0, 0.0, oh + (height - oh) / 2.0))
    else:
        _box_bmesh(bm, (length, t, height), (0.0, 0.0, height / 2.0))
    return bm


def write_wall_mesh(ob):
    kind = ob.get(WALL_KEY, 'WALL')
    bm = wall_bmesh(kind, float(ob.get(WALL_LEN, 2.4)), float(ob.get(WALL_HGT, 3.0)))
    bm.to_mesh(ob.data)
    bm.free()
    ob.data.update()


def studio_walls(scene):
    """The walls added by hand (Add Wall, Add Door Flat, the Kit's wall and door flats), not the back walls."""
    out = []
    for c in layer_colls(scene, "STUDIO"):
        for o in coll_objects(c):
            if not o.get(SHELL_KEY) and (o.get(WALL_KEY) or o.get("bb_st_kind") in ("Wall flat", "Door flat")):
                out.append(o)
    return sorted(out, key=lambda o: o.name)


def wall_spot(scene, at=None, length=0.0):
    """Where a new wall stands: the point given (the middle of the plan view), inside the studio with all its length
    and on its floor, a step towards the front from any wall already standing there."""
    st = scene.bb_st
    c = studio_center(scene)
    b = boundary_of(scene)
    yaw = b.rotation_euler.z if b is not None else 0.0
    rot = Matrix.Rotation(yaw, 3, 'Z')
    p = Vector(at) if at is not None else c.copy()
    local = rot.inverted() @ (Vector((p.x, p.y, 0.0)) - Vector((c.x, c.y, 0.0)))
    hx = max(0.0, st.studio_w / 2 - max(0.2, length / 2 + 0.05))
    hy = max(0.0, st.studio_d / 2 - 0.2)
    local.x, local.y, local.z = max(-hx, min(hx, local.x)), max(-hy, min(hy, local.y)), 0.0
    taken = [o.location.copy() for o in studio_walls(scene)]
    for _ in range(24):
        q = Vector((c.x, c.y, 0.0)) + rot @ local
        if not any((Vector((t.x, t.y, 0.0)) - q).length < 0.3 for t in taken):
            break
        local.y = local.y - 0.5 if local.y - 0.5 >= -hy else hy      # one step towards the front, then round again
    q = Vector((c.x, c.y, 0.0)) + rot @ local
    return Vector((q.x, q.y, st.floor_z)), yaw


def add_wall(scene, kind='WALL', length=2.4, height=3.0, at=None):
    studio = layer_colls(scene, "STUDIO")
    if not studio:
        return None
    label = "Door flat" if kind == 'DOOR' else "Wall"
    n = sum(1 for o in coll_objects(studio[0]) if o.get(WALL_KEY) == kind) + 1
    name = unique_object_name(f"Studio {label} {n:02d}")
    me = bpy.data.meshes.new(name)
    ob = bpy.data.objects.new(name, me)
    ob[ROLE_KEY] = "studio"
    ob["bb_st_kind"] = label
    ob[WALL_KEY] = kind
    ob[WALL_LEN] = float(max(0.5 if kind == 'DOOR' else 0.1, length))
    ob[WALL_HGT] = float(max(0.3, height))
    write_wall_mesh(ob)
    me.materials.append(ensure_grey_material())
    ob.color = KIT_GREY             # dark on the white studio floor: it reads in the plan when not selected
    loc, yaw = wall_spot(scene, at, ob[WALL_LEN])
    ob.location = loc
    ob.rotation_euler = (0.0, 0.0, yaw)
    studio[0].objects.link(ob)
    return ob


def visible_window_box(area):
    """(region, x0, x1) of a 3D pane: its drawing region and the span of it, in region pixels, that no sidebar or
    toolbar drawn over it covers. With Region Overlap (Blender's default) the Artist sidebar covers most of the plan,
    and the middle of the view sits behind it (review of s8-studio #10)."""
    win = next((r for r in area.regions if r.type == 'WINDOW'), None) if area is not None else None
    if win is None or win.width < 2:
        return win, 0, (win.width if win is not None else 0)
    x0, x1 = win.x, win.x + win.width
    for r in area.regions:
        if r.type not in ('UI', 'TOOLS') or r.width < 12 or r.height < win.height * 0.5:
            continue
        if r.x >= x1 or r.x + r.width <= x0:
            continue                    # beside the drawing region, not over it (Region Overlap off)
        if r.x + r.width / 2 > win.x + win.width / 2:
            x1 = min(x1, r.x)           # a sidebar on the right
        else:
            x0 = max(x0, r.x + r.width)
    if x1 - x0 < min(120, win.width * 0.25):
        return win, 0, win.width        # nearly all covered: the whole view
    return win, x0 - win.x, x1 - win.x


def visible_view_point(area, r3d=None):
    """The point in the scene under the middle of what can be seen of a 3D pane (at the depth of its view centre).
    None: no such pane."""
    try:
        from bpy_extras import view3d_utils
        r3d = r3d if r3d is not None else area.spaces.active.region_3d
        win, a, b = visible_window_box(area)
        if win is None or r3d is None:
            return None
        co = ((a + b) / 2.0, win.height / 2.0)
        p = view3d_utils.region_2d_to_location_3d(win, r3d, co, r3d.view_location)
        return Vector(p) if p is not None else None
    except Exception:
        return None


def _plan_view_centre(context):
    """Where a new wall goes: the middle of what can be seen of the plan (not behind the sidebar)."""
    area = stage_panes(getattr(context, "window", None)).get("WORK") if getattr(context, "window", None) else None
    if area is None:
        return None
    p = visible_view_point(area)
    if p is not None:
        return p
    try:
        return area.spaces.active.region_3d.view_location.copy()
    except Exception:
        return None


class BBST_OT_add_wall(bpy.types.Operator):
    """Add a studio wall on the studio floor in the middle of the plan view (Door Flat: a wall with a doorway in
the middle). Move it with G and turn it with R like anything else; type its Length and Height in Studio › Walls"""
    bl_idname = "bbst.add_wall"
    bl_label = "Add Wall"
    bl_options = {'REGISTER', 'UNDO'}

    kind: bpy.props.EnumProperty(name="Kind", items=[('WALL', "Wall", "A plain studio wall"),
                                                     ('DOOR', "Door flat", "A wall with a doorway in the middle")])
    length: bpy.props.FloatProperty(name="Length (m)", default=0.0, min=0.0, max=30.0, options={'SKIP_SAVE'},
                                    description="0: the Length set in the panel")
    height: bpy.props.FloatProperty(name="Height (m)", default=0.0, min=0.0, max=12.0, options={'SKIP_SAVE'},
                                    description="0: the Height set in the panel")

    def execute(self, context):
        scene = context.scene
        if not (is_staging(scene) and layer_colls(scene, "STUDIO")):
            self.report({'ERROR'}, "Open a staging first")
            return {'CANCELLED'}
        st = scene.bb_st
        ob = add_wall(scene, self.kind, self.length or st.wall_new_len, self.height or st.wall_new_h,
                      _plan_view_centre(context))
        if ob is None:
            return {'CANCELLED'}
        _select_only(context, ob)
        request_sync(0.0)
        self.report({'INFO'}, f"{ob.name}: {ob[WALL_LEN]:.2f} m long, {ob[WALL_HGT]:.2f} m high. G moves it, R turns it")
        return {'FINISHED'}


def _wall_get(key, axis):
    def get(ob):
        try:
            return float(ob.get(key, ob.dimensions[axis]))
        except Exception:
            return 0.0
    return get


def _wall_set(key):
    def set_(ob, v):
        if not ob.get(WALL_KEY):
            return                      # the Kit's flats and the back walls keep their own size
        if key == WALL_LEN and ob.get(WALL_KEY) == 'DOOR':
            v = max(0.5, v)             # a doorway needs its two sides
        ob[key] = float(v)
        write_wall_mesh(ob)
    return set_


def _note_get(ob):
    return str(ob.get(NOTE_KEY, ""))


def _note_set(ob, v):
    ob[NOTE_KEY] = str(v)


def _label_get(ob):
    return contact_label(ob)


def _label_set(ob, v):
    v = " ".join(str(v).split())
    if not v or v == derived_prop_label(ob.name):
        if LABEL_KEY in ob:
            del ob[LABEL_KEY]           # empty or the made-up one: it follows the object's name again
    else:
        ob[LABEL_KEY] = v


def _OBJECT_PROPS_0191():
    """(attribute, bpy.props kind, keywords): a studio prop's name and note and a wall's size, over the object's own
    custom properties (so a copy of the file, a Shift+D or a staging copy carries them)."""
    return (
        ("bbst_contact_note", "StringProperty", dict(
            name="Note", get=_note_get, set=_note_set, options=set(),
            description="What the crew should know about this studio prop (which one, where it comes from)")),
        ("bbst_contact_label", "StringProperty", dict(
            name="Name", get=_label_get, set=_label_set, options=set(),
            description="What the crew calls this studio prop, in this list, Studio Props.md and the top map. "
                        "Made from the set's name until you type one (clear it to go back)")),
        ("bbst_wall_length", "FloatProperty", dict(
            name="Length (m)", subtype='DISTANCE', min=0.1, max=30.0, step=10, precision=2, options=set(),
            get=_wall_get(WALL_LEN, 0), set=_wall_set(WALL_LEN), description="How long this wall is")),
        ("bbst_wall_height", "FloatProperty", dict(
            name="Height (m)", subtype='DISTANCE', min=0.3, max=12.0, step=10, precision=2, options=set(),
            get=_wall_get(WALL_HGT, 2), set=_wall_set(WALL_HGT), description="How high this wall is")),
    )


def draw_walls(lay, context):
    """Studio › Walls & doors: Add Wall, Add Door Flat, and the walls standing in the studio with their sizes."""
    scene = context.scene
    if not is_staging(scene):
        return
    st = scene.bb_st
    col = lay.column(align=True)
    r = col.row(align=True)
    r.prop(st, "wall_new_len", text="Length")
    r.prop(st, "wall_new_h", text="Height")
    r = col.row(align=True)
    r.scale_y = 1.3
    r.operator("bbst.add_wall", text="Add Wall", icon='MOD_SOLIDIFY').kind = 'WALL'
    r.operator("bbst.add_wall", text="Add Door Flat", icon='MOD_BOOLEAN').kind = 'DOOR'
    walls = studio_walls(scene)
    if walls:
        col = lay.column(align=True)
        col.label(text=f"Walls ({len(walls)}): length × height (m)")
        for ob in walls[:16]:
            r = col.split(factor=0.42, align=True)
            op = r.operator("bbst.obj_action", text=ob.name.replace("Studio ", ""),
                            icon='MOD_BOOLEAN' if ob.get(WALL_KEY) == 'DOOR' else 'MOD_SOLIDIFY')
            op.obj_name, op.action = ob.name, 'SELECT'
            rr = r.row(align=True)
            if ob.get(WALL_KEY):
                rr.prop(ob, "bbst_wall_length", text="")
                rr.prop(ob, "bbst_wall_height", text="")
            else:
                rr.label(text=f"{ob.dimensions.x:.2f} × {ob.dimensions.z:.2f}")
            op = rr.operator("bbst.obj_action", text="", icon='X')
            op.obj_name, op.action = ob.name, 'DELETE'
        if len(walls) > 16:
            _dim(lay, f"and {len(walls) - 16} more (Outliner › STUDIO)")
        _dim(lay, "Pick one, then G moves it and R turns it")
    shell = [o for c in layer_colls(scene, "STUDIO") for o in coll_objects(c)
             if o.get(SHELL_KEY) and o.get("bb_st_kind") == "Studio wall"]
    if shell:
        _dim(lay, f"Back walls: {len(shell)} × {shell[0].dimensions.x + 0.02:.2f} m (Studio space)")
    if not feature_on(scene, "kit") and not module_in_use(scene, MODULE_BY_ID["kit"]):
        op = lay.operator("bbst.feature_set", text="Show Kit Pieces (tables, boxes, stand-ins)", icon='HIDE_OFF')
        op.module, op.on = "kit", True      # the Kit panel is off and hidden: its pieces are one click away


# ------------------------------------------------------------------ characters & props

class BBST_OT_add_char(bpy.types.Operator):
    """Add a character in the middle of the studio, standing on its floor. A name from the cast library brings
    that character's colour, height and width; a new name makes a new character"""
    bl_idname = "bbst.add_char"
    bl_label = "Add Character"
    bl_options = {'REGISTER', 'UNDO'}

    height: bpy.props.FloatProperty(name="Height", default=1.75, min=0.5, max=2.6,
                                    description="A new character's height (a cast character brings its own)")
    width: bpy.props.FloatProperty(name="Width", default=0.0, min=0.0, max=0.9,
                                   description="Side to side at the widest (the whole peg gets wider or narrower). "
                                               "0: the cast character's, or the standard peg's for the height")

    def execute(self, context):
        scene = context.scene
        chars = sub_coll(scene, "STAGE", "Characters") if is_staging(scene) else None
        if chars is None:
            self.report({'ERROR'}, "Open a staging first")
            return {'CANCELLED'}
        st = scene.bb_st
        typed = " ".join(st.new_char_name.split())
        entry = None
        if typed and fstate() is not None:
            entry, le = cast_by_name(typed)
            if entry is None and le is not None:
                entry = ensure_file_cast(le)            # a library character: its colour, height and width
            elif entry is None:
                entry = new_file_cast(typed, _next_free_color(scene), self.height, self.width)
                self.report({'INFO'}, f"{typed} is new: Save to Library (under the cast list) keeps "
                                      f"{typed} for every file")
            elif self.properties.is_property_set("height") or self.properties.is_property_set("width"):
                if fully_locked(entry):
                    self.report({'WARNING'}, f"{entry.name} is locked in the cast library: "
                                             f"{entry.height:.2f} m kept")
                else:                                   # typed by hand for this file's character
                    if self.properties.is_property_set("height"):
                        entry.height = self.height
                    if self.width > 0.0:
                        entry.width = self.width
        if entry is not None:
            twice = any(o.get(CAST_KEY) == entry.cid for o in chars.objects)
            # the cast name with Blender's own suffix when another staging has it already (Jai.001): the panels
            # show the cast name, the link lives in the bb_st_cast property
            ob = build_peg_object(entry.name, entry.height, tuple(entry.color), width=entry.width)
            ob[CAST_KEY] = entry.cid
            apply_cast_to(ob, entry)
            if twice:       # UX review of s5: a second Riya came without a word, and two rows read just "Riya"
                self.report({'WARNING'}, f"{entry.name} was already in this staging: this is a second {entry.name} "
                                         f"({ob.name}). Undo if that was a slip")
        else:
            k = len(chars.objects) + 1
            while bpy.data.objects.get(f"Character {k}") is not None:
                k += 1          # 'Character 3', never 'Character 2 2'
            ob = build_peg_object(f"Character {k}", self.height, _next_free_color(scene),
                                  width=self.width or None)
            ob[CAST_KEY] = ""       # nobody from the cast: a rename later never links it behind Aman's back
        ob.location = spawn_point(scene, len(chars.objects))
        chars.objects.link(ob)
        st.new_char_name = ""
        _select_only(context, ob)
        request_sync(0.0)
        return {'FINISHED'}


# ------------------------------------------------------------------ characters: pose, configure, cast (0.19)

def _char_target(context, obj_name=""):
    ob = bpy.data.objects.get(obj_name) if obj_name else getattr(context, "active_object", None)
    return ob if (ob is not None and ob.get(ROLE_KEY) == "char") else None


class BBST_OT_pose(bpy.types.Operator):
    """Stand, sit or lie on this beat: the hip and knee bend and the body settles at the height given.
    Like a move, it is kept by Save Beat"""
    bl_idname = "bbst.pose"
    bl_label = "Pose"
    bl_options = {'REGISTER', 'UNDO'}

    kind: bpy.props.EnumProperty(name="Pose", items=[
        ('STAND', "Stand", "On their feet"),
        ('SIT', "Sit", "Hips and knees bent, resting on a seat at the height given"),
        ('LIE', "Lie", "On their back, on the floor or a bed at the height given")], default='STAND')
    at: bpy.props.FloatProperty(name="At (m)", default=-1.0, min=-1.0, max=5.0, step=1, precision=2,
                                description="Seat or bed height. -1: the character's own (Configure Character)")
    obj_name: bpy.props.StringProperty(options={'SKIP_SAVE'},
                                       description="The character; empty: every selected character")

    def execute(self, context):
        scene = context.scene
        if self.obj_name:
            obs = [_char_target(context, self.obj_name)]
        else:
            obs = [o for o in getattr(context, "selected_objects", []) if o.get(ROLE_KEY) == "char"]
            if not obs and _char_target(context) is not None:
                obs = [_char_target(context)]
        obs = [o for o in obs if is_peg(o)]
        if not obs:
            self.report({'WARNING'}, "Select a character (a peg) first")
            return {'CANCELLED'}
        for ob in obs:
            at = self.at
            if at < 0.0:
                at = float(ob.get("bbst_lie_at" if self.kind == 'LIE' else "bbst_sit_at",
                                  LIE_AT if self.kind == 'LIE' else SIT_AT))
            set_pose(scene, ob, pose_values(self.kind, at, ob))
        _caption_redraw(self, context)      # the panel's Stand / Sit / Lie shows the new pose at once
        return {'FINISHED'}


def _pose_get(prop):
    return lambda ob: float(ob.get(prop, POSE_NEUTRAL[prop]))


def _pose_setter(prop):
    def _set(ob, v):
        if is_peg(ob):
            vals = {prop: v}
            if prop == "bbst_seat" and pose_kind(ob) == 'SIT':      # a sitter on a new seat: his feet stay down
                vals = pose_values('SIT', v, ob)
            set_pose(bpy.context.scene, ob, vals)
    return _set


def _dim_get(which):
    return lambda ob: peg_height_of(ob) if which == "height" else peg_width_of(ob)


def _dim_setter(which):
    def _set(ob, v):
        """A cast character changes its cast entry (every staging follows; refused when locked); any other
        character changes on its own."""
        if ob.get(ROLE_KEY) != "char":
            return
        e = cast_of(ob)
        if e is not None:
            if which not in locked_fields(e):
                setattr(e, which, v)
            return
        if which == "height":
            set_char_size(ob, float(v))         # the whole model: the build stays
        else:
            set_char_size(ob, peg_height_of(ob), float(v))
    return _set


def _OBJECT_PROPS_019():
    """The character controls the panels draw (Object properties over the peg's own custom properties)."""
    return (
        ("bbst_pose_hip", dict(name="Hip", subtype='ANGLE', min=-math.pi, max=math.pi, soft_min=-math.radians(30),
                               soft_max=math.radians(150), get=_pose_get("bbst_hip"), set=_pose_setter("bbst_hip"),
                               description="The thigh forward from standing (90° sits). Save Beat keeps it")),
        ("bbst_pose_knee", dict(name="Knee", subtype='ANGLE', min=-math.pi, max=math.pi, soft_min=0.0,
                                soft_max=math.radians(160), get=_pose_get("bbst_knee"), set=_pose_setter("bbst_knee"),
                                description="The shin folded back (90° sits). Save Beat keeps it")),
        ("bbst_pose_tilt", dict(name="Lie back", subtype='ANGLE', min=-math.pi, max=math.pi,
                                soft_min=-math.radians(10), soft_max=math.radians(100), get=_pose_get("bbst_tilt"),
                                set=_pose_setter("bbst_tilt"),
                                description="The whole body tipped back about the hips (90° lies on the back)")),
        ("bbst_pose_at", dict(name="Seat / bed (m)", subtype='DISTANCE', min=0.0, max=5.0, step=1, precision=2,
                              get=_pose_get("bbst_seat"), set=_pose_setter("bbst_seat"),
                              description="Height of the seat or bed this character rests on, on this beat")),
        ("bbst_char_height", dict(name="Height (m)", subtype='DISTANCE', min=0.5, max=2.6, step=1, precision=2,
                                  get=_dim_get("height"), set=_dim_setter("height"),
                                  description="Floor to the top of the head")),
        ("bbst_char_width", dict(name="Width (m)", subtype='DISTANCE', min=0.08, max=0.9, step=1, precision=2,
                                 get=_dim_get("width"), set=_dim_setter("width"),
                                 description="Side to side at the widest: the whole peg, head included, gets wider "
                                             "or narrower. 0.27 m is the standard peg at 1.75 m")),
    )


def draw_char_config(layout, context, ob):
    """The Configure Character popup: cast link, colour, height, width, pose defaults, this beat's joints, and the
    library buttons. A locked character's fields are read-only."""
    e = cast_of(ob)
    col = layout.column()
    row = col.row(align=True)
    row.label(text=who_label(ob, context.scene), icon='USER')        # the cast name, not "Shefali.006"
    op = row.operator_menu_enum("bbst.cast_link", "cast", text=e.name if e is not None else "No cast link",
                                icon='LINKED' if e is not None else 'UNLINKED')
    if op is not None:
        op.obj_name = ob.name
    box = col.box()
    sub = box.column(align=True)
    if e is not None:
        fixed = locked_fields(e)
        # a cast character's fields change it in every staging: say so (UX review of s5: Width changed nine
        # Shefalis in nine stagings, and nothing said it would)
        n = sum(1 for s in stagings() for o in stage_objects(s, roles=("char",)) if o.get(CAST_KEY) == e.cid)
        if n > 1:
            _dim(sub, f"Changes apply to every {e.name} in this file ({n} in its stagings)", 'LINKED')

        for prop in ("name", "color", "height", "width"):
            r = sub.row(align=True)
            r.enabled = prop not in fixed
            r.prop(e, prop)
        r = sub.row(align=True)
        r.enabled = "sit_at" not in fixed
        r.prop(e, "sit_at", text="Usual seat")
        r.prop(e, "lie_at", text="Usual bed")
        sub.prop(e, "notes", text="", placeholder="Notes")
        r = box.row(align=True)
        # the cast library's lock is a pin, never the padlock: the padlock in the list holds a character in place
        if fixed == ("color",):
            r.label(text="Colour fixed by the cast library", icon='PINNED')
        elif fixed:
            r.label(text="Locked in the cast library", icon='PINNED')
        else:
            r.label(text="In the library" if e.in_library else "Only in this file",
                    icon='CHECKMARK' if e.in_library else 'FILE_BLEND')
        r = box.row(align=True)
        s = r.row(align=True)
        s.enabled = len(fixed) <= 1
        s.operator("bbst.cast_save", text="Save to Library", icon='EXPORT').obj_name = ob.name
        s = r.row(align=True)
        s.enabled = e.in_library
        s.operator("bbst.cast_revert", text="Revert", icon='FILE_REFRESH').obj_name = ob.name    # ↺: back to the beat
        op = r.operator("bbst.cast_lock", text="Unlock" if fixed else "Lock", icon='UNPINNED' if fixed else 'PINNED')
        op.obj_name, op.lock = ob.name, not fixed
    else:
        sub.prop(ob, "color")
        sub.prop(ob, "bbst_char_height")
        sub.prop(ob, "bbst_char_width")
        box.operator("bbst.cast_save", text="Make a Cast Character + Save to Library", icon='EXPORT').obj_name = ob.name
    if is_peg(ob):
        # the joints fold away: Stand / Sit / Lie in the Poses panel set them (Aman, 15 Oct 2026: "I just want
        # controls to adjust the overall height and width of the model")
        b = _fold(col, "bbst_cfg_joints", f"Pose on this beat: {pose_kind(ob).title()} · fine-tune the joints",
                  'POSE_HLT')
        if b is not None:
            r = b.row(align=True)
            r.prop(ob, "bbst_pose_hip", text="Hip")
            r.prop(ob, "bbst_pose_knee", text="Knee")
            r = b.row(align=True)
            r.prop(ob, "bbst_pose_tilt", text="Lie back")
            r.prop(ob, "bbst_pose_at", text="Seat / bed")
            b.label(text="Save Beat keeps the pose, like a move", icon='INFO')


_CONFIG_UNDO = {}       # Configure Character: the character as it was when the popup opened (for Cancel)


class BBST_OT_char_config(bpy.types.Operator):
    """Configure this character: cast link, colour, height and width, where it sits and lies, this beat's joints;
    save it to your cast library, revert to it, or lock it"""
    bl_idname = "bbst.char_config"
    bl_label = "Configure Character"
    bl_options = {'REGISTER', 'UNDO'}

    obj_name: bpy.props.StringProperty(options={'SKIP_SAVE'})

    def invoke(self, context, event):
        ob = _char_target(context, self.obj_name)
        if ob is None:
            self.report({'WARNING'}, "Select a character first")
            return {'CANCELLED'}
        self.obj_name = ob.name
        e = cast_of(ob)
        # the fields edit the character live; Cancel puts back what it was when the popup opened
        _CONFIG_UNDO.clear()
        _CONFIG_UNDO.update(obj=ob.name, cast=ob.get(CAST_KEY), entry=entry_dict(e) if e is not None else None,
                            color=tuple(ob.color), height=peg_height_of(ob), width=peg_width_of(ob),
                            pose={p: float(ob.get(p, v)) for p, v in POSE_NEUTRAL.items()})
        return context.window_manager.invoke_props_dialog(self, width=380, confirm_text="Done")

    def cancel(self, context):
        u = dict(_CONFIG_UNDO)
        _CONFIG_UNDO.clear()
        ob = bpy.data.objects.get(u.get("obj", ""))
        if ob is None or ob.get(ROLE_KEY) != "char":
            return
        if u.get("cast") is None:
            if CAST_KEY in ob:
                del ob[CAST_KEY]
        else:
            ob[CAST_KEY] = u["cast"]
        e = cast_of(ob)
        if e is not None and u.get("entry") is not None and e.cid == u["entry"]["id"] and not fully_locked(e):
            if _entry_set(e, u["entry"]):
                apply_cast(e)
        elif e is None:
            ob.color = u["color"]
            set_char_size(ob, u["height"], u["width"])
        pose = u.get("pose", {})
        if is_peg(ob) and any(abs(float(ob.get(p, v)) - v) > 1e-7 for p, v in pose.items()):
            set_pose(context.scene, ob, pose)

    def draw(self, context):
        ob = _char_target(context, self.obj_name)
        if ob is not None:
            draw_char_config(self.layout, context, ob)

    def execute(self, context):
        return {'FINISHED'} if _char_target(context, self.obj_name) is not None else {'CANCELLED'}


class BBST_OT_cast_save(bpy.types.Operator):
    """Save this character to your cast library on this computer: every file offers it by name from now on"""
    bl_idname = "bbst.cast_save"
    bl_label = "Save to Library"
    bl_options = {'REGISTER', 'UNDO'}

    obj_name: bpy.props.StringProperty(options={'SKIP_SAVE'})

    def execute(self, context):
        ob = _char_target(context, self.obj_name)
        if ob is None or fstate() is None:
            return {'CANCELLED'}
        e = cast_of(ob)
        if e is None:                                   # not a cast character yet: it becomes one
            name = " ".join(re.sub(r"\.\d{3}$", "", ob.name).split()) or "Character"
            fe, le = cast_by_name(name)
            if fe is not None or le is not None:
                # the name is taken by a cast character: saving would make this one that character (or rewrite
                # it for everybody linked to it). Nothing is changed (review of 15 Oct: a red stunt double was
                # turned into blue Jai and then refused)
                other = fe.name if fe is not None else le["name"]
                self.report({'WARNING'}, f"'{other}' is a cast character already: rename this one to save it as "
                                         f"its own character, or link it to {other} (Configure Character > cast)")
                return {'CANCELLED'}
            e = new_file_cast(name, tuple(ob.color), peg_height_of(ob), peg_width_of(ob))
            ob[CAST_KEY] = e.cid
            apply_cast_to(ob, e)
        elif fully_locked(e):
            self.report({'WARNING'}, f"{e.name} is locked: unlock it to change the library")
            return {'CANCELLED'}
        try:
            cast_save(e)
        except OSError as ex:
            self.report({'ERROR'}, f"Could not write the cast library: {ex}")
            return {'CANCELLED'}
        self.report({'INFO'}, f"{e.name} saved to {cast_library_path()}")
        return {'FINISHED'}


class BBST_OT_cast_revert(bpy.types.Operator):
    """Back to the library's colour, height and width for this character (every staging follows)"""
    bl_idname = "bbst.cast_revert"
    bl_label = "Revert to Library"
    bl_options = {'REGISTER', 'UNDO'}

    obj_name: bpy.props.StringProperty(options={'SKIP_SAVE'})

    def execute(self, context):
        ob = _char_target(context, self.obj_name)
        e = cast_of(ob) if ob is not None else None
        if e is None or not cast_revert(e):
            self.report({'WARNING'}, "The library has no such character")
            return {'CANCELLED'}
        return {'FINISHED'}


class BBST_OT_cast_lock(bpy.types.Operator):
    """Lock: nobody can edit this character, and every file follows the library. Unlock to edit it again"""
    bl_idname = "bbst.cast_lock"
    bl_label = "Lock Character"
    bl_options = {'REGISTER', 'UNDO'}

    obj_name: bpy.props.StringProperty(options={'SKIP_SAVE'})
    lock: bpy.props.BoolProperty(name="Lock", default=True)

    def execute(self, context):
        ob = _char_target(context, self.obj_name)
        e = cast_of(ob) if ob is not None else None
        if e is None:
            self.report({'WARNING'}, "Not a cast character: Save to Library first")
            return {'CANCELLED'}
        try:
            cast_lock(e, self.lock)
        except OSError as ex:
            self.report({'ERROR'}, f"Could not write the cast library: {ex}")
            return {'CANCELLED'}
        if self.lock:
            cast_revert(e)
        return {'FINISHED'}


class BBST_OT_cast_link(bpy.types.Operator):
    """Which cast character this is: it takes that character's colour, height and width"""
    bl_idname = "bbst.cast_link"
    bl_label = "Cast"
    bl_options = {'REGISTER', 'UNDO'}
    bl_property = "cast"

    obj_name: bpy.props.StringProperty(options={'SKIP_SAVE'})
    cast: bpy.props.EnumProperty(name="Cast", items=_cast_items)

    def execute(self, context):
        ob = _char_target(context, self.obj_name)
        if ob is None or fstate() is None:
            return {'CANCELLED'}
        link_cast(ob, self.cast)
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


def _delete_words(scene, ob):
    """(title, message, button) for the X on a list row: what that X really does to this object."""
    who = who_label(ob, scene)
    if is_staging(scene) and any(r.copy is not None and r.copy == ob for r in scene.bb_st.set_edits):
        return (f"Give {who} back to the set?", "The staging's copy and its beat keys are deleted; the set's own "
                "piece shows again here", "Give Back")
    if ob.type == 'CAMERA':
        return f"Delete {who}?", "The camera goes with its aim point and its cuts", "Delete"
    if ob.get(ROLE_KEY) == "char":
        return f"Delete {who}?", "The character goes from this staging, with all its beat keys", "Delete"
    return f"Delete {who}?", "It goes from this staging, with all its beat keys", "Delete"


class BBST_OT_obj_action(bpy.types.Operator):
    """Act on one staged object from the list"""
    bl_idname = "bbst.obj_action"
    bl_label = "Staged Object"         # the tooltip's title; its text says what each button does (description)
    bl_options = {'REGISTER', 'UNDO'}

    obj_name: bpy.props.StringProperty()
    action: bpy.props.EnumProperty(items=[
        ('SELECT', "Select", "Pick it"), ('LOCK', "Lock", "Lock it in place"), ('DELETE', "Delete", "Delete it"),
        ('EYE', "Eyeline", "Look through its eyes"), ('FLOOR', "Drop to floor", "Put it on the floor below"),
        ('RESET', "Reset to keys", "Back to where the saved beats hold it on this frame")])

    @classmethod
    def description(cls, context, properties):
        """Every icon in the lists says what it does (UX review of s5: they all read 'Act on one staged object')."""
        ob = bpy.data.objects.get(properties.obj_name)
        a = properties.action
        if ob is None:
            return cls.__doc__
        who = who_label(ob, getattr(context, "scene", None))
        if a == 'SELECT':
            if ob.type == 'CAMERA':
                return f"Pick {who}: Camera moves shows its controls"
            if ob.get(ROLE_KEY) == AIM_ROLE:
                return f"Pick {who}, to drag where the camera looks"
            return f"Pick {who}"
        if a == 'LOCK':
            return (f"{who} is locked in place: click to unlock" if ob.get(LOCK_KEY)
                    else f"Lock {who} in place, so a click or a drag can't move it")
        if a == 'DELETE':
            title, msg, _ok = _delete_words(getattr(context, "scene", None), ob)
            return f"{title[:-1]}: {msg[:1].lower()}{msg[1:]} (it asks first)"
        if a == 'EYE':
            return f"Look through {who}'s eyes: the plan pane's view goes to the head, facing where {who} faces"
        if a == 'FLOOR':
            return f"Drop {who} onto the floor below"
        if a == 'RESET':
            return f"Back to the saved beat: {who}'s unsaved move on this beat is dropped"
        return cls.__doc__

    def invoke(self, context, event):
        """The X asks first, like Give Back in Set edits (UX review of s5: one-click deletes next to harmless
        buttons). Scripts (EXEC) never ask."""
        ob = bpy.data.objects.get(self.obj_name)
        if self.action != 'DELETE' or ob is None:
            return self.execute(context)
        title, msg, ok = _delete_words(context.scene, ob)
        try:
            return context.window_manager.invoke_confirm(self, event, title=title, message=msg, confirm_text=ok,
                                                         icon='WARNING')
        except TypeError:
            return context.window_manager.invoke_confirm(self, event)

    def execute(self, context):
        ob = bpy.data.objects.get(self.obj_name)
        if not ob:
            return {'CANCELLED'}
        if self.action == 'RESET':
            reset_to_keys(context.scene, [ob])
            request_sync(0.0)
        elif self.action == 'SELECT':
            if context.view_layer.objects.get(ob.name) != ob:
                # fuzz E (0.19): an object this view does not hold can not be selected (select_set raised)
                self.report({'WARNING'}, f"{ob.name} is not in this view")
                return {'CANCELLED'}
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
            if not (is_staging(sc) and sc.objects.get(ob.name) == ob):
                # fuzz E (0.19): the cleanup belongs to the staging that holds it, not to the window's scene
                sc = next((s for s in stagings() if s.objects.get(ob.name) == ob), sc)
            role = ob.get(ROLE_KEY)
            listed = any(c is not None and c.objects.get(ob.name) == ob
                         for c in (sub_coll(sc, "STAGE", n) for n in ("Characters", "Props", "Cameras")))
            if (role in ("boundary", PART_ROLE) + _HELPER_ROLES
                    or not (listed or role in ("char", "prop", "cam", "studio")
                            or (ob.type == 'CAMERA' and ob in stage_cams(sc)))):
                # fuzz E (0.19): the X deletes what the lists show; never the studio space, a helper or the set
                self.report({'WARNING'}, f"{ob.name} is not a character, prop, camera or studio piece")
                return {'CANCELLED'}
            if is_staging(sc) and reset_copy(sc, ob):      # a piece taken from the set: back to the set
                request_sync(0.0)
                return {'FINISHED'}
            was_cam = ob.type == 'CAMERA'
            if is_staging(sc):
                keep_unsaved(sc, [ob] + stage_cams(sc))
                tidy_camera_rigs(sc)
                try:
                    ob.name
                except ReferenceError:              # a leftover helper the tidy-up already took away
                    request_sync(0.0)
                    return {'FINISHED'}
                if was_cam:
                    release_camera(sc, ob)          # its aim, ride helper and cuts go with it
                else:
                    release_target(sc, ob)          # cameras on him (eyes, travels with, looks at) keep their picture
                for p in _piece_parts(ob):          # a Shift+D of a taken piece: its copied set parts go with it
                    bpy.data.objects.remove(p)
            try:
                bpy.data.objects.remove(ob)
            except ReferenceError:
                pass                                # a helper its cameras already let go of
            if is_staging(sc):
                prune_moves(sc)
            if was_cam and is_staging(sc) and sc.camera is None:
                cams = stage_cams(sc)
                if cams:                     # playblast and F12 need a scene camera: the cut running here, else the first
                    cut = max((m for m in sc.timeline_markers if m.camera is not None and m.frame <= sc.frame_current),
                              key=lambda m: m.frame, default=None)
                    sc.camera = cut.camera if cut is not None else cams[0]
            refresh_paths(sc)               # a deleted walker takes its paths along
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
    """A staging's Characters or Props. An object the add-on did not stage (no BB Stage role: one parented to a peg
    by hand, like Gossip Maze's "Jai's hand") shows greyed as "not staged", with no controls (PLAN, 15 Oct)."""

    def draw_item(self, context, layout, data, item, icon, active_data, active_prop, index):
        ob = item
        row = layout.row(align=True)
        role = ob.get(ROLE_KEY)
        if role not in ("char", "prop"):
            r = row.row(align=True)
            r.enabled = False
            r.label(text=f"{ob.name}  · not staged", icon='OBJECT_DATA')
            return
        e = cast_of(ob) if role == "char" else None
        sw = row.row(align=True)
        sw.ui_units_x = 1.1         # a small swatch: the row itself is where a click picks somebody (UX review of s5)
        if e is not None:       # a cast character: its colour is the cast's (every staging), its name the cast name
            sw.enabled = "color" not in locked_fields(e)
            sw.prop(e, "color", text="")
            # a label, not a field: a double-click renamed the cast character in every staging. Configure renames.
            # Two of the same cast here read "Riya" and "Riya (Riya.003)"; "Footballer 1" stays as it is
            row.label(text=who_label(ob, context.scene))
        else:
            sw.prop(ob, "color", text="")
            row.prop(ob, "name", text="", emboss=False)
        kind = pose_kind(ob) if is_peg(ob) else 'STAND'
        if kind != 'STAND':         # the pose at the playhead, only when not on their feet (s5-ui)
            tag = row.row(align=True)
            tag.enabled = False
            tag.label(text={'SIT': "sits", 'LIE': "lies"}.get(kind, "posed"))
        locked = ob.get(LOCK_KEY, False)
        op = row.operator("bbst.obj_action", text="", icon='LOCKED' if locked else 'UNLOCKED')
        op.obj_name = ob.name; op.action = 'LOCK'
        row.prop(ob, "hide_viewport", text="", emboss=False,
                 icon='HIDE_ON' if ob.hide_viewport else 'HIDE_OFF')
        if ob.get(ROLE_KEY) == "char":
            op = row.operator("bbst.obj_action", text="", icon='USER')   # eyeline: look as this character
            op.obj_name = ob.name; op.action = 'EYE'
        op = row.operator("bbst.obj_action", text="", icon='LOOP_BACK')  # back to the saved keys
        op.obj_name = ob.name; op.action = 'RESET'
        op = row.operator("bbst.obj_action", text="", icon='X')
        op.obj_name = ob.name; op.action = 'DELETE'


# ------------------------------------------------------------------ beats operators

class BBST_OT_reset_moves(bpy.types.Operator):
    """Drop every unsaved move: everyone goes back to where the saved beats hold them on this frame"""
    bl_idname = "bbst.reset_moves"
    bl_label = "Reset Moves"
    bl_options = {'REGISTER', 'UNDO'}

    def execute(self, context):
        n = reset_to_keys(context.scene)
        self.report({'INFO'}, f"{n} object(s) back on their keys" if n else "Nothing had moved")
        request_sync(0.0)
        return {'FINISHED'}


class BBST_OT_beat_insert(bpy.types.Operator):
    """Insert a beat right after the active one, saving everyone's current positions to it (the move into the next beat is split in two)"""
    bl_idname = "bbst.beat_insert"
    bl_label = "Insert Beat After"
    bl_options = {'REGISTER', 'UNDO'}

    def execute(self, context):
        scene = context.scene
        st = scene.bb_st
        if not st.beats:
            return bpy.ops.bbst.beat_add()
        i = _clamped_beat(st)
        if i >= len(st.beats) - 1:
            return bpy.ops.bbst.beat_add()      # after the last one: a plain Add
        nxt_move = st.beats[i + 1].move_s
        add_beat(scene, every=True)             # keys the current arrangement on a new last beat
        last = len(st.beats) - 1
        _QUIET["beats"] = True
        try:
            poses = sample_beat_poses(scene)    # per beat, at the frames the keys sit on right now
            st.beats.move(last, i + 1)
            for name in poses:
                poses[name].insert(i + 1, poses[name].pop(last))
            half = max(0.5, round(nxt_move / 2.0, 1))
            st.beats[i + 1].move_s = half
            st.beats[i + 1].hold_s = st.beat_hold     # it holds like any new beat; the later beats move on by that
            st.beats[i + 2].move_s = max(0.5, round(nxt_move - half, 1))
            ensure_beat_uids(scene)
            write_beat_layout(scene, poses)
        finally:
            _QUIET["beats"] = False
        st.beat_index = i + 1
        scene.frame_set(st.beats[i + 1].frame)
        settle_unsaved(scene)
        return {'FINISHED'}


def add_beat(scene, every=False):
    """A new last beat, one Default move time after the last one and holding for the Default hold time. Whatever
    you moved (off its keys at the playhead) goes into it where you see it, everybody else keeps the last beat's
    pose; every=True takes everybody's pose as it stands (Insert Beat). Returns its index."""
    st = scene.bb_st
    upgrade_beats(scene)
    f = fps(scene)
    if st.beats:
        frame = beat_out(st.beats[-1]) + max(1, round(st.beat_spacing * f))
    else:
        frame = 1
    _QUIET["beats"] = True
    try:
        b = st.beats.add()
        ensure_beat_uids(scene)
        b.move_s = st.beat_spacing if len(st.beats) > 1 else 0.0
        b.hold_s = st.beat_hold     # Aman, 15 Oct 2026: every new beat holds a second, not 0
        b.frame = frame
        b.frame_out = frame + max(0, round(b.hold_s * f))
    finally:
        _QUIET["beats"] = False
    sync_markers(scene)
    # key the current (just-arranged) positions FIRST — setting beat_index jumps the
    # playhead (click-to-jump), and any frame change before saving re-evaluates the
    # action and wipes the arrangement
    index = len(st.beats) - 1
    save_beat(scene, index, every=every)
    st.beat_index = index
    scene.frame_set(frame)
    scene.frame_end = max(beat_out(st.beats[-1]), scene.frame_start + 1)     # the last hold plays too
    settle_unsaved(scene)
    return index


class BBST_OT_beat_add(bpy.types.Operator):
    """Add a beat after the last one: what you moved goes into it, everybody else holds the last beat's pose"""
    bl_idname = "bbst.beat_add"
    bl_label = "Add Beat"
    bl_options = {'REGISTER', 'UNDO'}

    def execute(self, context):
        add_beat(context.scene)
        return {'FINISHED'}


class BBST_OT_beat_save(bpy.types.Operator):
    """Save what you moved into the beat under the playhead (between two beats: into the highlighted beat)"""
    bl_idname = "bbst.beat_save"
    bl_label = "Save Beat"
    bl_options = {'REGISTER', 'UNDO'}

    def execute(self, context):
        scene = context.scene
        st = scene.bb_st
        if not st.beats:
            return {'CANCELLED'}
        # the beat under the playhead, not the highlighted row (audit r4 H2: B1 highlighted, the timeline scrubbed
        # to B3, a move there — Save wrote B3's pose into B1). Between beats: the highlighted beat, and it says so.
        i = beat_at_frame(scene)
        between = i is None
        if between:
            i = _clamped_beat(st)
        elif i != st.beat_index:
            st["beat_index"] = i            # the list follows the playhead (an ID write: no jump)
        n = save_beat(scene, i)
        refresh_paths(scene)
        if between and n:
            self.report({'WARNING'}, f"The playhead is between beats: what you moved went into B{i + 1}, the "
                                     "highlighted beat (Insert Beat makes a beat where the playhead is)")
        elif n:
            self.report({'INFO'}, f"Saved into B{i + 1}: {n} moved")
        else:
            self.report({'INFO'}, f"Nothing had moved on B{i + 1}")
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
            apply_path_focus(scene)
            settle_unsaved(scene)
        return {'FINISHED'}


class BBST_OT_beat_delete(bpy.types.Operator):
    """Delete the highlighted beat and its poses (it asks first; the other beats keep their times)"""
    bl_idname = "bbst.beat_delete"
    bl_label = "Delete Beat"
    bl_options = {'REGISTER', 'UNDO'}

    def invoke(self, context, event):
        """The X sits between Reset Moves and the ⋮ menu: it asks first (UX review of s5). Scripts never ask."""
        st = context.scene.bb_st
        if not len(st.beats):
            return self.execute(context)
        i = _clamped_beat(st)
        b = st.beats[i]
        name = f"B{i + 1}" + (f" {b.label}" if b.label else "")
        try:
            return context.window_manager.invoke_confirm(
                self, event, title=f"Delete {name}?", message="Everybody's pose on this beat goes with it",
                confirm_text="Delete Beat", icon='WARNING')
        except TypeError:
            return context.window_manager.invoke_confirm(self, event)

    def execute(self, context):
        scene = context.scene
        st = scene.bb_st
        if not st.beats:
            return {'CANCELLED'}
        i = _clamped_beat(st)
        upgrade_beats(scene)
        if beat_at_frame(scene) != i:
            save_unsaved(scene)     # an unsaved move on another beat is kept (one on the beat that goes, goes)
        if not len(st.beat_marks):
            claim_beat_markers(scene)   # each beat keeps its own marker (and a cut on it) by its id
        camera_refs_before_beat_delete(scene, i)    # looks and step-offs on this beat move to a neighbour (0.19)
        poses = sample_beat_poses(scene)
        for p in poses.values():
            del p[i]
        start = st.beats[0].frame
        st.beats.remove(i)
        if len(st.beats):
            _QUIET["beats"] = True
            try:
                if i == 0:
                    st.beats[0].move_s = 0.0
                write_beat_layout(scene, poses, start)
            finally:
                _QUIET["beats"] = False
        else:
            clear_blocking(scene)
        st.beat_index = max(0, i - 1)
        sync_markers(scene)         # the deleted beat's marker goes (a camera cut on it stays, as a cut marker)
        prune_moves(scene)
        settle_unsaved(scene)
        return {'FINISHED'}


def clear_blocking(scene):
    """The last beat is gone: no pose is held any more, so no beat key may stay behind either (fuzz bug O: the
    next Add Beat kept them as hand-made keys, between beats that no longer exist). Everybody stays put."""
    for ob in keyed_objects(scene):
        loc, rot = ob.location.copy(), ob.rotation_euler.copy()
        _drop_fcurves(ob, set(_BLOCK_PATHS))
        ob.location, ob.rotation_euler = loc, rot
        if lens_fcurve(ob) is not None:
            lens = ob.data.lens
            _drop_fcurves(ob.data, {"lens"})
            ob.data.lens = lens
        for k in (MOVE_KEY, HELD_KEY):
            if k in ob:
                del ob[k]


class BBST_OT_move_timing(bpy.types.Operator):
    """Natural moves works out when the selected character sets off and lands. Set by Hand: choose both yourself for this one move. Back to Auto: let Natural moves decide again"""
    bl_idname = "bbst.move_timing"
    bl_label = "Move Timing"
    bl_options = {'REGISTER', 'UNDO'}

    action: bpy.props.EnumProperty(items=[('HAND', "Set by Hand", ""), ('AUTO', "Back to Auto", "")])

    def execute(self, context):
        scene = context.scene
        st = scene.bb_st
        owner = _path_owner(context)
        i = _clamped_beat(st) if len(st.beats) else 0
        if owner is None or not i:
            return {'CANCELLED'}
        uid = st.beats[i].uid
        k = next((k for k, m in enumerate(st.moves) if m.owner == owner and m.beat_uid == uid), None)
        if self.action == 'AUTO':
            if k is not None:
                st.moves.remove(k)
        elif k is None:
            s, e = path_window(st, i)
            s2, e2 = move_window(scene, owner, i)
            m = st.moves.add()
            m.owner, m.beat_uid = owner, uid
            m["start_s"] = round((s2 - s) / fps(scene), 2)      # starts from what Auto gave it
            m["end_s"] = round((e - e2) / fps(scene), 2)
        rebuild_blocking(scene)
        return {'FINISHED'}


# ------------------------------------------------------------------ path operators

def _path_owner(context):
    """The character or prop the Path box works on: the selection, or the walker of a selected path."""
    scene = context.scene
    ob = context.view_layer.objects.active if context.view_layer else None
    if ob is None or not is_staging(scene):
        return None
    if ob.get(ROLE_KEY) in ("char", "prop"):
        return ob
    if ob.type == 'CAMERA' and ob in stage_cams(scene):
        return ob
    if ob.get(ROLE_KEY) == PATH_ROLE:
        rec = path_of_curve(scene, ob)
        return rec.owner if rec is not None else None
    return None


def _onto_path_beat(scene, i):
    """Fuzz L (0.19): Add Path and Edit Path work on the highlighted beat's move, while the path focus follows the
    playhead, so after a timeline scrub the path was made hidden and Edit Path raised. They now bring the playhead
    to that beat first (as a click on its row does; the unsaved beat was saved just before). A move left between
    two beats is never dropped for it: the path is then shown as it is."""
    st = scene.bb_st
    if i is None or not 0 <= i < len(st.beats) or beat_at_frame(scene) == i:
        return
    if st.unsaved_between:
        return
    scene.frame_set(st.beats[i].frame)
    apply_path_focus(scene)
    settle_unsaved(scene)


def _active_path(context):
    """(record, beat index) of the selected walker's path into the active beat, or (None, i)."""
    scene = context.scene
    st = scene.bb_st
    if not len(st.beats):
        return None, None
    ob = context.view_layer.objects.active
    rec = path_of_curve(scene, ob) if ob is not None and ob.get(ROLE_KEY) == PATH_ROLE else None
    if rec is not None:
        return rec, beat_index_of(st, rec.beat_uid)
    i = _clamped_beat(st)
    owner = _path_owner(context)
    return (path_for(scene, owner, st.beats[i].uid) if (owner is not None and i) else None), i


def _work_override(context):
    win = context.window
    area = stage_panes(win).get("WORK") if win is not None else None
    area = area or view3d_area(context)
    region = next((r for r in area.regions if r.type == 'WINDOW'), None) if area is not None else None
    if area is None or region is None:
        return None
    return dict(window=win, screen=win.screen, area=area, region=region)


def _finish_path_edit(context, rec):
    """Leave Edit Mode on a path and settle it: ends back on the beats, arrival heading, timing."""
    scene = context.scene
    ov = _work_override(context)
    if rec.curve is not None and rec.curve.mode == 'EDIT' and ov is not None:
        with context.temp_override(**ov):
            bpy.ops.object.mode_set(mode='OBJECT')
    i = beat_index_of(scene.bb_st, rec.beat_uid)
    if i:
        fit_path(scene, rec, i)
        set_arrival_heading(scene, rec, i)
        time_path(scene, rec, i)
    if rec.curve is not None:
        _PATH_EDITING.discard(rec.curve.name)
    if scene.bb_st.natural:
        rebuild_blocking(scene)


class BBST_OT_path_add(bpy.types.Operator):
    """Draw a path for this character's (or prop's) move into the active beat: they walk it instead of a straight line, facing along it"""
    bl_idname = "bbst.path_add"
    bl_label = "Add Path"
    bl_options = {'REGISTER', 'UNDO'}

    def execute(self, context):
        if ride_helper(_path_owner(context)) is not None:
            self.report({'ERROR'}, "This camera travels with a character: set Travels with to Nobody before drawing it a path")
            return {'CANCELLED'}
        if eyes_helper(_path_owner(context)) is not None:     # exclusive both ways, as Eyes of refuses a path (0.19)
            self.report({'ERROR'}, "This camera is in somebody's eyes: set Eyes of to Nobody before drawing it a path")
            return {'CANCELLED'}
        scene = context.scene
        st = scene.bb_st
        ob = _path_owner(context)
        if ob is None:
            self.report({'ERROR'}, "Select a character, a prop or a camera first")
            return {'CANCELLED'}
        if len(st.beats) < 2:
            self.report({'ERROR'}, "Add two beats first: a path shapes the move between them")
            return {'CANCELLED'}
        i = _clamped_beat(st)
        if i == 0:
            self.report({'ERROR'}, "A path shapes the move into a beat: pick B2 or later")
            return {'CANCELLED'}
        save_unsaved(scene)
        ensure_beat_uids(scene)
        if path_for(scene, ob, st.beats[i].uid) is not None:
            self.report({'INFO'}, f"{ob.name} already has a path into B{i + 1}")
            return {'CANCELLED'}
        if ob.type == 'CAMERA' and not (st.key_cameras or cam_moves(ob)):
            set_cam_moves(scene, ob, True)      # a path is a move: the camera now moves on the beats
        create_path(scene, ob, i)
        _onto_path_beat(scene, i)           # fuzz L: the new path is shown, on the beat it leads into
        request_sync(0.0)
        self.report({'INFO'}, f"Path for {ob.name} into B{i + 1}: Edit Path, then drag its points")
        return {'FINISHED'}


class BBST_OT_path_edit(bpy.types.Operator):
    """Shape this path: drag its points and handles in the plan (the two ends stay on the beats)"""
    bl_idname = "bbst.path_edit"
    bl_label = "Edit Path"
    bl_options = {'REGISTER', 'UNDO'}

    def execute(self, context):
        rec, _i = _active_path(context)
        ov = _work_override(context)
        if rec is None or rec.curve is None or ov is None:
            self.report({'ERROR'}, "No path here yet: Add Path first")
            return {'CANCELLED'}
        save_unsaved(context.scene)
        _onto_path_beat(context.scene, beat_index_of(context.scene.bb_st, rec.beat_uid))
        vl = context.view_layer
        if vl.objects.get(rec.curve.name) != rec.curve:
            self.report({'ERROR'}, f"{rec.curve.name} is not in this view")
            return {'CANCELLED'}
        if rec.curve.hide_viewport or rec.curve.hide_get(view_layer=vl):
            rec.curve.hide_viewport = False         # fuzz L (0.19): a path hidden by the focus is shown to be edited
            rec.curve.hide_set(False, view_layer=vl)
        with context.temp_override(**ov):
            act = vl.objects.active
            if act is not None and act.mode != 'OBJECT':
                bpy.ops.object.mode_set(mode='OBJECT')
            for o in list(vl.objects.selected):
                o.select_set(False)
            rec.curve.select_set(True)
            vl.objects.active = rec.curve
            bpy.ops.object.mode_set(mode='EDIT')
            bpy.ops.curve.select_all(action='DESELECT')
            try:
                bpy.ops.wm.tool_set_by_id(name="builtin.select")     # drag a point to move it
            except Exception:
                pass
        _PATH_EDITING.add(rec.curve.name)
        return {'FINISHED'}


class BBST_OT_path_done(bpy.types.Operator):
    """Finish shaping the path"""
    bl_idname = "bbst.path_done"
    bl_label = "Done"
    bl_options = {'REGISTER', 'UNDO'}

    def execute(self, context):
        rec, _i = _active_path(context)
        if rec is None:
            ob = context.view_layer.objects.active
            if ob is not None and ob.mode == 'EDIT':
                ov = _work_override(context)
                if ov is not None:
                    with context.temp_override(**ov):
                        bpy.ops.object.mode_set(mode='OBJECT')
            return {'FINISHED'}
        _finish_path_edit(context, rec)
        if rec.owner is not None:
            _select_only(context, rec.owner)
        for w in stage_windows():
            apply_mode_tool(w)
        request_sync(0.0)
        return {'FINISHED'}


class BBST_OT_path_point(bpy.types.Operator):
    """Add: a new point in the middle of the longest stretch (or between the two points you picked). Delete: the middle points you picked"""
    bl_idname = "bbst.path_point"
    bl_label = "Path Point"
    bl_options = {'REGISTER', 'UNDO'}

    action: bpy.props.EnumProperty(items=[('ADD', "Add", ""), ('DELETE', "Delete", "")])

    @classmethod
    def poll(cls, context):
        ob = context.view_layer.objects.active if context.view_layer else None
        return ob is not None and ob.get(ROLE_KEY) == PATH_ROLE and ob.mode == 'EDIT'

    def execute(self, context):
        ob = context.view_layer.objects.active
        ov = _work_override(context)
        if ov is None or not len(ob.data.splines):
            return {'CANCELLED'}
        pts = ob.data.splines[0].bezier_points
        n = len(pts)
        if self.action == 'ADD':
            sel = [k for k, bp in enumerate(pts) if bp.select_control_point]
            if len(sel) == 2 and sel[1] - sel[0] == 1:
                pair = sel
            else:
                lens = [(pts[k + 1].co - pts[k].co).length for k in range(n - 1)]
                k = max(range(n - 1), key=lambda j: lens[j])
                pair = [k, k + 1]
            for k, bp in enumerate(pts):
                on = k in pair
                bp.select_control_point = bp.select_left_handle = bp.select_right_handle = on
            with context.temp_override(**ov):
                bpy.ops.curve.subdivide(number_cuts=1)
            pts = ob.data.splines[0].bezier_points
            for k, bp in enumerate(pts):
                on = k == pair[0] + 1
                bp.select_control_point = bp.select_left_handle = bp.select_right_handle = on
        else:
            doomed = [k for k, bp in enumerate(pts) if bp.select_control_point and 0 < k < n - 1]
            if not doomed:
                self.report({'ERROR'}, "Click a middle point first (the two ends stay on the beats)")
                return {'CANCELLED'}
            for k, bp in enumerate(pts):
                on = k in doomed
                bp.select_control_point = bp.select_left_handle = bp.select_right_handle = on
            with context.temp_override(**ov):
                bpy.ops.curve.delete(type='VERT')
        return {'FINISHED'}


class BBST_OT_path_reset(bpy.types.Operator):
    """Straighten this path again: start, middle, end"""
    bl_idname = "bbst.path_reset"
    bl_label = "Straighten Path"
    bl_options = {'REGISTER', 'UNDO'}

    def execute(self, context):
        scene = context.scene
        rec, i = _active_path(context)
        if rec is None or not i:
            return {'CANCELLED'}
        _finish_path_edit(context, rec)
        s, e = path_window(scene.bb_st, i)
        p0, p1 = keyed_location_at(rec.owner, s), keyed_location_at(rec.owner, e)
        _set_path_shape(rec, p0, _start_shape(rec.owner, p0, p1), p1)
        set_arrival_heading(scene, rec, i)
        time_path(scene, rec, i)
        return {'FINISHED'}


class BBST_OT_path_remove(bpy.types.Operator):
    """Remove this path: the move into the beat goes back to a straight line"""
    bl_idname = "bbst.path_remove"
    bl_label = "Remove Path"
    bl_options = {'REGISTER', 'UNDO'}

    def execute(self, context):
        scene = context.scene
        rec, _i = _active_path(context)
        if rec is None:
            return {'CANCELLED'}
        owner = rec.owner
        if rec.curve is not None and rec.curve.mode == 'EDIT':
            _finish_path_edit(context, rec)
        k = next(j for j, r in enumerate(scene.bb_st.paths) if r == rec)
        remove_path(scene, k)
        if owner is not None:
            _select_only(context, owner)
        for w in stage_windows():
            apply_mode_tool(w)
        request_sync(0.0)
        return {'FINISHED'}


class BBST_OT_play(bpy.types.Operator):
    """Play / pause the staging"""
    bl_idname = "bbst.play"
    bl_label = "Play / Pause"

    def execute(self, context):
        scene = context.scene
        if is_staging(scene) and not (context.screen and context.screen.is_animation_playing):
            save_unsaved(scene)          # playback re-reads the keys and would wipe unsaved moves
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


BEAT_SPLIT = 0.56          # the beat list: name on the left, Move and Hold on the right (header and rows alike)


class BBST_UL_beats(bpy.types.UIList):
    def draw_item(self, context, layout, data, item, icon, active_data, active_prop, index):
        # data is the BBST_Props group itself (the list lives on it)
        b = item
        sp = layout.split(factor=BEAT_SPLIT, align=True)    # fixed columns: Move and Hold always read (s5-ui)
        row = sp.row(align=True)
        active = (getattr(active_data, active_prop) == index)
        # the badge is the beat's save state (orange = unsaved moves); click it to jump
        op = row.operator("bbst.beat_goto", text="", emboss=active, depress=active,
                          icon='STRIP_COLOR_02' if b.dirty else 'DECORATE_KEYFRAME')
        op.index = index
        tag = row.row(align=True)
        tag.ui_units_x = 1.3
        tag.label(text=f"B{index + 1}")
        row.prop(b, "label", text="", emboss=False, placeholder="beat name")
        nums = sp.row(align=True)
        mv = nums.row(align=True)
        mv.enabled = index > 0                      # the first beat has nothing to move from
        mv.prop(b, "move_s", text="")
        nums.prop(b, "hold_s", text="")


# ------------------------------------------------------------------ cameras

def framing_camera(scene, window=None):
    """The camera the framing pane (the lower left one) looks through, else the staging's second pane camera."""
    win = window if window is not None else getattr(bpy.context, "window", None)
    area = stage_panes(win).get("CAM1") if win is not None else None
    if area is not None:
        sp = area.spaces.active
        if sp.region_3d.view_perspective == 'CAMERA':
            cam = sp.camera if sp.use_local_camera else scene.camera
            if cam is not None and cam in stage_cams(scene):
                return cam
    return pane_camera(scene, "CAM1")


def _cam_start_update(self, context):
    """Start from the framing pane: the lens follows that shot's, so the dialog shows what the camera will get."""
    if self.start == 'FRAMING':
        scene = getattr(context, "scene", None)
        cam = framing_camera(scene, getattr(context, "window", None)) if is_staging(scene) else None
        if cam is not None and cam.type == 'CAMERA':
            self.lens = cam.data.lens


class BBST_OT_cam_add(bpy.types.Operator):
    """Add a camera to this staging. A dialog asks its name, its lens, where it starts and whether it is animated
on the beats. Not ticked (the default), it is Static: it stays wherever you put it and carries no keys. Switch it
later with the camera's ◆ / ◇ button"""
    bl_idname = "bbst.cam_add"
    bl_label = "Add Camera"
    bl_options = {'REGISTER', 'UNDO'}

    name: bpy.props.StringProperty(name="Name", default="", options={'SKIP_SAVE'},
                                   description="The camera's name (empty: the next STG Cam letter)")
    lens: bpy.props.FloatProperty(name="Lens (mm)", default=35.0, min=1.0, max=5000.0, step=100, precision=0)
    # Off by default: Aman, 15 Oct 2026, a new camera is not keyframed unless he chooses it
    animated: bpy.props.BoolProperty(
        name="Animated on the beats", default=False, options={'SKIP_SAVE'},
        description="On: the camera is keyed on the beats, so moving it on a beat and Save Beat moves it there. "
                    "Off (Static): it stays where you put it and carries no keys")
    start: bpy.props.EnumProperty(name="Start from", default='STUDIO', update=_cam_start_update, items=[
        ('STUDIO', "Studio middle", "Back from the studio's middle at eye level, looking across the studio"),
        ('VIEW', "This view", "Where the view you clicked in looks from (the plan from above: the middle of what "
                              "you see of it, at eye level, facing the top of the plan)"),
        ('FRAMING', "Framing pane", "The shot the framing pane (lower left) shows: its position, direction and "
                                    "lens. The framing pane then shows the new camera")])
    # the view the button was clicked in, read when the dialog opens (the dialog itself has no 3D view)
    view_loc: bpy.props.FloatVectorProperty(size=3, options={'HIDDEN', 'SKIP_SAVE'})
    view_rot: bpy.props.FloatVectorProperty(size=4, default=(1.0, 0.0, 0.0, 0.0), options={'HIDDEN', 'SKIP_SAVE'})
    view_kind: bpy.props.StringProperty(default="", options={'HIDDEN', 'SKIP_SAVE'})    # '', PERSP, ORTHO

    def _grab_from(self, context, area, sp, r3d):
        if r3d is None:
            return False
        if r3d.view_perspective == 'CAMERA':
            cam = sp.camera if sp.use_local_camera else context.scene.camera
            if cam is None:
                return False            # an empty camera pane looks from nowhere: the next view in line
            self.view_loc = cam.matrix_world.translation
            self.view_rot = cam.matrix_world.to_quaternion()
            self.view_kind = 'PERSP'
            return True
        mw = r3d.view_matrix.inverted()
        if r3d.view_perspective == 'ORTHO':
            p = visible_view_point(area, r3d)
            self.view_loc = p if p is not None else r3d.view_location
        else:
            self.view_loc = mw.translation
        self.view_rot = mw.to_quaternion()
        self.view_kind = r3d.view_perspective
        return True

    def _grab_view(self, context):
        """The view the button was pressed in. Pressed in the sidebar or a pane's header (the only places the button
        is drawn), context.region_data is None: then that pane's own view, and from an empty camera pane the plan
        (review of s8-studio #2). False: no view found."""
        sp = getattr(context, "space_data", None)
        area = getattr(context, "area", None)
        cands = []
        if getattr(sp, "type", "") == 'VIEW_3D':
            r3d = getattr(context, "region_data", None)
            if r3d is not None:
                cands.append((area, sp, r3d))
            cands.append((area, sp, sp.region_3d))
        win = getattr(context, "window", None)
        work = stage_panes(win).get("WORK") if win is not None else None
        if work is not None and work != area:
            wsp = work.spaces.active
            cands.append((work, wsp, wsp.region_3d))
        for a, s, r in cands:
            try:
                if self._grab_from(context, a, s, r):
                    return True
            except Exception:
                continue
        return False

    def invoke(self, context, event):
        if not is_staging(context.scene):
            return self.execute(context)
        self._grab_view(context)
        if not self.properties.is_property_set("name"):
            self.name = next_camera_name(context.scene)
        if self.start == 'FRAMING':
            _cam_start_update(self, context)
        return context.window_manager.invoke_props_dialog(self, width=360, title="Add Camera", confirm_text="Add")

    def draw(self, context):
        lay = self.layout
        col = lay.column()
        col.prop(self, "name")
        col.prop(self, "lens")
        col.separator()
        col.label(text="Start from:")
        col.row().prop(self, "start", expand=True)
        col.separator()
        col.prop(self, "animated")
        sub = col.column(align=True)
        sub.enabled = False
        if self.animated:
            sub.label(text="Keyed on the beats: move it on a beat, then Save Beat", icon='KEYFRAME_HLT')
        else:
            sub.label(text="Static: it stays where you put it, no keys", icon='KEYFRAME')
        sub.label(text="Switch later with the camera's ◆ / ◇ button")

    def _place(self, context, scene, ob):
        """Put the new camera where Start from says (Studio middle: make_stage_camera already did). False: Start
        from could not be followed (no view, no framing camera) and it stays at the studio middle."""
        st = scene.bb_st
        mw = None
        if self.start == 'FRAMING':
            cam = framing_camera(scene, getattr(context, "window", None))
            if cam is None or cam == ob:
                return False
            mw = cam.matrix_world.copy()
            if cam.type == 'CAMERA':
                for attr in ("lens", "sensor_width", "sensor_fit", "shift_x", "shift_y", "clip_start", "clip_end"):
                    try:
                        setattr(ob.data, attr, getattr(cam.data, attr))
                    except Exception:
                        pass
                if self.properties.is_property_set("lens") and abs(self.lens - cam.data.lens) > 1e-3:
                    ob.data.lens = self.lens        # typed in the dialog after picking the pane: the typed one
        elif self.start == 'VIEW':
            if not self.view_kind:
                self._grab_view(context)
            if self.view_kind == 'ORTHO':
                q = Quaternion(self.view_rot)
                up = q @ Vector((0.0, 1.0, 0.0))
                yaw = math.atan2(-up.x, up.y) if Vector((up.x, up.y)).length > 1e-4 else 0.0
                p = Vector(self.view_loc)
                ob.location = (p.x, p.y, st.floor_z + EYE_HEIGHT)
                ob.rotation_euler = (math.radians(90.0), 0.0, yaw)
                return True
            if self.view_kind == 'PERSP':
                mw = Matrix.LocRotScale(Vector(self.view_loc), Quaternion(self.view_rot), None)
            else:
                return False
        if mw is not None:
            loc, rot, _s = mw.decompose()
            ob.location = loc
            ob.rotation_euler = rot.to_euler('XYZ')
        return True

    def execute(self, context):
        scene = context.scene
        if not is_staging(scene):
            self.report({'ERROR'}, "Open a staging first")
            return {'CANCELLED'}
        st = scene.bb_st
        # what the two camera panes show before the new camera exists (cam1 unset: the second camera)
        shown0, shown1 = pane_camera(scene, "CAM0"), pane_camera(scene, "CAM1")
        ob = make_stage_camera(scene, self.lens, animated=bool(self.animated), name=self.name)
        if ob is None:
            return {'CANCELLED'}
        placed = self._place(context, scene, ob)
        if scene.camera is None:
            scene.camera = ob
        took = False
        if st.cam0 is None:
            st.cam0 = ob
        elif (self.start == 'FRAMING' and placed) or shown1 is None or shown1 == shown0:
            st.cam1 = ob          # the framing pane picks up the new camera (it showed this shot, or a duplicate)
            took = True
        elif st.cam1 is None:
            st.cam1 = shown1      # the framing pane keeps the shot it showed (review of s8-studio #15)
        if self.animated and len(st.beats):
            tidy_camera_rigs(scene)
            set_cam_moves(scene, ob, True)      # one pose held on every beat until it is moved and saved
        request_sync(0.0)
        text = f"{ob.name} added: " + ("animated on the beats" if self.animated else "Static (no keys)")
        if took:
            text += "; the framing pane shows it"
        if not placed:
            self.report({'WARNING'}, text + (". No view to start from: it stands at the studio middle"
                                             if self.start == 'VIEW' else
                                             ". No framing camera to start from: it stands at the studio middle"))
        else:
            self.report({'INFO'}, text)
        return {'FINISHED'}


class BBST_OT_cam_moves(bpy.types.Operator):
    """Moves on beats: key this camera on every beat (move it on a beat, Save Beat; add a path for a gimbal move). Static: no keys, it stays put"""
    bl_idname = "bbst.cam_moves"
    bl_label = "On the Beats or Static"
    bl_options = {'REGISTER', 'UNDO'}

    cam_name: bpy.props.StringProperty()
    on: bpy.props.BoolProperty(default=True)

    @classmethod
    def description(cls, context, properties):
        """The ◆/◇ on a camera row and the switch under Camera moves say the same thing (UX review of s5)."""
        cam = bpy.data.objects.get(properties.cam_name)
        name = cam.name if cam is not None else "this camera"
        if properties.on:
            return (f"{name} is Static: left out of the beats, it stays where it is. Click to put it on the beats: "
                    "it is keyed on every beat, so a move on a beat and Save Beat move it (a path gives a gimbal move)")
        return (f"{name} is on the beats: keyed where it moves. Click to make it Static: left out of the beats, it "
                "stays where it is now (its beat moves and paths go; it asks first)")

    def invoke(self, context, event):
        cam = bpy.data.objects.get(self.cam_name)
        if not self.on and cam is not None and (cam.animation_data and cam.animation_data.action):
            return context.window_manager.invoke_confirm(
                self, event, title=f"Make {cam.name} static?",
                message="Its beat moves and paths are removed; it stays where it is now", confirm_text="Make Static")
        return self.execute(context)

    def execute(self, context):
        scene = context.scene
        cam = bpy.data.objects.get(self.cam_name)
        if cam is None or cam not in stage_cams(scene):
            return {'CANCELLED'}
        if not len(scene.bb_st.beats) and self.on:
            cam[CAM_KEY] = True         # keyed from the first beat on
            if STATIC_KEY in cam:
                del cam[STATIC_KEY]     # it really is back on the beats (the click did nothing before 0.19)
            return {'FINISHED'}
        tidy_camera_rigs(scene)
        set_cam_moves(scene, cam, self.on)
        request_sync(0.0)
        return {'FINISHED'}


_RIDE_ENUM_CACHE = []


def _ride_enum_items(self, context):
    global _RIDE_ENUM_CACHE
    scene = context.scene if context else None
    obs = stage_objects(scene, roles=("char", "prop")) if (scene is not None and is_staging(scene)) else []
    _RIDE_ENUM_CACHE = [('NONE', "Nobody (stands free)", "The camera stays where the beats put it")]
    _RIDE_ENUM_CACHE += [(o.name, who_label(o, scene), f"The camera goes wherever {who_label(o, scene)} goes, keeping its own framing")
                         for o in obs]
    return _RIDE_ENUM_CACHE


class BBST_OT_cam_ride(bpy.types.Operator):
    """The camera travels with a character: it keeps its own framing and goes wherever the character goes (a follow shot, a game camera locked to a player). Frame it on any frame as usual"""
    bl_idname = "bbst.cam_ride"
    bl_label = "Camera Travels With"
    bl_options = {'REGISTER', 'UNDO'}

    cam_name: bpy.props.StringProperty()
    target: bpy.props.EnumProperty(items=_ride_enum_items)

    def execute(self, context):
        scene = context.scene
        cam = bpy.data.objects.get(self.cam_name)
        if cam is None or cam not in stage_cams(scene):
            return {'CANCELLED'}
        tgt = bpy.data.objects.get(self.target) if self.target != 'NONE' else None
        if tgt is not None and any(r.owner == cam for r in scene.bb_st.paths):
            self.report({'ERROR'}, f"{cam.name} has a drawn path: remove it first, a camera either travels its own path or with somebody")
            return {'CANCELLED'}
        if ride_helper(cam) is not None if tgt is None else cam.constraints.get(EYES_CON) is not None:
            keep_unsaved(scene, [cam])      # only letting go of a ride (or of the eyes) re-keys the camera
        tidy_camera_rigs(scene)
        was_eyes = eyes_target(cam) if tgt is not None else None
        set_ride(scene, cam, tgt)
        if was_eyes is not None:
            self.report({'INFO'}, f"{cam.name} left {was_eyes.name}'s eyes: a camera is somebody's eyes or travels with somebody")
        request_sync(0.0)
        return {'FINISHED'}


_EYES_ENUM_CACHE = []
_STEP_ENUM_CACHE = []


def _eyes_enum_items(self, context):
    global _EYES_ENUM_CACHE
    scene = context.scene if context else None
    obs = stage_objects(scene, roles=("char",)) if (scene is not None and is_staging(scene)) else []
    _EYES_ENUM_CACHE = [('NONE', "Nobody (a camera of its own)", "The camera stays where the beats put it")]
    _EYES_ENUM_CACHE += [(o.name, who_label(o, scene), f"The camera is {who_label(o, scene)}'s eyes: it sees what he sees")
                         for o in obs]
    return _EYES_ENUM_CACHE


def _step_enum_items(self, context):
    global _STEP_ENUM_CACHE
    scene = context.scene if context else None
    beats = scene.bb_st.beats if (scene is not None and is_staging(scene)) else []
    _STEP_ENUM_CACHE = [('0', "Never (stays in the eyes)", "The camera is his point of view to the end of the shot")]
    _STEP_ENUM_CACHE += [(str(b.uid), f"B{i + 1}" + (f" {b.label}" if b.label else ""),
                          "The camera leaves the eyes on this beat and flies to its pose on the next one")
                         for i, b in enumerate(beats)]
    return _STEP_ENUM_CACHE


class BBST_OT_cam_eyes(bpy.types.Operator):
    """The camera sits in a character's eyes: it goes where his eyes go, and points where its own keys or its Looks at say. Let it step off at a beat to end the shot on his face"""
    bl_idname = "bbst.cam_eyes"
    bl_label = "Camera in the Eyes of"
    bl_options = {'REGISTER', 'UNDO'}

    cam_name: bpy.props.StringProperty()
    target: bpy.props.EnumProperty(items=_eyes_enum_items)

    def execute(self, context):
        scene = context.scene
        cam = bpy.data.objects.get(self.cam_name)
        if cam is None or cam not in stage_cams(scene):
            return {'CANCELLED'}
        char = bpy.data.objects.get(self.target) if self.target != 'NONE' else None
        if char is not None and any(r.owner == cam for r in scene.bb_st.paths):
            self.report({'ERROR'}, f"{cam.name} has a drawn path: remove it first, a camera either flies its own path or rides in somebody's eyes")
            return {'CANCELLED'}
        if (cam.constraints.get(EYES_CON) is not None if char is None
                else (ride_helper(cam) is not None or EYES_OWN_KEY in cam)):
            keep_unsaved(scene, [cam])      # only a bake re-keys the camera: leaving the eyes, or a ride it leaves
        tidy_camera_rigs(scene)
        set_eyes(scene, cam, char)
        request_sync(0.0)
        return {'FINISHED'}


class BBST_OT_cam_ride_turn(bpy.types.Operator):
    """Snorricam: the camera turns with whoever it travels with, not only goes where they go. He stays put in frame and the set swings past behind him, and when he turns, the camera swings around him. The picture it has right now is kept"""
    bl_idname = "bbst.cam_ride_turn"
    bl_label = "Turns With Them"
    bl_options = {'REGISTER', 'UNDO'}

    cam_name: bpy.props.StringProperty()
    on: bpy.props.BoolProperty(default=True)

    def execute(self, context):
        scene = context.scene
        cam = bpy.data.objects.get(self.cam_name)
        if cam is None or ride_target(cam) is None:
            return {'CANCELLED'}
        tidy_camera_rigs(scene)
        set_ride_turn(scene, cam, self.on)
        request_sync(0.0)
        return {'FINISHED'}


_LOOK_ENUM_CACHE = []


def _look_enum_items(self, context):
    global _LOOK_ENUM_CACHE
    scene = context.scene if context else None
    obs = stage_objects(scene, roles=("char", "prop")) if (scene is not None and is_staging(scene)) else []
    _LOOK_ENUM_CACHE = [
        ('NONE', "Nothing (its own rotation)", "The camera points where its own beat poses point it"),
        ('POINT', "Its aim point", "The camera points at its aim, which you place like any other pose — "
                                   "move it on a beat and Save Beat"),
    ]
    _LOOK_ENUM_CACHE += [(o.name, who_label(o, scene), f"The camera points at {who_label(o, scene)} and tracks them wherever they go")
                         for o in obs]
    return _LOOK_ENUM_CACHE


class BBST_OT_cam_looks_at(bpy.types.Operator):
    """What this camera points at from this beat on: nothing (its own rotation keys), its own aim point, or somebody it then tracks. It holds until another beat changes it, and it swings over during the move rather than snapping"""
    bl_idname = "bbst.cam_looks_at"
    bl_label = "Camera Looks At"
    bl_options = {'REGISTER', 'UNDO'}

    cam_name: bpy.props.StringProperty()
    target: bpy.props.EnumProperty(items=_look_enum_items)

    def execute(self, context):
        scene = context.scene
        cam = bpy.data.objects.get(self.cam_name)
        if cam is None or cam not in stage_cams(scene) or not len(scene.bb_st.beats):
            return {'CANCELLED'}
        if eyes_aims(cam):
            self.report({'ERROR'}, f"{cam.name} points where {who_label(eyes_target(cam), scene)}'s eyes point: free its aim first")
            return {'CANCELLED'}
        keep_unsaved(scene, [cam, aim_of(cam)])
        i = _clamped_beat(scene.bb_st)
        if self.target == 'NONE':
            set_look(scene, cam, i, None)
        elif self.target == 'POINT':
            set_look(scene, cam, i, "")
        else:
            tgt = bpy.data.objects.get(self.target)
            if tgt is None:
                return {'CANCELLED'}
            set_look(scene, cam, i, tgt)
        request_sync(0.0)
        return {'FINISHED'}


class BBST_OT_cam_free_aim(bpy.types.Operator):
    """Free this camera's aim from the eyes it sits in: it keeps its picture, but from now on it points where its own keys or its Looks at say, and the gaze sliders are gone"""
    bl_idname = "bbst.cam_free_aim"
    bl_label = "Free the Aim"
    bl_options = {'REGISTER', 'UNDO'}

    cam_name: bpy.props.StringProperty()

    def execute(self, context):
        scene = context.scene
        cam = bpy.data.objects.get(self.cam_name)
        con = cam.constraints.get(EYES_CON) if cam is not None else None
        if con is None or con.type != 'COPY_TRANSFORMS':
            return {'CANCELLED'}
        st = scene.bb_st
        keep_unsaved(scene, [cam])
        uid, _secs = step_off(cam)
        last = beat_index_of(st, uid) if uid else None
        rots = {}                                   # the aim it has now, beat by beat, so nothing moves
        for i, b in enumerate(st.beats):
            if last is not None and i > last:
                break                               # after the step-off its own pose rules: the landing stays yours
            m = eyes_world(cam, b.frame)
            if m is not None:
                rots[i] = m.to_euler('XYZ', Euler(keyed_rotation_at(cam, b.frame)))
        loc = cam.constraints.new('COPY_LOCATION')
        loc.name = EYES_CON + " tmp"
        loc.target = con.target
        cam.constraints.remove(con)
        loc.name = EYES_CON
        while cam.constraints.find(EYES_CON) > 0:
            cam.constraints.move(cam.constraints.find(EYES_CON), 0)
        order_cam_rig(cam)
        poses = sample_beat_poses(scene)
        rows = poses.get(cam.name)
        if rows is not None:
            for i, rot in rots.items():
                for k in range(3):
                    rows[i][("rotation_euler", k)] = rot[k]
        relayout_only(scene, [cam], poses)     # this camera only: nobody's unsaved move is thrown away
        request_sync(0.0)
        return {'FINISHED'}


class BBST_OT_cam_step_off(bpy.types.Operator):
    """The beat where the camera leaves the eyes. It lets go over the step-off time and flies to the pose you give it on the next beat — one shot, no cut, and it leaves from exactly the picture we were watching"""
    bl_idname = "bbst.cam_step_off"
    bl_label = "Steps Off At"
    bl_options = {'REGISTER', 'UNDO'}

    cam_name: bpy.props.StringProperty()
    beat: bpy.props.EnumProperty(items=_step_enum_items)

    def execute(self, context):
        scene = context.scene
        cam = bpy.data.objects.get(self.cam_name)
        if cam is None or eyes_helper(cam) is None:
            return {'CANCELLED'}
        keep_unsaved(scene, [cam])
        set_step_off(scene, cam, uid=int(self.beat))
        request_sync(0.0)
        return {'FINISHED'}


def _step_s_set(self, v):
    scene = getattr(bpy.context, "scene", None)
    if scene is not None and eyes_helper(self) is not None:
        set_step_off(scene, self, secs=v)


def _gaze_get(k, rest):
    return lambda ob: float(ob.rotation_euler[k] - rest)


def _gaze_setter(k, rest):
    def _set(ob, v):
        ob.rotation_euler[k] = float(v) + rest
    return _set


class BBST_OT_lens_key(bpy.types.Operator):
    """Zoom: make this camera's lens part of the beats. Change the lens on a beat and that beat keeps it, so the camera zooms on its way there. Off: one lens for the whole staging"""
    bl_idname = "bbst.lens_key"
    bl_label = "Zoom on Beats"
    bl_options = {'REGISTER', 'UNDO'}

    cam_name: bpy.props.StringProperty()
    on: bpy.props.BoolProperty(default=True)

    def execute(self, context):
        scene = context.scene
        cam = bpy.data.objects.get(self.cam_name)
        if cam is None or cam not in stage_cams(scene) or not len(scene.bb_st.beats):
            return {'CANCELLED'}
        keep_unsaved(scene, [cam])
        set_zoom(scene, cam, self.on)
        if scene.bb_st.natural:
            relayout_only(scene, [cam])     # its lens is derived like its moves; nobody else is re-keyed
        return {'FINISHED'}


class BBST_OT_rename(bpy.types.Operator):
    """Rename this camera"""
    bl_idname = "bbst.rename"
    bl_label = "Rename"
    bl_options = {'REGISTER', 'UNDO'}

    obj_name: bpy.props.StringProperty()
    new_name: bpy.props.StringProperty(name="Name")

    def invoke(self, context, event):
        self.new_name = self.obj_name
        return context.window_manager.invoke_props_dialog(self, width=300)

    def execute(self, context):
        ob = bpy.data.objects.get(self.obj_name)
        name = " ".join(self.new_name.split())
        if ob is None or not name:
            return {'CANCELLED'}
        ob.name = name
        if ob.type == 'CAMERA' and ob.data is not None:
            ob.data.name = ob.name
        if is_staging(context.scene):
            tidy_camera_rigs(context.scene, deep=False)     # its aim, ride helper and "CUT" markers take the new name
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
        if area is None:
            return {'CANCELLED'}                # no 3D view to look through (it raised before 0.19)
        space = area.spaces.active
        space.use_local_camera = True
        space.camera = ob
        space.region_3d.view_perspective = 'CAMERA'
        return {'FINISHED'}


class BBST_OT_cam_bind(bpy.types.Operator):
    """Cut to this camera at the active beat during playback (0.14 and earlier; cuts now live on the timeline)"""
    bl_idname = "bbst.cam_bind"
    bl_label = "Cut Here at Beat"
    cam_name: bpy.props.StringProperty()

    def execute(self, context):
        scene = context.scene
        st = scene.bb_st
        ob = bpy.data.objects.get(self.cam_name)
        if not (ob and st.beats) or ob not in stage_cams(scene):
            return {'CANCELLED'}             # another staging's camera would be a scene camera not in this scene
        b = st.beats[_clamped_beat(st)]
        set_cut(scene, b.frame, ob)
        return {'FINISHED'}


# ------------------------------------------------------------------ camera cuts (0.15)
#
# Aman, 10 Oct 2026: cuts are not tied to beats. A cut is a timeline marker bound to a camera, placed at any
# frame from the preview pane (or Ctrl+B in the timeline) and dragged around on the timeline like any marker.
# Blender switches the scene camera at the markers; the preview pane follows the scene camera.

CUT_PREFIX = "CUT "


def cut_markers(scene):
    return [m for m in scene.timeline_markers if m.camera is not None]


def cut_at(scene, frame):
    """The cut marker sitting exactly on this frame, if any."""
    return next((m for m in scene.timeline_markers if m.frame == frame and m.camera is not None), None)


def set_cut(scene, frame, cam):
    """Cut to cam at this frame: reuse a marker already on the frame (a beat marker keeps its name)."""
    save_unsaved(scene)         # the frame_set below re-reads the keys: an unsaved move would go (audit r4 H1)
    here = [m for m in scene.timeline_markers if m.frame == frame]
    target = next((m for m in here if m.camera is not None), None) or next((m for m in here if not m.name.startswith("B")), None)
    if target is None:
        target = scene.timeline_markers.new(f"{CUT_PREFIX}{cam.name}", frame=frame)
    for m in here:
        if m is not target and m.camera is not None:
            m.camera = None
    target.camera = cam
    if target.name.startswith(CUT_PREFIX):
        target.name = f"{CUT_PREFIX}{cam.name}"
    scene.frame_set(scene.frame_current)       # Blender applies the marker cameras on a frame change
    return target


def remove_cut(scene, frame):
    save_unsaved(scene)         # the frame_set below re-reads the keys: an unsaved move would go (audit r4 H1)
    for m in[m for m in scene.timeline_markers if m.frame == frame and m.camera is not None]:
        if m.name.startswith(CUT_PREFIX):
            scene.timeline_markers.remove(m)
        else:
            m.camera = None             # a beat marker stays, only its cut goes
    scene.frame_set(scene.frame_current)


class BBST_OT_cut_here(bpy.types.Operator):
    """Cut to this camera from the current frame on (a marker on the timeline; drag it to move the cut)"""
    bl_idname = "bbst.cut_here"
    bl_label = "Add Camera Cut"
    bl_options = {'REGISTER', 'UNDO'}
    cam: bpy.props.EnumProperty(items=lambda self, ctx: _cam_enum_items(self, ctx))   # defined further down

    def execute(self, context):
        scene = context.scene
        ob = bpy.data.objects.get(self.cam)
        if not (ob and is_staging(scene)) or ob not in stage_cams(scene):
            return {'CANCELLED'}
        set_cut(scene, scene.frame_current, ob)
        for a in context.screen.areas:
            a.tag_redraw()
        return {'FINISHED'}


class BBST_OT_cut_remove(bpy.types.Operator):
    """Remove the camera cut on the current frame"""
    bl_idname = "bbst.cut_remove"
    bl_label = "Remove Camera Cut"
    bl_options = {'REGISTER', 'UNDO'}

    def execute(self, context):
        scene = context.scene
        if cut_at(scene, scene.frame_current) is None:
            return {'CANCELLED'}
        remove_cut(scene, scene.frame_current)
        for a in context.screen.areas:
            a.tag_redraw()
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
        space.show_region_hud = False        # Blender's "Adjust Last Operation" box after a drag
    except Exception:
        pass
    # gizmos on for BB Stage's own handles; Blender's object handles stay off
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
    sett, studio, boundary, cams, stage, paths, rigs = set(), set(), set(), set(), set(), set(), set()
    for c in layer_colls(scene, "SET"):
        for ob in coll_objects(c):
            if ob.type in SET_TYPES or (ob.type == 'EMPTY' and ob.instance_type == 'COLLECTION'):
                sett.add(ob.name)
    for c in layer_colls(scene, "STUDIO"):
        for ob in coll_objects(c):
            (boundary if ob.get(ROLE_KEY) == "boundary" else studio).add(ob.name)
    for c in layer_colls(scene, "STAGE"):
        for ob in coll_objects(c):
            role = ob.get(ROLE_KEY)
            if role in (FOLLOWER_ROLE, RIDE_ROLE):
                continue                # rides the path (or carries a camera) unseen
            if role == PATH_ROLE:
                paths.add(ob.name)      # drawn in the plan only, never in a camera
                continue
            if role in (AIM_ROLE, EYES_ROLE):
                rigs.add(ob.name)       # the aim sphere and the eyes cross sat over the picture in the camera panes (0.19)
                continue
            (cams if ob.type == 'CAMERA' else stage).add(ob.name)
    return dict(set=sett, studio=studio, boundary=boundary, cams=cams, stage=stage, paths=paths, rigs=rigs)


def desired_names(plan, role, world):
    names = set(plan["stage"])
    if role == "WORK":
        names |= plan["cams"] | plan["boundary"] | plan.get("paths", set()) | plan.get("rigs", set())
    if world in ('STUDIO', 'GHOST'):
        names |= plan["studio"]
    if world in ('SET', 'GHOST'):
        names |= plan["set"]
    return names


def plan_cut(scene, space):
    """Section-cut height for the working pane, or None for no cut."""
    fs = floor_state(scene)
    st = scene.bb_st
    if not st.use_floors:
        return None             # no floors, no section cut: the whole model shows
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
        apply_path_focus(scene)          # safe here: a timer, not the middle of a depsgraph evaluation
        sync_window(win, scene)


def _ensure_local_view(win, area, scene):
    sp = area.spaces.active
    if sp.local_view is not None:
        return True
    vl = win.view_layer
    b = boundary_of(scene)
    cand = [b] if b is not None else []
    cand += stage_cams(scene)[:8]           # cameras stay clickable in every mode (Camera mode locks the people)
    cand += [o for k in ("STUDIO", "STAGE") for c in layer_colls(scene, k) for o in coll_objects(c)][:50]
    cand = [o for o in cand if o.visible_get(view_layer=vl) and not o.hide_select]
    if not cand:
        return False
    prev_sel = [o for o in scene.objects if o.select_get(view_layer=vl)]
    prev_act = vl.objects.active
    for o in prev_sel:
        o.select_set(False, view_layer=vl)
    # the first one that really takes the selection: a collection made unclickable (Easy's studio lock, Camera
    # mode's people lock) leaves select_set without effect
    pick = None
    for o in cand:
        o.select_set(True, view_layer=vl)
        if o.select_get(view_layer=vl):
            pick = o
            break
    region = next((r for r in area.regions if r.type == 'WINDOW'), None)
    try:
        if pick is None:
            raise RuntimeError("nothing in the staging can be selected")
        with bpy.context.temp_override(window=win, screen=win.screen, area=area, region=region):
            bpy.ops.view3d.localview(frame_selected=False)
    except Exception as e:
        _SYNC["last_error"] = f"local view: {e}"
    if pick is not None:
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


def apply_studio_lock(scene, locked):
    """Easy Mode: the studio (space, floor, walls, pieces) can't be clicked until Edit Studio
    is on, so a drag on the floor never moves the set build by accident."""
    for c in layer_colls(scene, "STUDIO"):
        if c.hide_select != locked:
            c.hide_select = locked
        if locked:
            for ob in coll_objects(c):
                for vl in scene.view_layers:
                    try:
                        if ob.select_get(view_layer=vl):
                            ob.select_set(False, view_layer=vl)
                    except RuntimeError:
                        pass


CAMLOCK_KEY = "bb_st_camlock"     # on a collection that Camera mode made unclickable


def _camlock_colls(scene):
    """What Camera mode makes unclickable: the staging's Characters and Props, and the set (clickable only while
    Edit Set is on). The studio (its space, floor, walls and kit) is locked by apply_studio_lock."""
    out = [c for c in (sub_coll(scene, "STAGE", k) for k in ("Characters", "Props")) if c is not None]
    for c in layer_colls(scene, "SET"):
        if c not in out:
            out.append(c)
    return out


def apply_camera_lock(scene, on, keep=()):
    """Camera mode (0.19): the staging's characters and props can't be clicked in the panes, so framing a shot never
    nudges a peg; nor can the set while Edit Set is on (review of s5: a set piece was still clickable in Camera).
    The collections are made unclickable and tagged; only a tagged one is unlocked again (one the user locked by
    hand stays locked), and never one in keep (the pointers of collections a staging in Camera mode shares: a
    Linked Copy's cast). Saving, Exit, a file load and unregister unlock."""
    for c in _camlock_colls(scene):
        try:
            if on:
                if not c.hide_select:
                    c.hide_select = True
                    c[CAMLOCK_KEY] = True
                    for ob in coll_objects(c):
                        for vl in scene.view_layers:
                            try:
                                if ob.select_get(view_layer=vl):
                                    ob.select_set(False, view_layer=vl)
                            except RuntimeError:
                                pass
            elif c.get(CAMLOCK_KEY) and c.as_pointer() not in keep:
                c.hide_select = False
                del c[CAMLOCK_KEY]
        except Exception as e:          # a linked (library) collection can not be changed
            print("BB Stage camera lock:", c.name, e)


def sync_camera_locks():
    """Camera mode's lock on every staging: on for a staging some Stage Mode window shows in Camera mode, off for
    the others. A collection shared with a staging in Camera mode (a Linked Copy's Characters) is never released,
    so a sync does not unlock and lock it again (review of s5: two needless writes per sync)."""
    wanted = {w.scene.as_pointer() for w in stage_windows() if is_staging(w.scene) and window_tab(w) == 'CAMERA'}
    ss = stagings()
    keep = {c.as_pointer() for s in ss if s.as_pointer() in wanted for c in _camlock_colls(s)}
    for s in ss:
        apply_camera_lock(s, s.as_pointer() in wanted, keep)


def release_camera_locks():
    """Every collection Camera mode locked, clickable again (any staging, any scene)."""
    for c in bpy.data.collections:
        try:
            if c.get(CAMLOCK_KEY):
                c.hide_select = False
                del c[CAMLOCK_KEY]
        except Exception:
            pass


def window_tab(win):
    """The mode tab this window's sidebar is on (Easy Mode has no Studio or Output tab: Block)."""
    ws = getattr(win, "workspace", None) if win is not None else None
    tab = getattr(ws, "bbst_tab", 'BLOCK') if (ws is not None and _is_stage_ws(ws)) else 'BLOCK'
    return 'BLOCK' if (tab in ARTIST_TABS and _mode() != 'ARTIST') else tab


def sync_window(win, scene):
    st = scene.bb_st
    roles = stage_panes(win)
    if not roles:
        return
    # Camera mode locks the studio too: a click on a locked peg fell through to the Studio Space, and G then moved
    # the whole staging (UX review of s5)
    apply_studio_lock(scene, not studio_editable() or window_tab(win) == 'CAMERA')
    sync_camera_locks()         # the people lock belongs to a staging on screen in Camera mode, and to no other
    _LAST_STG[win.as_pointer()] = scene.name
    _SYNC["last_error"] = ""      # this pass reports afresh; cut and local-view errors add to it
    sync_cast(scene)
    refresh_set_edits(scene, adopt=False, structural=False)    # flags only: a copy deleted by hand shows its original
    sync_peg_colors(scene)
    sync_contact_colors(scene)  # 0.19.1: the parts of a studio prop copied after it was made one are magenta too
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
        if role == "WORK" and not sp.overlay.show_extras:
            sp.overlay.show_extras = True       # camera outlines in the plan, to see and click them
        if role == "CAM0":
            # the preview follows the scene camera (the camera cuts on the timeline switch it)
            if scene.camera is None:
                cams = stage_cams(scene)
                if cams:
                    scene.camera = cams[0]
            if not sp.use_local_camera:
                sp.use_local_camera = True
            if scene.camera is not None and sp.camera != scene.camera:
                sp.camera = scene.camera
            if sp.region_3d.view_perspective != 'CAMERA':
                sp.region_3d.view_perspective = 'CAMERA'
            if sp.lock_camera:
                sp.lock_camera = False
            if sp.show_gizmo:
                sp.show_gizmo = False
            if sp.region_3d.use_clip_planes:
                sp.region_3d.use_clip_planes = False
        elif role.startswith("CAM"):
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
        cam.data.bbst_lens_mm = int(round(self.mm))
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
        cam.data.bbst_lens_mm = int(nxt)
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
        fs = floor_state(context.scene)
        if not context.scene.bb_st.use_floors:
            self.report({'INFO'}, "Floors are off for this staging (Settings: Floors)")
            return {'CANCELLED'}
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
        if role == "CAM0":
            # the preview: what the cuts show at this frame; a cut can be placed or removed here
            cams = stage_cams(scene)
            if not cams:
                lay.operator("bbst.cam_add", text="Add Camera", icon='ADD')
            else:
                cut = cut_at(scene, scene.frame_current)
                showing = scene.camera.name if scene.camera is not None else "—"
                lay.label(text=f"Preview · {showing}", icon='SEQUENCE')
                _dropdown(lay, 8, "bbst.cut_here", "cam",
                          f"Cut here: {cut.camera.name}" if (cut is not None and cut.camera) else "Add camera cut",
                          icon='MARKER_HLT')
                sub = lay.row(align=True)
                sub.enabled = cut is not None
                sub.operator("bbst.cut_remove", text="", icon='X')
            lay.separator_spacer()
            _draw_world_shading(lay, context, role)
            lay.separator_spacer()
            lay.label(text="cuts live on the timeline below", icon='INFO')
        elif role and role.startswith("CAM"):
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
            if st.use_floors:
                _dropdown(lay, 7, "bbst.pane_level", "level",
                          dict((k, v) for k, v, _d in LEVEL_ITEMS)[st.active_level], icon='CON_FLOOR')
            lay.separator_spacer()
            _draw_world_shading(lay, context, role or "WORK")
            lay.separator_spacer()
            if _mode() == 'ARTIST':
                r = lay.row()
                r.alert = st.needs_place
                r.operator("bbst.place_space", text="Place Studio Space", icon='OBJECT_ORIGIN')
            else:
                fs = fstate()
                if fs is not None:
                    lay.prop(fs, "edit_studio", text="Edit Studio", toggle=True,
                             icon='UNLOCKED' if fs.edit_studio else 'LOCKED')
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
            lay.operator("bbst.exit_stage", text="Exit", icon='SCREEN_BACK')
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
    for s in stagings():
        apply_studio_lock(s, False)     # plain Blender: everything clickable again
    release_camera_locks()              # Camera mode's people lock too (0.19)
    _restore_foreign_v3d_panels()
    for w in bpy.context.window_manager.windows:
        if w.as_pointer() == _EXIT["win"] and is_staging(w.scene):
            back = set_scene_of(w.scene)
            if back is not None:
                w.scene = back      # back on the set scene this staging plays in
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
        if self.easy and fs.edit_studio:
            fs["edit_studio"] = False         # Easy always starts with the studio locked
        if _in_stage(context) and not _EXIT["pending"]:
            apply_mode_tool(context.window)        # switching Easy ⇄ Artist changes the tool
            request_sync(0.0)
            return {'FINISHED'}
        mine = [] if is_staging(context.scene) else stagings_of(context.scene)
        last = _last_staging(context.window)
        scene = (context.scene if is_staging(context.scene)
                 else (last if last in mine else None) or (mine[0] if mine else None)
                 or last or (stagings() or [None])[0])
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
                # target (0.15): three 3D views + one timeline under the preview (top-left)
                timelines = [a for a in screen.areas if _is_timeline_area(a)]
                victim = next((a for a in screen.areas if a.type != 'VIEW_3D' and not _is_timeline_area(a)), None)
                if victim is None and len(timelines) > 1:
                    victim = min(timelines, key=lambda a: a.width * a.height)
                if victim is None and timelines and timelines[0].width > 0.6 * win.width:
                    victim = timelines[0]       # a full-width timeline (Blender's Layout): ours goes under the preview
                if victim is not None:
                    try:
                        with ctx.temp_override(window=win, screen=screen, area=victim):
                            bpy.ops.screen.area_close()
                    except Exception:
                        victim.ui_type = 'VIEW_3D'
                    return 0.05
                v3 = [a for a in screen.areas if a.type == 'VIEW_3D']
                if len(v3) == 4 and not timelines:
                    # the preview pane was just split: the middle piece of the left column becomes the timeline
                    work = max(v3, key=lambda a: (a.x + a.width, a.width * a.height))
                    left = sorted([a for a in v3 if a != work], key=lambda a: -a.y)
                    if len(left) == 3:
                        left[1].ui_type = 'TIMELINE'
                        return 0.05
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
                if len(v3) == 3 and not timelines:
                    preview = stage_panes(win).get("CAM0")
                    if preview is not None and preview.height > 240:
                        with ctx.temp_override(window=win, screen=screen, area=preview):
                            bpy.ops.screen.area_split(direction='HORIZONTAL', factor=0.28)
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


# ------------------------------------------------------------------ handles (gizmos)
#
# Aman, 5 Oct 2026: a click-drag already moves things, so the handles give what a drag can't:
# rings to turn, and plane squares to move on one plane. No arrows, and no scaling of
# characters or props. The studio space (its floor counts as the same thing) gets a move handle
# in the middle and resize handles on its edges and corners, no rotation.

AX_COL = {'X': (0.96, 0.22, 0.32), 'Y': (0.55, 0.86, 0.0), 'Z': (0.17, 0.56, 1.0)}
_RING_AXES = {"char": "Z", "piece": "Z", "cam": "Z", "prop": "XYZ"}
# no floor square: a click-drag already moves things along the floor (Aman, 5 Oct 2026); props and
# cameras keep the two upright squares, the only way to lift them from the plan's camera panes
_PLANES = {"char": (), "piece": (), "cam": ("XZ", "YZ"), "prop": ("XZ", "YZ")}
_PLANE_AXES = {"XY": (True, True, False), "XZ": (True, False, True), "YZ": (False, True, True)}
_PLANE_COL = {"XY": 'Z', "XZ": 'Y', "YZ": 'X'}       # coloured like the axis it does not move along
_RESIZE = {'E': (1, 0), 'W': (-1, 0), 'N': (0, 1), 'S': (0, -1),
           'NE': (1, 1), 'NW': (-1, 1), 'SE': (1, -1), 'SW': (-1, -1)}
_SPACE_COL = (1.0, 0.78, 0.15)
_HANDLES = {}       # region pointer -> its handles group (read by the GUI tests)
RING_MIN_PX = 30    # a turn ring never shrinks below this on screen (at 1x UI scale)


def _turn_ring_tris():
    """A turn ring in unit radius: two arcs, each ending in an arrowhead pointing the same way
    round, so it reads as 'turn' at a glance."""
    tris = []
    r0, r1 = 0.86, 1.0

    def p(r, a):
        return (r * math.cos(a), r * math.sin(a), 0.0)
    for a0, a1 in ((math.radians(28), math.radians(150)), (math.radians(208), math.radians(330))):
        n = 16
        for k in range(n):
            t0 = a0 + (a1 - a0) * k / n
            t1 = a0 + (a1 - a0) * (k + 1) / n
            tris += [p(r0, t0), p(r1, t0), p(r1, t1), p(r0, t0), p(r1, t1), p(r0, t1)]
        tip = a1 + math.radians(22)
        tris += [p(0.74, a1), p(1.12, a1), p(0.93, tip)]
    return tris


def _ring_select_tris():
    tris = []
    r0, r1, n = 0.7, 1.18, 48
    for k in range(n):
        t0, t1 = 2 * math.pi * k / n, 2 * math.pi * (k + 1) / n
        a = [(r0 * math.cos(t0), r0 * math.sin(t0), 0.0), (r1 * math.cos(t0), r1 * math.sin(t0), 0.0),
             (r1 * math.cos(t1), r1 * math.sin(t1), 0.0), (r0 * math.cos(t1), r0 * math.sin(t1), 0.0)]
        tris += [a[0], a[1], a[2], a[0], a[2], a[3]]
    return tris


class BBST_GT_turn(bpy.types.Gizmo):
    """Turn ring with arrows; clicking it runs the rotate its group gives it."""
    bl_idname = "BBST_GT_turn"

    def setup(self):
        if not hasattr(self, "shape"):
            self.shape = self.new_custom_shape('TRIS', _turn_ring_tris())
            self.shape_select = self.new_custom_shape('TRIS', _ring_select_tris())

    def draw(self, context):
        self.draw_custom_shape(self.shape)

    def draw_select(self, context, select_id):
        self.draw_custom_shape(self.shape_select, select_id=select_id)


def _px_per_m(region, r3d, p):
    from bpy_extras.view3d_utils import location_3d_to_region_2d
    if region is None or r3d is None:
        return None
    a = location_3d_to_region_2d(region, r3d, p)
    b = location_3d_to_region_2d(region, r3d, p + r3d.view_rotation @ Vector((1.0, 0.0, 0.0)))
    return (b - a).length if (a is not None and b is not None) else None


def ring_radius(ob, kind):
    """Just outside what it turns: a character's base disc, a prop's or piece's footprint."""
    if kind == "char":
        return 0.46
    if kind == "cam":
        return 0.4
    d = ob.dimensions
    return max(0.3, min(3.0, max(d.x, d.y) / 2 + 0.12))


def handles_on():
    """Handles and click-drag moving: always in Easy Mode, in Artist only from Settings."""
    fs = fstate()
    return _mode() == 'EASY' or bool(fs is not None and fs.artist_handles)


def studio_editable():
    """Artist can always change the studio; Easy only while Edit Studio is on."""
    fs = fstate()
    return _mode() == 'ARTIST' or bool(fs is not None and fs.edit_studio)


def handle_kind(scene, ob):
    """Which handles an object gets: char / prop / cam / piece / space, or None."""
    if ob is None or ob.get(LOCK_KEY):
        return None
    role = ob.get(ROLE_KEY)
    if role in ("char", "prop", "cam"):
        return role
    if role == "boundary" or is_studio_floor(ob):
        return "space" if studio_editable() else None
    if role == "studio":
        return "piece" if studio_editable() else None
    return None


def _axis_matrix(axis):
    """Orientation whose local Z is this world axis (a ring turns about its local Z)."""
    if axis == 'X':
        return Matrix.Rotation(math.pi / 2, 4, 'Y')
    if axis == 'Y':
        return Matrix.Rotation(-math.pi / 2, 4, 'X')
    return Matrix.Identity(4)


def _plane_matrix(plane):
    """Orientation whose local XY is this world plane (a plane square lies in its local XY)."""
    if plane == "XZ":
        return Matrix.Rotation(math.pi / 2, 4, 'X')
    if plane == "YZ":
        return Matrix.Rotation(-math.pi / 2, 4, 'Y')
    return Matrix.Identity(4)


def _style(gz, color, alpha=0.85):
    gz.color = color
    gz.alpha = alpha
    gz.color_highlight = (1.0, 1.0, 1.0)
    gz.alpha_highlight = 1.0
    gz.use_draw_scale = True


class BBST_GGT_handles(bpy.types.GizmoGroup):
    bl_idname = "BBST_GGT_handles"
    bl_label = "BB Stage handles"
    bl_space_type = 'VIEW_3D'
    bl_region_type = 'WINDOW'
    bl_options = {'3D', 'PERSISTENT'}

    @classmethod
    def poll(cls, context):
        try:
            if not (_in_stage(context) and handles_on()):
                return False
            ob = context.active_object
            return ob is not None and ob.select_get() and handle_kind(context.scene, ob) is not None
        except Exception:
            return False

    def setup(self, context):
        self.rings, self.planes, self.resize = {}, {}, {}
        for ax in "XYZ":
            gz = self.gizmos.new(BBST_GT_turn.bl_idname)
            op = gz.target_set_operator("transform.rotate")
            op.orient_axis = ax
            op.orient_type = 'GLOBAL'
            op.constraint_axis = (ax == 'X', ax == 'Y', ax == 'Z')
            op.release_confirm = True
            _style(gz, AX_COL[ax], 0.9)
            gz.use_draw_scale = False        # sized in metres around what it turns (see _place)
            self.rings[ax] = gz
        for pl, axes in _PLANE_AXES.items():
            gz = self.gizmos.new("GIZMO_GT_primitive_3d")
            gz.draw_style = 'PLANE'
            op = gz.target_set_operator("transform.translate")
            op.orient_type = 'GLOBAL'
            op.constraint_axis = axes
            op.release_confirm = True
            gz.matrix_offset = Matrix.Translation((0.42, 0.42, 0.0)) @ Matrix.Scale(0.2, 4)
            _style(gz, AX_COL[_PLANE_COL[pl]], 0.75)
            self.planes[pl] = gz
        gz = self.gizmos.new("GIZMO_GT_move_3d")          # the studio space: move from the middle
        gz.draw_style = 'RING_2D'
        gz.draw_options = {'FILL_SELECT', 'ALIGN_VIEW'}
        op = gz.target_set_operator("transform.translate")
        op.orient_type = 'GLOBAL'
        op.constraint_axis = (True, True, False)
        op.release_confirm = True
        gz.scale_basis = 0.35
        gz.line_width = 3.0
        _style(gz, _SPACE_COL, 0.9)
        self.move = gz
        for key in _RESIZE:                               # ... and resize from its edges
            gz = self.gizmos.new("GIZMO_GT_primitive_3d")
            gz.draw_style = 'PLANE'
            gz.target_set_operator("bbst.studio_resize").handle = key
            gz.matrix_offset = Matrix.Scale(0.13 if len(key) == 2 else 0.10, 4)
            _style(gz, _SPACE_COL, 0.9)
            self.resize[key] = gz
        if context.region is not None:
            _HANDLES[context.region.as_pointer()] = self
        self._place(context)

    def refresh(self, context):
        self._place(context)

    def draw_prepare(self, context):
        self._place(context)

    def _place(self, context):
        for gz in self.gizmos:
            gz.hide = True
        try:
            scene = context.scene
            ob = context.active_object
            kind = handle_kind(scene, ob) if (ob is not None and ob.select_get()) else None
            sp = context.space_data
            r3d = getattr(sp, "region_3d", None)
            if kind is not None and r3d is not None and r3d.view_perspective == 'CAMERA':
                if (sp.camera if sp.use_local_camera else scene.camera) == ob:
                    kind = None         # never handles on the camera this pane looks through
            scr = context.screen
            if kind is None or (scr is not None and scr.is_animation_playing):
                return
            if kind == "space":
                self._place_space(scene)
                return
            loc = ob.matrix_world.translation
            base = Matrix.Translation(loc)
            rad = ring_radius(ob, kind)
            ppm = _px_per_m(context.region, context.region_data, loc)
            if ppm:
                prefs = context.preferences
                rad = max(rad, RING_MIN_PX * prefs.view.ui_scale * prefs.system.pixel_size / ppm)
            for ax in _RING_AXES[kind]:
                gz = self.rings[ax]
                gz.matrix_basis = base @ _axis_matrix(ax) @ Matrix.Scale(rad, 4)
                gz.hide = False
            for pl in _PLANES[kind]:
                gz = self.planes[pl]
                gz.matrix_basis = base @ _plane_matrix(pl)
                gz.hide = False
        except Exception as e:
            print("BB Stage handles:", e)

    def _place_space(self, scene):
        b = boundary_of(scene)
        if b is None:
            return
        st = scene.bb_st
        rot = Matrix.Rotation(b.rotation_euler.z, 4, 'Z')
        c = Vector((b.location.x, b.location.y, st.floor_z))
        self.move.matrix_basis = Matrix.Translation(c) @ rot
        self.move.hide = False
        if not st.use_floors:           # no floors: lift and lower the studio too
            for pl in ("XZ", "YZ"):
                gz = self.planes[pl]
                gz.matrix_basis = Matrix.Translation(c) @ _plane_matrix(pl)
                gz.hide = False
        hw, hd = st.studio_w / 2, st.studio_d / 2
        for key, (sx, sy) in _RESIZE.items():
            p = c + rot.to_3x3() @ Vector((sx * hw, sy * hd, 0.0))
            gz = self.resize[key]
            gz.matrix_basis = Matrix.Translation(p) @ rot
            gz.hide = False


class BBST_OT_studio_resize(bpy.types.Operator):
    """Drag to resize the studio from this side; the opposite side stays where it is"""
    bl_idname = "bbst.studio_resize"
    bl_label = "Resize Studio"
    bl_options = {'REGISTER', 'UNDO', 'INTERNAL'}

    handle: bpy.props.EnumProperty(items=[(k, k, "") for k in _RESIZE], default='E')
    delta: bpy.props.FloatVectorProperty(size=2, default=(0.0, 0.0),
                                         description="How far the side moved, in metres along the studio's width and depth")

    @classmethod
    def poll(cls, context):
        return is_staging(context.scene) and boundary_of(context.scene) is not None

    def _start(self, scene):
        b = boundary_of(scene)
        st = scene.bb_st
        self.w0, self.d0 = st.studio_w, st.studio_d
        self.c0 = Vector((b.location.x, b.location.y))
        self.rot = b.rotation_euler.z

    def _apply(self, scene, shell=True):
        sx, sy = _RESIZE[self.handle]
        w = min(60.0, max(2.0, self.w0 + sx * self.delta[0])) if sx else self.w0
        d = min(60.0, max(2.0, self.d0 + sy * self.delta[1])) if sy else self.d0
        shift = Matrix.Rotation(self.rot, 2) @ Vector((sx * (w - self.w0) / 2, sy * (d - self.d0) / 2))
        resize_studio(scene, w, d, self.c0.x + shift.x, self.c0.y + shift.y, shell=shell)

    def execute(self, context):
        self._start(context.scene)
        self._apply(context.scene)
        request_sync(0.0)
        return {'FINISHED'}

    def _floor_hit(self, context, event):
        from bpy_extras import view3d_utils
        from mathutils import geometry
        r = self.region
        co = (event.mouse_x - r.x, event.mouse_y - r.y)
        o = view3d_utils.region_2d_to_origin_3d(r, self.r3d, co)
        v = view3d_utils.region_2d_to_vector_3d(r, self.r3d, co)
        z = context.scene.bb_st.floor_z
        return geometry.intersect_line_plane(o, o + v * 1e4, Vector((0.0, 0.0, z)), Vector((0.0, 0.0, 1.0)))

    def invoke(self, context, event):
        self.region, self.r3d = context.region, context.region_data
        if self.region is None or self.r3d is None:
            return self.execute(context)
        self._start(context.scene)
        self.p0 = self._floor_hit(context, event)
        if self.p0 is None:
            return {'CANCELLED'}
        self.delta = (0.0, 0.0)
        context.workspace.status_text_set("Drag to resize the studio · release to finish · Esc cancels")
        context.window_manager.modal_handler_add(self)
        return {'RUNNING_MODAL'}

    def modal(self, context, event):
        scene = context.scene
        if event.type == 'MOUSEMOVE':
            p = self._floor_hit(context, event)
            if p is not None:
                d = Matrix.Rotation(-self.rot, 2) @ Vector((p.x - self.p0.x, p.y - self.p0.y))
                self.delta = (d.x, d.y)
                self._apply(scene, shell=False)
        elif event.type == 'LEFTMOUSE' and event.value == 'RELEASE':
            context.workspace.status_text_set(None)
            self._apply(scene)
            return {'FINISHED'}
        elif event.type in ('ESC', 'RIGHTMOUSE'):
            context.workspace.status_text_set(None)
            self.delta = (0.0, 0.0)
            self._apply(scene, shell=False)
            return {'CANCELLED'}
        return {'RUNNING_MODAL'}


def apply_mode_tool(win):
    """Handles on (Easy Mode, or Artist with Settings › Easy handles): the Tweak tool, so a
    click-drag moves what is under the mouse, and BB Stage's own handles turn it. Artist
    otherwise: Select Box, everything by shortcut (G, R, S, Tab) — more manual, more control."""
    work = stage_panes(win).get("WORK")
    if work is None:
        return
    tool = "builtin.select" if handles_on() else "builtin.select_box"
    region = next((r for r in work.regions if r.type == 'WINDOW'), None)
    try:
        with bpy.context.temp_override(window=win, screen=win.screen, area=work, region=region):
            bpy.ops.wm.tool_set_by_id(name=tool)
    except Exception:
        pass


def _is_timeline_area(area):
    try:
        return area.type == 'DOPESHEET_EDITOR' and area.ui_type == 'TIMELINE'
    except Exception:
        return False


def timeline_area(window):
    """The timeline under the preview pane (0.15), if the screen has one."""
    if window is None or window.screen is None:
        return None
    tl = [a for a in window.screen.areas if _is_timeline_area(a)]
    return min(tl, key=lambda a: a.x) if tl else None


def _configure_timeline(win, area):
    area.show_menus = False
    sp = area.spaces.active
    try:
        sp.show_region_ui = False
        sp.show_region_channels = False
    except Exception:
        pass
    try:
        sp.show_markers = True
        sp.show_seconds = False
        sp.dopesheet.show_only_selected = False
    except Exception:
        pass


def _configure_stage_panes(scene_name, win):
    # the window's own staging wins: a build scheduled earlier must not undo a newer switch
    scene = win.scene if is_staging(win.scene) else (bpy.data.scenes.get(scene_name) or win.scene)
    if win.scene != scene and is_staging(scene):
        win.scene = scene
    roles = stage_panes(win)
    tl = timeline_area(win)
    if tl is not None:
        _configure_timeline(win, tl)
    for role, a in roles.items():
        a.show_menus = False
        sp = a.spaces.active
        if getattr(sp, "use_local_collections", False):
            sp.use_local_collections = False
        _declutter(sp, names=(role == "WORK"), sidebar=(role == "WORK"))
        if role == "CAM0":
            # the preview: the scene camera, which the cut markers switch; nothing is edited here.
            # A pane in local view never follows scene.camera on its own, so the pane carries its
            # own camera pointer and the frame handler keeps it equal to the scene camera.
            sp.lock_camera = False
            sp.use_local_camera = True
            if scene.camera is not None and sp.camera != scene.camera:
                sp.camera = scene.camera
            sp.show_gizmo = False
            if sp.region_3d.view_perspective != 'CAMERA':
                sp.region_3d.view_perspective = 'CAMERA'
            _flip_header_to_bottom(win, a)
        elif role.startswith("CAM"):
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
        if role == "CAM0":
            if (not sp.use_local_camera or sp.region_3d.view_perspective != 'CAMERA'
                    or (scene.camera is not None and sp.camera != scene.camera)):
                return True
        elif role.startswith("CAM"):
            cam = pane_camera(scene, role)
            if cam is not None and (sp.camera != cam or not sp.use_local_camera
                                    or sp.region_3d.view_perspective != 'CAMERA'):
                return True
    return False


def _transform_running(wm):
    return any(op.bl_idname.startswith("TRANSFORM_OT") for w in wm.windows for op in w.modal_operators)


def adopt_studio_shape(scene):
    """Artist scaled the studio space (S) or edited its points (Tab): take the new size back
    into the studio settings, so the floor, walls and handles follow. The space stays a box."""
    b = boundary_of(scene)
    if b is None or b.type != 'MESH' or b.mode != 'OBJECT' or len(b.data.vertices) < 2:
        return False
    st = scene.bb_st
    sx, sy, sz = (abs(v) for v in b.scale)
    vs = [v.co for v in b.data.vertices]
    x0, x1 = min(v.x for v in vs), max(v.x for v in vs)
    y0, y1 = min(v.y for v in vs), max(v.y for v in vs)
    z0, z1 = min(v.z for v in vs), max(v.z for v in vs)
    w, d, h = (x1 - x0) * sx, (y1 - y0) * sy, (z1 - z0) * sz
    ox, oy = (x0 + x1) / 2 * sx, (y0 + y1) / 2 * sy
    same = (max(abs(sx - 1), abs(sy - 1), abs(sz - 1)) < 1e-4 and abs(w - st.studio_w) < 1e-3
            and abs(d - st.studio_d) < 1e-3 and abs(h - st.studio_h) < 1e-3
            and abs(ox) < 1e-3 and abs(oy) < 1e-3 and abs(z0) < 1e-3)
    if same:
        return False
    off = Matrix.Rotation(b.rotation_euler.z, 2) @ Vector((ox, oy))
    b.scale = (1.0, 1.0, 1.0)
    _QUIET["dims"] = True
    try:
        st.studio_h = min(20.0, max(2.0, h))
    finally:
        _QUIET["dims"] = False
    resize_studio(scene, w, d, b.location.x + off.x, b.location.y + off.y)
    return True


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
            if is_staging(win.scene) and not _BUILD_STATE["active"] and not _transform_running(wm):
                try:
                    if adopt_studio_shape(win.scene):
                        request_sync(0.0)
                except Exception as e:
                    print("BB Stage studio shape:", e)
                try:
                    tick_paths(win.scene)
                except Exception as e:
                    print("BB Stage paths:", e)
                try:
                    if tick_camera_rigs(win.scene):
                        request_sync(0.0)       # a Shift+D camera got its own helpers (they show in the plan)
                except Exception as e:
                    print("BB Stage camera rigs:", e)
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
                    release_camera_locks()      # left Stage Mode some other way: people clickable again
                    for s in stagings():
                        apply_studio_lock(s, False)     # and the studio (Camera mode and Easy lock it)
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
        if pane_role(context.window, context.area) == "CAM0":
            self.report({'INFO'}, "The preview only watches: frame cameras in the pane below")
            return {'CANCELLED'}
        area = context.area
        region = next((r for r in area.regions if r.type == 'WINDOW'), None)   # the header button runs in HEADER
        scene = context.scene
        sp0 = area.spaces.active
        pane_cam = sp0.camera if (sp0.use_local_camera and sp0.region_3d.view_perspective == 'CAMERA') else None
        if pane_cam is not None:
            _select_only(context, pane_cam)     # F in a camera pane works on that pane's camera
        prev_cam = scene.camera
        try:
            if pane_cam is not None:
                scene.camera = pane_cam         # Set Viewer's walk flies the scene camera; it keeps
            with context.temp_override(area=area, region=region):     # its target once started
                bpy.ops.bb_sv.flythrough('INVOKE_DEFAULT')
            return {'FINISHED'}
        except Exception:
            pass
        finally:
            if pane_cam is not None and prev_cam is not None and scene.camera != prev_cam:
                scene.camera = prev_cam         # the playblast / beat-cut camera stays as it was
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


def _named_upper_floor(ground, scene=None):
    """A loft is too small for the area vote (Jai's: 8.6 m2): trust the set's own collection
    names (Loft, Mezzanine, Upper floor...) and take the height of their biggest flat top face."""
    import numpy as np
    m = set_scene_of(scene) if scene is not None else master_scene()
    if m is None:
        return None
    dg = _scene_depsgraph(scene) if scene is not None else None
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
            mw = np.array(_evaluated_matrix(ob, dg), dtype=np.float64)
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
    dg = _scene_depsgraph(scene)
    for c in layer_colls(scene, "SET") or [set_scene_of(scene).collection]:
        for ob in coll_objects(c):
            if ob.type != 'MESH' or ob.data is None or not ob.visible_get(view_layer=vl):
                continue
            mw = _evaluated_matrix(ob, dg)
            key = (ob.data.name, tuple(round(v, 3) for row in mw for v in row))
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
            m = np.array(mw, dtype=np.float64)
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
    if set_instancers(scene):
        insts = set(set_instancers(scene))
        for inst in (dg.object_instances if dg is not None else []):
            if not (inst.is_instance and inst.parent is not None and inst.parent.original in insts):
                continue
            ob = inst.object
            if ob.type != 'MESH' or ob.data is None:
                continue
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
            m = np.array(inst.matrix_world, dtype=np.float64)
            r3 = m[:3, :3]
            nw = (nor.reshape(-1, 3) @ r3.T)
            ln = np.linalg.norm(nw, axis=1)
            ln[ln == 0] = 1
            nz = nw[:, 2] / ln
            cw = cen.reshape(-1, 3) @ r3.T + m[:3, 3]
            scale = abs(np.linalg.det(r3)) ** (2 / 3)
            zs.append(cw[nz > 0.9, 2])
            areas.append(area[nz > 0.9] * scale)
            down_z.append(cw[nz < -0.9, 2])
            down_a.append(area[nz < -0.9] * scale)
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
        named = _named_upper_floor(ground, scene)    # a loft is too small for the area vote
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
        scene = context.scene
        fs = floor_state(scene)
        if fs is None:
            return {'CANCELLED'}
        g, u, gc, uc = store_floors(fs, scene)
        for s in stagings_of(set_scene_of(scene)):
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
        for ob in context.selected_objects:     # everything unselected rides along with the space
            ob.select_set(False)
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
            follow_studio_space(scene)      # the contents followed live; catch the last step
            refresh_floor(scene)
            cursor_to_studio(scene)
        else:
            try:
                self.bound.location = self.start
                follow_studio_space(scene)      # and the contents go back with it
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
    use_cuts: bpy.props.BoolProperty(name="Follow the camera cuts", default=False)

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
        if self.use_cuts and "CAM0" in roles:
            area = roles["CAM0"]        # the preview: the frame handler feeds it the cut camera per frame
        if area is None:
            self.report({'ERROR'}, "No 3D view to render from")
            return {'CANCELLED'}
        st = scene.bb_st if is_staging(scene) else None
        if st is not None:
            save_unsaved(scene)          # playback re-reads the keys and would wipe unsaved moves
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
        out = os.path.join(stage_dir(scene), f"Playblast {safe_folder_name(label, 'Camera')}.mp4")   # "Cam:1" (B12)
        saved_binds = [(mk, mk.camera) for mk in scene.timeline_markers if mk.camera]
        try:
            if not self.use_cuts:
                for mk, _c in saved_binds:
                    mk.camera = None   # a bound beat camera would hijack a per-camera playblast
            scene.camera = cam
            space.use_local_camera = True        # a local-view pane never follows scene.camera by itself:
            space.camera = cam                   # the frame handler re-points it at every cut
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
            for walker in stage_objects(scene, roles=("char", "prop")) + stage_cams(scene):
                rec = path_for(scene, walker, b.uid) if i else None
                if rec is not None:
                    lines.append(f"- {walker.name} walks a drawn path into this beat: "
                                 f"{path_length(rec):.1f} m in {b.move_s:.1f} s (see the top map)")
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
        studio_props = contact_props(scene)
        if studio_props:        # 0.19.1: the real props the studio needs on the shoot day (Studio Props.md has more)
            inv_lines += ["", "## Real props (studio contact props, W × D × H)", ""]
            inv_lines += [f"- {contact_label(o, scene)}: {size_text(o)}" + (f" — {o.get(NOTE_KEY)}" if o.get(NOTE_KEY) else "")
                          for o in studio_props]
        open(os.path.join(d, "Build Inventory.md"), "w", encoding="utf-8").write("\n".join(inv_lines))
        open(os.path.join(d, "Studio Props.md"), "w", encoding="utf-8").write(studio_props_sheet(scene, label))
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

        n = len(contact_props(scene))
        self.report({'INFO'}, f"Staging pack written to {d}" + (f" ({n} studio prop{'s' if n != 1 else ''})" if n else ""))
        return {'FINISHED'}


def studio_props_sheet(scene, label=None):
    """Studio Props.md: every studio contact prop with its size, its note, where it comes from, and where it stands
    on the first beat and each beat it moves on (metres from the studio-space centre, as the floor tape map)."""
    st = scene.bb_st
    label = label or staging_label(scene)
    b = boundary_of(scene)
    ox, oy = (b.location.x, b.location.y) if b is not None else (0.0, 0.0)
    out = [f"# Studio props — {label}", "",
           "Real props that stand in the studio on the shoot day (studio contact props). Size W × D × H in metres "
           "along the prop's own axes. Positions in metres from the studio-space centre (X right, Y up on the plan), "
           "on the first beat and on each beat it moves.", ""]
    props = contact_props(scene)
    if not props:
        out.append("None yet: Studio tab › Studio props › Make Studio Contact Prop.")
    origin = {r.copy.as_pointer(): r.original.name for r in st.set_edits if r.copy is not None and r.original is not None}
    for ob in props:
        src = (f"from the set ({origin.get(ob.as_pointer(), 'set piece')})" if ob.get(SETPIECE_KEY) else "prop block")
        out.append(f"## {contact_label(ob, scene)}")
        out.append(f"- Size: {size_text(ob)} · {src} · object {ob.name}")
        if ob.get(NOTE_KEY):
            out.append(f"- Note: {ob.get(NOTE_KEY)}")
        last = None
        frames = [(f"B{i + 1}", bt.frame) for i, bt in enumerate(st.beats)] or [("now", scene.frame_current)]
        for tag, fr in frames:
            loc, rot = keyed_location_at(ob, fr), keyed_rotation_at(ob, fr)
            pos = (round(loc.x - ox, 2), round(loc.y - oy, 2), round(math.degrees(rot.z)) % 360)
            if pos != last:
                out.append(f"- {tag}: ({pos[0]:+.2f}, {pos[1]:+.2f}), rotation {pos[2]:.0f}°")
            last = pos
        out.append("")
    return "\n".join(out) + "\n"


def build_contact_labels(scene):
    """Temporary name labels lying on the floor beside each studio prop, for the top map. Returns the objects."""
    stage = layer_colls(scene, "STAGE")
    made = []
    if not stage:
        return made
    for ob in contact_props(scene):
        cu = bpy.data.curves.new(f"LABEL {ob.name}", 'FONT')
        cu.body = contact_label(ob, scene)
        cu.size = 0.22
        cu.align_x = 'CENTER'
        lab = bpy.data.objects.new(f"LABEL {ob.name}", cu)
        w, d, _h = piece_size(ob)
        p = ob.matrix_world.translation
        lab.location = (p.x, p.y - max(w, d) / 2 - 0.3, scene.bb_st.floor_z + 0.06)
        lab.color = PROP_MAGENTA
        stage[0].objects.link(lab)
        made.append(lab)
    return made


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
        beat_pts = [Vector((xy[f][0], xy[f][1], st.floor_z + 0.05)) for f in frames]
        pts = []
        for k, v in enumerate(beat_pts):
            rec = path_for(scene, ob, st.beats[k].uid) if k else None
            if rec is not None:         # a drawn walk: the trail follows it
                pts += [Vector((q.x, q.y, st.floor_z + 0.05)) for q in path_world_points(rec)[1:-1]]
            pts.append(v)
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
        for k, v in enumerate(beat_pts):   # a flat dot on every beat
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
        trails = build_beat_trails(scene) + build_contact_labels(scene)     # 0.19.1: the studio props, named
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


# ------------------------------------------------------------------ panels (0.19: mode tabs and modules)
#
# Stage Mode's sidebar: one compact header (the staging dropdown and its … menu, the Switchboard, Settings, and the
# mode tabs Block · Camera · Studio · Output), then the modules of the tab in view, one panel each, made from MODULES
# (above BBST_Props). Easy Mode is a detail level: no Studio or Output tab, and the advanced rows stay out of view.
# Aman, 4 Oct 2026: "tabs on one side ... so we can focus on one thing at once"; 14 Oct: "make different modes for
# the different types of things that we are trying to do".

def _mode():
    fs = fstate()
    return fs.mode if fs is not None else 'ARTIST'


def cur_tab(context):
    """The mode tab the sidebar shows (read only: draw code never writes)."""
    return window_tab(getattr(context, "window", None))


def feature_on(scene, mid):
    """Is this module ticked in the staging's Switchboard (always-on modules always are)."""
    m = MODULE_BY_ID.get(mid)
    if m is None:
        return False
    if m.always:
        return True
    f = getattr(getattr(scene, "bb_st", None), "features", None)
    return bool(getattr(f, mid, m.default)) if f is not None else m.default


def module_in_use(scene, m):
    """Does the staging hold data of this module (then it is never hidden)."""
    fn = globals().get(m.in_use) if m.in_use else None
    if fn is None or scene is None:
        return False
    try:
        return bool(fn(scene))
    except Exception:
        return False


def module_shown(context, m):
    if not _in_stage(context):
        return False
    if m.artist and _mode() != 'ARTIST':
        return False
    if cur_tab(context) not in m.tabs:
        return False
    return feature_on(context.scene, m.id) or module_in_use(context.scene, m)


def features_from_defaults(scene):
    """A new staging starts with the file's Switchboard defaults (kept on the set scene, see fstate)."""
    fs = fstate()
    if fs is None or not is_staging(scene):
        return
    for m in MODULES:
        if not m.always:
            setattr(scene.bb_st.features, m.id, getattr(fs.features, m.id))


# ---- what "in use" means for each module (the Switchboard never hides a module whose data the staging has)

def poses_in_use(scene):
    """Somebody sits or lies on some beat."""
    for ob in stage_objects(scene, roles=("char",)):
        if is_peg(ob) and pose_kind(ob) != 'STAND':
            return True
        for fc in id_fcurves(ob):
            p = POSE_PATHS.get(fc.data_path)
            if p is not None and p != "bbst_seat" and any(abs(k.co.y - POSE_NEUTRAL[p]) > 1e-4
                                                          for k in fc.keyframe_points):
                return True
    return False


def props_in_use(scene):
    c = sub_coll(scene, "STAGE", "Props")
    return c is not None and any(o.get(ROLE_KEY) == "prop" for o in c.objects)


def set_edits_in_use(scene):
    st = scene.bb_st
    return st.edit_set or any(r.copy is not None for r in st.set_edits)


def paths_in_use(scene):
    return len(scene.bb_st.paths) > 0


def natural_in_use(scene):
    """A move timed by hand is data of this panel. The Natural moves switch itself is a setting (Settings has it
    too), so a staging that only has it on can still hide the panel (UX review of s5: the tick hid nothing)."""
    return len(scene.bb_st.moves) > 0


def cam_rigs_in_use(scene):
    for cam in stage_cams(scene):
        if (look_table(cam) or ride_target(cam) is not None or eyes_target(cam) is not None
                or lens_fcurve(cam) is not None or getattr(cam.data, "bbst_handheld", 0.0) > 0.0):
            return True
    return False


def cuts_in_use(scene):
    return any(m.camera is not None for m in scene.timeline_markers)


def kit_in_use(scene):
    # walls added in Walls & doors are not the Kit's (review of s8-studio #12: one Add Wall made the hidden Kit panel
    # claim this staging uses it)
    for c in layer_colls(scene, "STUDIO"):
        if any(o.get(ROLE_KEY) == "studio" and not o.get(SHELL_KEY) and not o.get(WALL_KEY)
               for o in coll_objects(c)):
            return True
    return any(o.get(STANDIN_KEY) or o.get(SOURCE_KEY) for o in stage_objects(scene))


# ---- small layout helpers

def _dim(lay, text, icon='NONE'):
    """A greyed line: a hint, never a control."""
    r = lay.row()
    r.enabled = False
    r.label(text=text, icon=icon)


def _fold(lay, idname, text, icon, closed=True):
    """A folding sub-section (Blender's layout panel) titled with its state: its body, or None while folded."""
    try:
        header, body = lay.panel(idname, default_closed=closed)
    except Exception:           # a layout without layout panels (a test's stand-in): drawn open
        lay.label(text=text, icon=icon)
        return lay.column(align=True)
    header.label(text=text, icon=icon)
    return body.column(align=True) if body is not None else None


# ---- the header: staging, … menu, Switchboard, Settings, mode tabs

def draw_stage_header(lay, context):
    scene = context.scene
    artist = _mode() == 'ARTIST'
    row = lay.row(align=True)
    row.scale_y = 1.25
    row.menu("BBST_MT_stagings", text=staging_label(scene), icon='SCENE_DATA')
    if artist:
        row.menu("BBST_MT_staging_more", text="", icon='THREE_DOTS')
    row.separator()
    row.operator("bbst.switchboard", text="", icon='MENU_PANEL')     # it picks the panels: not a tick box
    row.operator("bbst.settings", text="", icon='PREFERENCES')
    tab = cur_tab(context)
    row = lay.row(align=True)
    row.scale_y = 1.35
    for key, label, _d, icon in TABS:
        if key in ARTIST_TABS and not artist:
            continue
        # four tabs in a sidebar: words only, or they get cut ("Cam...")
        row.operator("bbst.stage_tab", text=label, icon=icon if not artist else 'NONE', depress=(tab == key)).tab = key
    if tab == 'CAMERA':
        # in a box: over the plan, a bare line had no background and could not be read (UX review of s5)
        _dim(lay.box(), "Only cameras can be clicked here", 'RESTRICT_SELECT_ON')
    if tab != 'BLOCK' and is_staging(scene) and scene.bb_st.edit_set:
        # Edit Set lives in Block: say it is still on anywhere else, and let it be switched off (review of s5)
        box = lay.box()
        r = box.row(align=True)
        r.label(text="Edit Set is on", icon='RESTRICT_SELECT_OFF')
        r.operator("bbst.edit_set", text="Switch Off").on = False
    draw_staging_copies(lay, context)


class BBST_MT_stagings(bpy.types.Menu):
    """The stagings of this file, under the set scene each plays in: pick one to go there"""
    bl_idname = "BBST_MT_stagings"
    bl_label = "Stagings"

    def draw(self, context):
        lay = self.layout
        scene = context.scene
        offered = set_scenes()
        first = True
        for src in set_scenes(offered=False):
            mine = stagings_of(src)
            if src not in offered and not mine:
                continue
            if not first:
                lay.separator()
            first = False
            lay.label(text=src.name, icon='SCENE_DATA')
            for s in mine:
                lay.operator("bbst.goto_scene", text=staging_label(s),
                             icon='CHECKMARK' if s == scene else 'BLANK1').scene_name = s.name
            if not mine:
                lay.label(text="No stagings here yet", icon='BLANK1')


class BBST_MT_staging_more(bpy.types.Menu):
    """New, Duplicate, Split off Beats, Plays in, Delete"""
    bl_idname = "BBST_MT_staging_more"
    bl_label = "Staging"

    def draw(self, context):
        lay = self.layout
        lay.operator_context = 'INVOKE_DEFAULT'
        scene = context.scene
        lay.operator("bbst.new_staging", text="New Staging…", icon='ADD')
        if not is_staging(scene):
            return
        lay.operator("bbst.duplicate_staging", text="Duplicate Staging…", icon='DUPLICATE').scene_name = scene.name
        if len(scene.bb_st.beats):
            lay.operator("bbst.split_beats", text="Split off Beats…", icon='SPLIT_HORIZONTAL').scene_name = scene.name
        # any staging, not only the one on screen (review of s5: 0.18 had these on every staging's row)
        lay.menu("BBST_MT_staging_plays_in", icon='SCENE_DATA')
        lay.separator()
        lay.menu("BBST_MT_staging_delete", icon='X')


def _staging_pick_menu(lay, context, op_id, icon):
    """One row per staging, the one on screen first: op_id with its scene_name."""
    lay.operator_context = 'INVOKE_DEFAULT'
    scene = context.scene
    ss = sorted(stagings(), key=lambda s: (s != scene, s.name.lower()))
    for s in ss:
        lay.operator(op_id, text=staging_label(s) + ("   (on screen)" if s == scene else ""),
                     icon=icon).scene_name = s.name


class BBST_MT_staging_plays_in(bpy.types.Menu):
    """Move a staging to another set scene"""
    bl_idname = "BBST_MT_staging_plays_in"
    bl_label = "Plays in Another Set Scene"

    def draw(self, context):
        _staging_pick_menu(self.layout, context, "bbst.staging_set", 'SCENE_DATA')


class BBST_MT_staging_delete(bpy.types.Menu):
    """Delete a staging (it asks first)"""
    bl_idname = "BBST_MT_staging_delete"
    bl_label = "Delete a Staging"

    def draw(self, context):
        _staging_pick_menu(self.layout, context, "bbst.delete_staging", 'X')


class BBST_OT_stage_tab(bpy.types.Operator):
    """Switch the sidebar to another kind of work"""
    bl_idname = "bbst.stage_tab"
    bl_label = "Mode"
    tab: bpy.props.EnumProperty(name="Mode", items=[(k, l, d, i, n) for n, (k, l, d, i) in enumerate(TABS)],
                                default='BLOCK')

    @classmethod
    def description(cls, context, properties):
        return next((d for k, _l, d, _i in TABS if k == properties.tab), cls.__doc__)

    def execute(self, context):
        win = context.window
        ws = win.workspace if (win is not None and _is_stage_ws(win.workspace)) else None
        if ws is None:
            return {'CANCELLED'}
        if self.tab in ARTIST_TABS and _mode() != 'ARTIST':
            self.report({'INFO'}, "Studio and Output are in Artist Mode (Settings)")
            return {'CANCELLED'}
        ws.bbst_tab = self.tab
        if is_staging(context.scene):     # at once; the sync keeps it so
            apply_studio_lock(context.scene, not studio_editable() or self.tab == 'CAMERA')
            sync_camera_locks()
        request_sync(0.0)
        _caption_redraw(self, context)
        return {'FINISHED'}


def draw_switchboard(lay, context):
    """The Switchboard popup: a tick per module of this staging, grouped by mode tab, with what each one does."""
    scene = context.scene
    if not is_staging(scene):
        lay.label(text="Open a staging first", icon='INFO')
        return
    feat = scene.bb_st.features
    artist = _mode() == 'ARTIST'
    lay.label(text=f"Panels shown in {staging_label(scene)}", icon='MENU_PANEL')
    # Aman expected an untick to switch a feature off (UX review of s5): say plainly that it only hides the panel
    _dim(lay, "Untick a panel to hide it. Hiding a panel switches nothing off.")
    _dim(lay, "A panel holding something this staging uses stays in view.")
    for key, label, _d, icon in TABS:
        mods = [m for m in MODULES if m.tabs[0] == key]
        if not mods:
            continue
        col = lay.box().column(align=True)
        col.label(text=label + " tab" + ("" if artist or key not in ARTIST_TABS else "   (Artist Mode)"), icon=icon)
        for m in mods:
            row = col.split(factor=0.34, align=True)
            if m.always:
                r = row.row()
                r.enabled = False
                r.label(text=m.label, icon='CHECKBOX_HLT')
                note = "Always shown"
            else:
                row.prop(feat, m.id, text=m.label)
                note = ("In use here, so it stays" if (not feature_on(scene, m.id) and module_in_use(scene, m))
                        else m.what)
            r = row.row()
            r.enabled = False
            r.label(text=note)
    lay.separator()
    lay.operator("bbst.features_default", icon='FILE_TICK')


class BBST_OT_switchboard(bpy.types.Operator):
    """Switchboard: pick the panels this staging shows in the sidebar. Hiding a panel switches nothing off, and a
panel holding something the staging uses stays in view"""
    bl_idname = "bbst.switchboard"
    bl_label = "Switchboard"

    def invoke(self, context, event):
        if not is_staging(context.scene):
            return {'CANCELLED'}
        return context.window_manager.invoke_popup(self, width=620)

    def draw(self, context):
        draw_switchboard(self.layout, context)

    def execute(self, context):
        return {'FINISHED'}


class BBST_OT_feature_set(bpy.types.Operator):
    """Show or hide this panel in this staging (the same tick as in the Switchboard)"""
    bl_idname = "bbst.feature_set"
    bl_label = "Show Panel"
    bl_options = {'REGISTER', 'UNDO'}
    module: bpy.props.EnumProperty(name="Feature", items=[(m.id, m.label, m.what) for m in MODULES if not m.always])
    on: bpy.props.BoolProperty(name="On", default=True)

    def execute(self, context):
        scene = context.scene
        if not is_staging(scene):
            return {'CANCELLED'}
        setattr(scene.bb_st.features, self.module, self.on)
        return {'FINISHED'}


class BBST_OT_features_default(bpy.types.Operator):
    """Every new staging made in this file starts with this staging's ticks"""
    bl_idname = "bbst.features_default"
    bl_label = "Use These for New Stagings"
    bl_options = {'REGISTER', 'UNDO'}

    def execute(self, context):
        fs = fstate()
        scene = context.scene
        if fs is None or not is_staging(scene):
            return {'CANCELLED'}
        for m in MODULES:
            if not m.always:
                setattr(fs.features, m.id, getattr(scene.bb_st.features, m.id))
        self.report({'INFO'}, "New stagings in this file start with these features")
        return {'FINISHED'}


def draw_settings(lay, context):
    """The Settings popup: what is set once and rarely changed (Aman, 14 Oct 2026: "for some of these settings i
    feel it's not necessary to put them in the main ui. there could be a button that pops up a dialogue")."""
    # UX review of s5: it mixed this staging's settings with the whole file's without saying which (a Hold of 2.0
    # changed one staging of seventeen), so each part is titled with what it applies to
    scene = context.scene
    fs = fstate()
    artist = _mode() == 'ARTIST'
    lay.label(text="Settings", icon='PREFERENCES')
    if is_staging(scene):
        st = scene.bb_st
        box = lay.box()
        box.label(text=f"This staging only: {staging_label(scene)}", icon='SCENE_DATA')
        col = box.column(align=True)
        col.label(text="Beats you add from now on:")
        col.prop(st, "beat_spacing")
        col.prop(st, "beat_hold")
        col = box.column(align=True)
        col.label(text="Movement:")
        col.prop(st, "natural", text="Natural moves (each at their own pace)")
        sub = col.column(align=True)
        sub.enabled = st.natural
        sub.prop(st, "pace")
        if not st.natural:
            _dim(col, "Walking pace needs Natural moves on")
        col.prop(st, "alive", slider=True)
        col = box.column(align=True)
        col.label(text="On screen:")
        col.prop(st, "show_captions")
        _dim(col, "Captions never show in a playblast")
        col.prop(st, "path_focus")
        col.prop(st, "black_outside")
    box = lay.box()
    box.label(text="Every staging in this file", icon='FILE_BLEND')
    col = box.column(align=True)
    col.label(text="Detail level:")
    row = col.row(align=True)
    row.scale_y = 1.2
    row.operator("bbst.enter_stage", text="Easy", depress=not artist).easy = True
    row.operator("bbst.enter_stage", text="Artist", depress=artist).easy = False
    _dim(col, "Easy: Block and Camera tabs only")
    if artist and fs is not None:
        col = box.column(align=True)
        col.prop(fs, "artist_handles")
        _dim(col, "On: click and drag moves people, with turn handles")
        col = box.column(align=True)
        col.label(text="Set scenes New Staging offers:")
        sets = set_scenes(offered=False)
        flow = col.grid_flow(columns=2, even_columns=True, align=True) if len(sets) > 5 else col
        for sc in sets:
            flow.prop(sc.bb_st, "stageable", text=f"Set scene “{sc.name}”" if len(sets) <= 5 else sc.name)
        if not any(sc.bb_st.stageable for sc in sets):
            _dim(col, "None ticked, so every set scene is offered", 'INFO')
    lay.separator()
    lay.operator("bbst.fix_screen", icon='FILE_REFRESH')
    _dim(lay, "Fix Screen: rebuilds the panes when something looks wrong")


class BBST_OT_settings(bpy.types.Operator):
    """Settings: Easy or Artist, the times new beats get, walking pace, what the panes show, and the rest you set
once"""
    bl_idname = "bbst.settings"
    bl_label = "Settings"

    def invoke(self, context, event):
        if fstate() is None:
            return {'CANCELLED'}
        return context.window_manager.invoke_popup(self, width=420)

    def draw(self, context):
        draw_settings(self.layout, context)

    def execute(self, context):
        return {'FINISHED'}


# ---- Block: Beats, Characters (+ Poses), Props, Set edits, Paths, Natural moves

def draw_path_box(lay, context):
    """Under the active beat: the selected character's (or prop's) drawn path into it."""
    scene = context.scene
    st = scene.bb_st
    owner = _path_owner(context)
    if owner is None or not len(st.beats):
        return
    rec, i = _active_path(context)
    box = lay.box()
    col = box.column(align=True)
    row = col.row(align=True)
    row.label(text=f"Path · {who_label(owner, scene)}", icon='CURVE_BEZCURVE')
    row.prop(st, "path_focus", text="", icon='HIDE_OFF' if st.path_focus else 'HIDE_ON', toggle=True)
    if len(st.beats) < 2 or not i:
        col.label(text="Pick B2 or later: a path shapes the walk into that beat", icon='INFO')
    elif rec is None:
        r = col.row()
        r.scale_y = 1.2
        r.operator("bbst.path_add", text=f"Add Path into B{i + 1}", icon='ADD')
    elif rec.curve is not None and rec.curve.mode == 'EDIT':
        col.label(text="Drag points · ends stay on beats", icon='INFO')
        row = col.row(align=True)
        row.operator("bbst.path_point", text="Add Point", icon='ADD').action = 'ADD'
        row.operator("bbst.path_point", text="Delete Point", icon='REMOVE').action = 'DELETE'
        r = col.row()
        r.scale_y = 1.3
        r.operator("bbst.path_done", text="Done", icon='CHECKMARK')
    else:
        row = col.row(align=True)
        row.operator("bbst.path_edit", text="Edit Path", icon='EDITMODE_HLT')
        row.operator("bbst.path_reset", text="Straighten", icon='IPO_LINEAR')
        row.operator("bbst.path_remove", text="", icon='X')
    if rec is not None and i and owner.get(ROLE_KEY) != "char":
        col.prop(rec, "face_path")
    if rec is not None and i:
        s, e = move_window(scene, owner, i)
        secs = (e - s) / fps(scene)
        length = path_length(rec)
        speed = length / secs if secs > 0 else 0.0
        col.label(text=f"{length:.1f} m in {secs:.1f} s · {speed:.1f} m/s",
                  icon='ERROR' if (owner.get(ROLE_KEY) == "char" and speed > 1.6) else 'TIME')
    mine = sorted(((beat_index_of(st, r.beat_uid), r) for r in st.paths if r.owner == owner),
                  key=lambda x: -1 if x[0] is None else x[0])
    others = [(k, r) for k, r in mine if k and k != i]
    if others:
        col.separator()
        for k, r in others:
            row = col.row(align=True)
            row.label(text=f"Path into B{k + 1} · {path_length(r):.1f} m", icon='CURVE_PATH')
            row.operator("bbst.beat_goto", text="", icon='FORWARD').index = k


def draw_move_box(lay, context):
    """Natural moves, under the active beat: when the selected character (prop, moving camera) sets off and lands."""
    scene = context.scene
    st = scene.bb_st
    if not st.natural or len(st.beats) < 2:
        return
    owner = _path_owner(context)
    i = _clamped_beat(st)
    if owner is None or not i or (owner.type == 'CAMERA' and not cam_moves(owner)):
        return
    f = fps(scene)
    s, e = path_window(st, i)
    s2, e2 = move_window(scene, owner, i)
    rec = move_rec(scene, owner, st.beats[i].uid)
    box = lay.box()
    col = box.column(align=True)
    col.label(text=f"Timing · {who_label(owner, scene)} into B{i + 1}", icon='TIME')
    if rec is None:
        if (s2, e2) == (s, e):
            col.label(text=f"Auto: uses the whole {(e - s) / f:.1f} s")
        else:
            col.label(text=f"Auto: waits {(s2 - s) / f:.1f} s, moves {(e2 - s2) / f:.1f} s, lands {(e - e2) / f:.1f} s early")
        col.operator("bbst.move_timing", text="Set by Hand", icon='GREASEPENCIL').action = 'HAND'
    else:
        row = col.row(align=True)
        row.prop(rec, "start_s")
        row.prop(rec, "end_s")
        if owner.get(ROLE_KEY) == "char":
            col.prop(rec, "face", text="")
        col.label(text=f"Moves {(e2 - s2) / f:.1f} s of {(e - s) / f:.1f} s")
        col.operator("bbst.move_timing", text="Back to Auto", icon='AUTO').action = 'AUTO'


def draw_unsaved_between(lay, context):
    """A move made while the playhead is between two beats belongs to no beat: say so, and where Save puts it."""
    st = context.scene.bb_st
    if not (st.unsaved_between and len(st.beats)):
        return
    box = lay.box()
    box.alert = True
    col = box.column(align=True)
    col.label(text="Moved between two beats", icon='ERROR')
    col.label(text=f"Save Beat puts it into B{_beat_row(st) + 1} (highlighted)")
    col.label(text="A jump or a scrub drops it; Ctrl+S keeps it")


def _beat_row(st):
    """The highlighted beat, read only (draw code must not write: _clamped_beat would)."""
    return min(max(st.beat_index, 0), len(st.beats) - 1) if len(st.beats) else 0


class BBST_MT_beat_more(bpy.types.Menu):
    """Beats: the rarer actions"""
    bl_idname = "BBST_MT_beat_more"
    bl_label = "Beats"

    def draw(self, context):
        lay = self.layout
        st = context.scene.bb_st
        lay.operator("bbst.fit_range", icon='PREVIEW_RANGE')
        lay.prop(st, "carry_set")


def _save_label(scene, n):
    """Save Beat names the beat it writes: the one under the playhead, else the highlighted one."""
    if not n:
        return "Save Beat"
    i = beat_at_frame(scene)
    return f"Save B{(_beat_row(scene.bb_st) if i is None else i) + 1}"


def _transport(lay, context, n):
    row = lay.grid_flow(row_major=True, columns=5, even_columns=True, align=True)
    row.operator("bbst.beat_goto", text="", icon='REW').index = 0
    row.operator("bbst.step_beat", text="", icon='PREV_KEYFRAME').forward = False
    playing = context.screen.is_animation_playing if context.screen else False
    row.operator("bbst.play", text="", icon='PAUSE' if playing else 'PLAY')
    row.operator("bbst.step_beat", text="", icon='NEXT_KEYFRAME').forward = True
    row.operator("bbst.beat_goto", text="", icon='FF').index = max(0, n - 1)


def _beat_list(lay, st, rows, list_id=""):
    hdr = lay.row()
    hdr.separator(factor=0.6)           # the list's frame
    sp = hdr.split(factor=BEAT_SPLIT)
    sp.label(text="Beat")
    nums = sp.row(align=True)
    for text in ("Move s", "Hold s"):
        c = nums.row()
        c.alignment = 'CENTER'
        c.label(text=text)
    hdr.separator(factor=1.4)           # the list's scrollbar
    if list_id:     # the short list: its own id, so it never takes the size Block's list was dragged to (UX review)
        lay.template_list("BBST_UL_beats", list_id, st, "beats", st, "beat_index", rows=rows, maxrows=rows)
    else:
        lay.template_list("BBST_UL_beats", "", st, "beats", st, "beat_index", rows=rows)


def draw_beats(lay, context, compact=False):
    """Beats (Block), or its short form (Camera): what changes when, and Save Beat."""
    scene = context.scene
    st = scene.bb_st
    n = len(st.beats)
    idx = _beat_row(st)
    unsaved = n > 0 and (st.unsaved_between or any(b.dirty for b in st.beats))   # the playhead's beat, not the row's
    save_icon = 'STRIP_COLOR_02' if unsaved else 'KEYINGSET'
    if compact:
        sp = lay.split(factor=0.42)
        sp.scale_y = 1.3
        sub = sp.row(align=True)
        sub.enabled = n > 0
        sub.alert = unsaved
        sub.operator("bbst.beat_save", text=_save_label(scene, n), icon=save_icon)
        _transport(sp, context, n)
        draw_unsaved_between(lay, context)
        if n:
            _beat_list(lay, st, 3, list_id="short")
        else:
            _dim(lay, "No beats yet: add them in Block", 'INFO')
        return
    row = lay.row(align=True)
    row.scale_y = 1.5
    row.operator("bbst.beat_add", icon='ADD')
    sub = row.row(align=True)
    sub.enabled = n > 0
    sub.alert = unsaved         # Blender's red tint: the strongest signal a button has (no orange button exists)
    sub.operator("bbst.beat_save", text=_save_label(scene, n), icon=save_icon)
    row = lay.row(align=True)
    sub = row.row(align=True)
    sub.enabled = n > 0
    sub.operator("bbst.beat_insert", text="Insert After", icon='NODE_INSERT_ON')
    sub = row.row(align=True)
    sub.enabled = unsaved
    sub.operator("bbst.reset_moves", text="Reset Moves", icon='LOOP_BACK')
    sub = row.row(align=True)
    sub.enabled = n > 0
    sub.operator("bbst.beat_delete", text="", icon='X')
    row.menu("BBST_MT_beat_more", text="", icon='THREE_DOTS')
    draw_unsaved_between(lay, context)
    row = lay.row()
    row.scale_y = 1.3
    _transport(row, context, n)
    if not n:
        _dim(lay, "Place everyone, then Add Beat", 'INFO')
        return
    _beat_list(lay, st, 5)
    lay.prop(st.beats[idx], "note", text="", placeholder="What happens on this beat")
    if n > 1:
        total = (beat_out(st.beats[-1]) - st.beats[0].frame) / fps(scene)
        warn = "" if 4 <= total <= 30 else "  (outside Seedance 4–30 s)"
        lay.label(text=f"Total: {total:.1f} s{warn}", icon='TIME')
        top = beat_top_speed(scene, idx)
        if top and top[1] > 0.05:
            top = (who_label(bpy.data.objects.get(top[0]), scene) or top[0], top[1])     # "Jai", not "Jai.013"
            r = lay.row()
            if top[1] > HUMAN_MAX_SPEED:
                r.alert = True       # red: nobody moves that fast; fine for a previz, but know it
                r.label(text=f"{top[0]} {top[1]:.1f} m/s to next beat — beyond human", icon='ERROR')
            elif top[1] > 1.6:
                r.label(text=f"{top[0]} {top[1]:.1f} m/s to next beat — running", icon='ERROR')
            else:
                r.label(text=f"Fastest to next beat: {top[0]} {top[1]:.1f} m/s", icon='CHECKMARK')
    draw_split_beats(lay, context)


def draw_cast(lay, context):
    """Characters: add one by name (the cast library is searched as you type), the list, the picked one's card."""
    scene = context.scene
    st = scene.bb_st
    chars = sub_coll(scene, "STAGE", "Characters")
    if chars is None:
        _dim(lay, "This staging has no Characters collection", 'ERROR')
        return
    row = lay.row(align=True)
    row.scale_y = 1.2
    row.prop(st, "new_char_name", text="", icon='VIEWZOOM', placeholder="Name, or search the cast")
    row.operator("bbst.add_char", text="Add", icon='ADD')
    lay.template_list("BBST_UL_objects", "chars", chars, "objects", st, "char_index", rows=3)
    if not len(chars.objects):
        _dim(lay, "Type a name and press Add", 'INFO')
        return
    ob = _char_target(context)
    col = lay.box().column(align=True)
    if ob is None:
        _dim(col, "Click a character for its card", 'INFO')
    else:
        e = cast_of(ob)
        sp = col.split(factor=0.5, align=True)
        sp.label(text=cast_name(ob), icon='LINKED' if e is not None else 'USER')
        row = sp.row(align=True)
        row.operator("bbst.char_config", text="Configure…", icon='PREFERENCES').obj_name = ob.name
        if e is None or not e.in_library:
            row.operator("bbst.cast_save", text="", icon='EXPORT').obj_name = ob.name
        lock = _lock_word(e).strip(" ·") if e is not None else ""
        if lock:
            _dim(col, lock[:1].upper() + lock[1:] + " by the cast library", 'PINNED')
    row = lay.row(align=True)
    row.operator("bbst.turn", text="Turn Left 45°", icon='TRIA_LEFT').deg = 45     # ↺ is "back to the saved beat" only
    row.operator("bbst.turn", text="Turn Right 45°", icon='TRIA_RIGHT').deg = -45


def draw_poses(lay, context):
    """Poses, under the Characters: Stand / Sit / Lie on this beat, and the height it rests at (0.19)."""
    ob = _char_target(context)
    col = lay.column(align=True)
    if ob is None:
        _dim(col, "Click a character to stand, sit or lie it", 'INFO')
        return
    kind = pose_kind(ob) if is_peg(ob) else None
    if kind is None:
        _dim(col, "Old peg: rebuilt on the next sync" if old_peg(ob) else "Not a peg: no joints to pose", 'INFO')
        return
    row = col.row(align=True)
    row.scale_y = 1.2
    for k, label in (('STAND', "Stand"), ('SIT', "Sit"), ('LIE', "Lie")):
        op = row.operator("bbst.pose", text=label, depress=(kind == k))
        op.kind, op.obj_name = k, ob.name
    if kind in ('SIT', 'LIE', 'CUSTOM') and ob.get("bbst_rest", 0.0) > 0.0:
        # this beat's seat or bed (Configure Character holds the usual ones)
        col.prop(ob, "bbst_pose_at",
                 text="Seat height" if kind == 'SIT' else ("Bed height" if kind == 'LIE' else "Rests at"))
    scene = context.scene
    st = scene.bb_st
    n = len(st.beats)
    if n and (st.unsaved_between or any(b.dirty for b in st.beats)):
        # Save right here: Save Beat sat a whole sidebar away from Stand / Sit / Lie (UX review of s5)
        r = col.row(align=True)
        r.scale_y = 1.2
        r.alert = True
        r.operator("bbst.beat_save", text=_save_label(scene, n), icon='STRIP_COLOR_02')
    else:
        _dim(col, "Save Beat keeps the pose, like a move")


def draw_props(lay, context):
    scene = context.scene
    st = scene.bb_st
    props_c = sub_coll(scene, "STAGE", "Props")
    if props_c is None:
        return
    lay.operator("bbst.add_prop", icon='MESH_CUBE')
    if len(props_c.objects):
        lay.template_list("BBST_UL_objects", "props", props_c, "objects", st, "prop_index", rows=2)
    else:
        _dim(lay, "A prop moves and keys on the beats like a character")


def draw_paths(lay, context):
    """Paths: the picked character's or prop's drawn route into the beat (a camera's is in Camera › Camera moves)."""
    owner = _path_owner(context)
    if owner is None:
        _dim(lay, "Click somebody, then a beat from B2 on", 'INFO')
        return
    if owner.type == 'CAMERA':
        _dim(lay, "A camera's path: Camera tab, Camera moves", 'INFO')
        return
    draw_path_box(lay, context)


def draw_natural(lay, context):
    """Natural moves: the switch, and the picked mover's timing into this beat."""
    st = context.scene.bb_st
    lay.prop(st, "natural", text="Move naturally")      # a tick reads as on / off; the panel title says what
    if not st.natural:
        _dim(lay, "Off: everybody moves together")
        return
    _dim(lay, f"Walking pace {st.pace:.1f} m/s (Settings)")
    # Easy has Set by Hand too, as 0.18 had (review of s5: the UI move must not take a control away)
    owner = _path_owner(context)
    if owner is None or len(st.beats) < 2:
        _dim(lay, "Click somebody to time their move", 'INFO')
        return
    if owner.type == 'CAMERA':
        _dim(lay, "A camera's timing: Camera tab, Camera moves", 'INFO')
        return
    draw_move_box(lay, context)


# ---- Camera: Beats (short), Cameras, Camera moves, Cuts

def _cam_row(row, context, ob):
    scene = context.scene
    active = context.view_layer.objects.active == ob and ob.select_get()
    live = scene.camera == ob           # the camera the cuts show on this frame
    # the live one gets the record dot: VIEW_CAMERA and OUTLINER_OB_CAMERA looked the same at sidebar size (UX review)
    op = row.operator("bbst.obj_action", text=ob.name, icon='REC' if live else 'OUTLINER_OB_CAMERA', depress=active)
    op.obj_name, op.action = ob.name, 'SELECT'
    row.operator("bbst.rename", text="", icon='GREASEPENCIL').obj_name = ob.name
    sub = row.row(align=True)
    sub.ui_units_x = 2.3
    sub.prop(ob.data, "bbst_lens_mm", text="")     # whole millimetres, like the pane header
    mm = row.row()
    mm.ui_units_x = 1.3
    mm.label(text="mm")                             # the unit on screen, not only in the tooltip (UX review)
    moves = scene.bb_st.key_cameras or cam_moves(ob)
    op = row.operator("bbst.cam_moves", text="", icon='DECORATE_KEYFRAME' if moves else 'DECORATE_ANIMATE',
                      depress=moves)
    op.cam_name, op.on = ob.name, not moves
    op = row.operator("bbst.obj_action", text="", icon='X')
    op.obj_name = ob.name
    op.action = 'DELETE'


class BBST_UL_cams(bpy.types.UIList):
    """The cameras of a staging. A staging cut into shots can hold dozens: the list scrolls and can be searched."""

    def draw_item(self, context, layout, data, item, icon, active_data, active_prop, index):
        _cam_row(layout.row(align=True), context, item)

    def filter_items(self, context, data, propname):
        obs = getattr(data, propname)
        text = self.filter_name.lower()
        flags = [self.bitflag_filter_item if (o.type == 'CAMERA' and (not text or text in o.name.lower())) else 0 for o in obs]
        order = bpy.types.UI_UL_list.sort_items_by_name(obs, "name") if self.use_filter_sort_alpha else []
        return flags, order


CAM_LIST_FROM = 9           # more cameras than this: the list scrolls


def draw_cams(lay, context):
    """Cameras: Add Camera and the list (name, lens, on the beats or Static, delete)."""
    scene = context.scene
    row = lay.row()
    row.scale_y = 1.2
    row.operator("bbst.cam_add", icon='ADD')
    cams = stage_cams(scene)
    coll = sub_coll(scene, "STAGE", "Cameras")
    if coll is not None and len(cams) >= CAM_LIST_FROM:
        lay.template_list("BBST_UL_cams", "", coll, "objects", scene.bb_st, "cam_index", rows=8)
    else:
        col = lay.column(align=True)
        for ob in cams:
            _cam_row(col.row(align=True), context, ob)
    if cams:
        live = scene.camera if scene.camera in cams else None
        _dim(lay, f"On screen now: {live.name}" if live is not None else "No camera on screen", 'REC')
        _dim(lay, "◆ on the beats · ◇ Static (hover for more)")
    else:
        _dim(lay, "Add one, then frame it in the lower pane", 'INFO')


def _fold_head(lay, idname, closed=True):
    """A folding sub-section whose header row holds the control itself (UX review of s5: each header repeated the
    dropdown inside it). Returns (header row, body column or None while folded)."""
    try:
        header, body = lay.panel(idname, default_closed=closed)
    except Exception:           # a layout without layout panels (a test's stand-in): drawn open
        return lay.row(align=True), lay.column(align=True)
    return header.row(align=True), (body.column(align=True) if body is not None else None)


def draw_cam_moves(lay, context):
    """Camera moves for the picked camera (else the one on screen). Each behaviour is one dropdown showing what it
    does now; the ones with more to set fold open under it. Behaviours that can not go together are greyed with the
    reason. Eyes of shows in Easy too (review of s5: Easy had lost it); a moving camera's timing is here (review of
    s5: it was only in Block)."""
    scene = context.scene
    st = scene.bb_st
    cams = stage_cams(scene)
    cam = context.view_layer.objects.active if context.view_layer else None
    picked = cam is not None and cam.type == 'CAMERA' and cam in cams
    if not picked:
        cam = scene.camera if scene.camera in cams else None      # nothing picked: the one in the preview
    if cam is None:
        _dim(lay, "Add a camera, then click it", 'INFO')
        return
    i = _beat_row(st) if len(st.beats) else None
    row = lay.row(align=True)
    row.label(text=cam.name, icon='OUTLINER_OB_CAMERA')
    sub = row.row()
    sub.enabled = False
    sub.alignment = 'RIGHT'
    sub.label(text="picked" if picked else "on screen")
    has_path = any(r.owner == cam for r in st.paths)
    tgt = ride_target(cam)
    eyes = eyes_target(cam)

    # where it looks, on this beat
    looks = look_at_beat(scene, cam, i) if i is not None else None
    text = "Looks at: nothing (its own rotation)" if looks is None else (
        "Looks at: its aim point" if looks == "" else f"Looks at: {who_label(looks, scene)}")
    head, col = _fold_head(lay, "bbst_cam_look", closed=False)
    r = head.row(align=True)
    r.enabled = i is not None
    op = r.operator_menu_enum("bbst.cam_looks_at", "target", icon='CON_TRACKTO', text=text)
    op.cam_name = cam.name
    if looks is not None and aim_of(cam) is not None:
        op = head.operator("bbst.obj_action", text="", icon='RESTRICT_SELECT_OFF')
        op.obj_name, op.action = aim_of(cam).name, 'SELECT'
    if col is not None:
        if i is None:
            _dim(col, "Add a beat first", 'INFO')
        elif looks is not None and i > 0:
            src = look_source(scene, cam, i)
            _dim(col, "Set here; held until a beat changes it" if src == i else
                 f"From B{src + 1} on; pick another to change it here", 'INFO')
        elif looks is None:
            _dim(col, "Pick somebody: it keeps them in frame", 'INFO')
        else:
            _dim(col, "Held until a beat changes it", 'INFO')

    # where it goes: with somebody, in somebody's eyes, or its own drawn path (one at a time)
    text = f"Travels with: {who_label(tgt, scene)}" if tgt is not None else "Travels with: nobody"
    head, col = _fold_head(lay, "bbst_cam_ride")
    r = head.row(align=True)
    r.enabled = not has_path
    op = r.operator_menu_enum("bbst.cam_ride", "target", icon='CON_FOLLOWPATH', text=text)
    op.cam_name = cam.name
    if col is not None:
        if tgt is not None:
            turns = ride_turns(cam)
            op = col.operator("bbst.cam_ride_turn", depress=turns, icon='ORIENTATION_GIMBAL',
                              text=f"Turns with {who_label(tgt, scene)} too — Snorricam" if turns
                                   else f"Goes where {who_label(tgt, scene)} goes, keeps its own facing")
            op.cam_name, op.on = cam.name, not turns
        if has_path:
            _dim(col, "It has a drawn path: remove it first", 'INFO')
        elif eyes is not None:
            _dim(col, "Picking somebody here leaves the eyes", 'INFO')
        elif tgt is None:
            _dim(col, "Follows them, keeping its distance", 'INFO')

    text = f"Eyes of: {who_label(eyes, scene)}" if eyes is not None else "Eyes of: nobody"
    head, col = _fold_head(lay, "bbst_cam_eyes")
    r = head.row(align=True)
    r.enabled = not has_path
    op = r.operator_menu_enum("bbst.cam_eyes", "target", icon='HIDE_OFF', text=text)
    op.cam_name = cam.name
    if col is not None:
        if eyes is not None and eyes_aims(cam):
            # the old rig, where the eyes carried the aim too: its gaze sliders stay until it is freed
            helper = eyes_helper(cam)
            s2 = col.column(align=True)
            s2.prop(helper, "bbst_gaze_up")
            s2.prop(helper, "bbst_gaze_turn")
            op = s2.operator("bbst.cam_free_aim", icon='UNLOCKED')
            op.cam_name = cam.name
        if eyes is not None:
            uid, _secs = step_off(cam)
            k = beat_index_of(st, uid) if uid else None
            b = st.beats[k] if k is not None else None
            s2 = col.column(align=True)
            op = s2.operator_menu_enum(
                "bbst.cam_step_off", "beat", icon='FORWARD',
                text="Steps off at: " + (f"B{k + 1}" + (f" {b.label}" if b.label else "") if b is not None else "never"))
            op.cam_name = cam.name
            if b is not None:
                s2.prop(cam, "bbst_step_s")
        if has_path:
            _dim(col, "It has a drawn path: remove it first", 'INFO')
        elif tgt is not None:
            _dim(col, "Picking somebody here leaves Travels with", 'INFO')
        elif eyes is None:
            _dim(col, "Sees what they see, from their head", 'INFO')

    mine = [beat_index_of(st, r.beat_uid) for r in st.paths if r.owner == cam]
    text = ("Path: into " + ", ".join(f"B{k + 1}" for k in sorted(x for x in mine if x is not None))) if mine else "Path: none"
    col = _fold(lay, "bbst_cam_path", text, 'CURVE_BEZCURVE')
    if col is not None:
        if tgt is not None or eyes is not None:
            _dim(col, "Set Travels with / Eyes of to nobody first", 'INFO')
        elif not picked:
            _dim(col, "Click the camera to draw its path", 'INFO')
        else:
            draw_path_box(col, context)

    # Natural moves: when a moving camera sets off and lands into this beat (0.18 drew it in Beats)
    if st.natural and picked and len(st.beats) > 1 and i and cam_moves(cam):
        rec = move_rec(scene, cam, st.beats[i].uid)
        col = _fold(lay, "bbst_cam_timing", f"Timing into B{i + 1}: " + ("by hand" if rec is not None else "auto"),
                    'TIME')
        if col is not None:
            draw_move_box(col, context)

    # the lens: one switch, no fold
    zoom = lens_fcurve(cam) is not None
    sub = lay.row(align=True)
    sub.enabled = len(st.beats) > 0
    op = sub.operator("bbst.lens_key", depress=zoom, icon='ZOOM_ALL',
                      text="Zoom: lens set per beat" if zoom else "Zoom: one lens (click to set it per beat)")
    op.cam_name, op.on = cam.name, not zoom
    lay.prop(cam.data, "bbst_handheld", text="Handheld", slider=True, icon='MOD_NOISE')
    if getattr(cam.data, "bbst_handheld", 0.0) > 0:
        _dim(lay, "Handheld takes over the lens shift", 'INFO')
    moves = cam_moves(cam)
    row = lay.row()
    row.scale_y = 1.15
    # the same words as the ◆/◇ on its row (UX review of s5: three names for one switch)
    op = row.operator("bbst.cam_moves", icon='DECORATE_KEYFRAME' if moves else 'DECORATE_ANIMATE',
                      text="On the beats: keyed where it moves" if moves else "Static: left out of the beats")
    op.cam_name, op.on = cam.name, not moves


class BBST_OT_cut_goto(bpy.types.Operator):
    """Go to this cut on the timeline (an unsaved move is saved into its beat first)"""
    bl_idname = "bbst.cut_goto"
    bl_label = "Go to Cut"
    frame: bpy.props.IntProperty(name="Frame")

    def execute(self, context):
        scene = context.scene
        if not is_staging(scene):
            return {'CANCELLED'}
        save_unsaved(scene)         # the jump re-reads the keys: an unsaved move would go
        scene.frame_set(self.frame)
        apply_path_focus(scene)
        settle_unsaved(scene)
        return {'FINISHED'}


def draw_cuts(lay, context):
    """Cuts: cut to a camera at the playhead, and every cut of the staging (Aman, 10 Oct 2026: cuts live on the
    timeline, not on the beats)."""
    scene = context.scene
    if not stage_cams(scene):
        _dim(lay, "Add a camera first", 'INFO')
        return
    cut = cut_at(scene, scene.frame_current)
    row = lay.row(align=True)
    row.scale_y = 1.2
    row.operator_menu_enum("bbst.cut_here", "cam", icon='MARKER_HLT',
                           text=f"Cut here: {cut.camera.name}" if (cut is not None and cut.camera) else "Cut to a camera here")
    sub = row.row(align=True)
    sub.enabled = cut is not None
    sub.operator("bbst.cut_remove", text="", icon='X')
    marks = sorted(cut_markers(scene), key=lambda m: m.frame)
    if marks:
        col = lay.column(align=True)
        f = fps(scene)
        for m in marks:
            r = col.split(factor=0.5, align=True)
            here = m.frame == scene.frame_current
            op = r.operator("bbst.cut_goto", text=f"{(m.frame - scene.frame_start) / f:.1f} s · f {m.frame}",
                            icon='PLAY' if here else 'MARKER', depress=here)
            op.frame = m.frame
            r.label(text=m.camera.name, icon='VIEW_CAMERA')
    else:
        _dim(lay, "No cuts: the preview stays on one camera", 'INFO')
    _dim(lay, "Ctrl+B in the timeline cuts too")


# ---- Studio (Artist): Studio space, Kit & stand-ins, Floors & levels

def draw_studio(lay, context):
    st = context.scene.bb_st
    r = lay.row()
    r.scale_y = 1.3
    r.alert = st.needs_place
    r.operator("bbst.place_space", icon='OBJECT_ORIGIN')
    if st.needs_place:
        _dim(lay, "Then drag it to where the scene plays", 'INFO')
    col = lay.column(align=True)
    col.label(text="Size (m):")
    col.prop(st, "studio_w")
    col.prop(st, "studio_d")
    col.prop(st, "studio_h")
    col = lay.column(align=True)
    col.label(text="Floor & back walls:")       # 0.19.1: the walls you place are in Walls & doors, below
    col.prop(st, "wall_count", text="Back walls")
    col.prop(st, "wall_width")
    col.prop(st, "wall_height")
    col.operator("bbst.rebuild_shell", icon='FILE_REFRESH')
    outside = chars_outside_studio(context.scene)
    if outside:
        names = [who_label(bpy.data.objects.get(n), context.scene) or n for n in outside[:4]]
        lay.label(text="Outside the studio: " + ", ".join(names), icon='ERROR')


def draw_kit(lay, context):
    col = lay.column(align=True)
    col.label(text="Add to the studio:")
    grid = col.grid_flow(columns=3, align=True)
    for key, (label, *_rest) in KIT_PIECES.items():
        grid.operator("bbst.add_kit", text=label).piece = key
    col = lay.column(align=True)
    col.scale_y = 1.2
    col.operator("bbst.pick_standin", text="Grey Box from Set Object", icon='EYEDROPPER')
    col.operator("bbst.pick_match", text="Match Piece to Set Object", icon='SNAP_FACE')
    op = col.operator("bbst.add_prop", text="Placeholder Stand-in Prop", icon='GHOST_ENABLED')
    op.standin = True
    _dim(lay, "A placeholder is banned from every output")


def draw_levels(lay, context):
    scene = context.scene
    st = scene.bb_st
    ff = floor_state(scene)
    col = lay.column(align=True)
    col.prop(st, "use_floors", text="Floors (levels and plan cut)", toggle=True, icon='CON_FLOOR')
    if not st.use_floors:
        _dim(lay, "Off: the studio moves freely", 'INFO')
        return
    col.label(text="Plan cuts of the set's floors:")
    if ff is not None:
        col.prop(ff, "level1_cut", text="Ground floor plan cut (m)")
        col.prop(ff, "ceiling_cut", text="Upper floor plan cut (m)")
        col.prop(ff, "has_upper")
    col.operator("bbst.detect_floors", icon='VIEWZOOM')
    col = lay.column(align=True)
    col.prop(st, "play_level")
    col.prop(st, "floor_z")
    _dim(lay, "Plays on: where the studio stands")


# ---- Output (Artist): Outputs, Captions

class BBST_MT_playblast(bpy.types.Menu):
    """Playblast one camera of this staging"""
    bl_idname = "BBST_MT_playblast"
    bl_label = "Playblast a Camera"

    def draw(self, context):
        scene = context.scene
        for cam in stage_cams(scene):
            self.layout.operator("bbst.playblast", text=cam.name,
                                 icon='VIEW_CAMERA' if cam == scene.camera else 'OUTLINER_OB_CAMERA').cam_name = cam.name


def draw_outputs(lay, context):
    scene = context.scene
    col = lay.column(align=True)
    col.scale_y = 1.2
    sub = col.row(align=True)
    sub.enabled = bool(stage_cams(scene))
    sub.menu("BBST_MT_playblast", text="Playblast a Camera", icon='RENDER_ANIMATION')
    if any(mk.camera for mk in scene.timeline_markers):
        op = col.operator("bbst.playblast", text="Playblast the Edit (camera cuts)", icon='SEQUENCE')
        op.cam_name = ""
        op.use_cuts = True
    col = lay.column(align=True)
    col.operator("bbst.export_pack", icon='EXPORT')
    col.operator("bbst.top_map", icon='AXIS_TOP')
    _dim(lay, "Saved in Stage/ next to the .blend")


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


# ---- the panel classes

class _NPanel:
    bl_space_type = 'VIEW_3D'
    bl_region_type = 'UI'
    bl_category = "BB Stage"


class BBST_PT_entry(_NPanel, bpy.types.Panel):
    """Outside Stage Mode the sidebar shows only the way in, like BB Set Viewer."""
    bl_label = "BB Stage"
    bl_order = 0

    @classmethod
    def poll(cls, context):
        return not _in_stage(context)

    def draw(self, context):
        col = self.layout.column(align=True)
        col.scale_y = 1.5
        if fstate() is None:
            return
        if stagings():
            col.operator("bbst.enter_stage", text="Enter Artist Mode", icon='FULLSCREEN_ENTER').easy = False
            col.operator("bbst.enter_stage", text="Enter Easy Mode", icon='VIEW_CAMERA').easy = True
        col.operator("bbst.new_staging", text="New Staging…", icon='ADD')


class BBST_PT_header(_NPanel, bpy.types.Panel):
    """Stage Mode's sidebar header: the staging, its menu, the Switchboard, Settings and the mode tabs."""
    bl_label = "BB Stage"
    bl_order = 0
    bl_options = {'HIDE_HEADER'}

    @classmethod
    def poll(cls, context):
        return _in_stage(context)

    def draw(self, context):
        draw_stage_header(self.layout, context)


def draw_module(lay, context, m):
    """A module's panel: its controls, or, switched off while the staging uses it, a line saying so."""
    scene = context.scene
    if not feature_on(scene, m.id):
        col = lay.column(align=True)
        _dim(col, "Hidden, but this staging uses it", 'INFO')
        op = col.operator("bbst.feature_set", text=f"Show {m.label}", icon='HIDE_OFF')
        op.module, op.on = m.id, True
        return
    fn = globals().get(m.draw)
    if fn is None:
        return
    if cur_tab(context) in m.compact:
        fn(lay, context, compact=True)
    else:
        fn(lay, context)


def _module_panel(m, order):
    """One sidebar panel for one module of MODULES."""
    def poll(cls, context):
        try:
            return module_shown(context, MODULE_BY_ID[cls.bbst_module])
        except Exception:
            return False

    def draw(self, context):
        draw_module(self.layout, context, MODULE_BY_ID[self.bbst_module])

    def draw_header_preset(self, context):
        if not feature_on(context.scene, self.bbst_module):
            r = self.layout.row()
            r.enabled = False
            r.label(text="hidden", icon='HIDE_ON')

    ns = dict(bl_idname=f"BBST_PT_mod_{m.id}", bl_label=m.label, bl_order=order, bbst_module=m.id,
              poll=classmethod(poll), draw=draw, draw_header_preset=draw_header_preset, __doc__=m.what,
              __module__=__name__)
    if m.parent:
        ns["bl_parent_id"] = f"BBST_PT_mod_{m.parent}"
    return type(f"BBST_PT_mod_{m.id}", (_NPanel, bpy.types.Panel), ns)


MODULE_PANELS = [_module_panel(m, k + 1) for k, m in enumerate(MODULES)]


# ------------------------------------------------------------------ handlers

@persistent
def _bbst_on_load(*_args):
    _TOUCHED.clear()            # another file: its stagings may carry the same names
    _WATCH.clear()
    _LAST_STG.clear()
    _SYNC["pending"] = False
    _BUILD_STATE["active"] = False
    _SET_GUARD.update(scene="", snap={}, msg="", names=set(), strays=set(), left=None)     # Edit Set's guard belongs to the file it was switched on in
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
        if m and tuple(int(g) for g in m.groups()) < VERSION:
            t.use_module = False       # never runs again, and saves no longer carry it as a script
            stale = True
    live = getattr(getattr(getattr(bpy.types, "BBST_OT_enter_stage", None), "execute", None), "__code__", None)
    foreign = live is not None and live.co_filename != BBST_OT_enter_stage.execute.__code__.co_filename
    return stale or foreign


def _reclaim():
    """Register this copy again: unregister the classes another copy put under our names
    (register() alone fails on them), then ours, then register."""
    ours = {c.__name__: c for c in CLASSES}
    for base in (bpy.types.Operator, bpy.types.Panel, bpy.types.UIList, bpy.types.PropertyGroup, bpy.types.Menu):
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
            print("BB Stage: an older embedded copy took over on load; registering", VERSION)
            _reclaim()          # takes the classes back; register() schedules this again
            return None
        _ensure_handlers()
        release_camera_locks()              # a file saved without save_pre (an autosave) may carry the people lock
        for s in stagings():
            try:
                migrate_staging(s)
                forget_unsaved(s)              # loading read the keys over whatever the file held: no move is left
            except Exception as e:             # one staging that fails to upgrade must not stop the others
                print("BB Stage after load:", s.name, e)
            if s.bb_st.stage_mode:
                s.bb_st.stage_mode = False     # v0.7 stored Stage Mode per scene
        cast_sync_from_library(force=True)     # locked cast characters follow the library (0.19)
        for s in stagings():
            try:
                refresh_set_edits(s)        # set edits, structural: a load starts a fresh undo history
            except Exception as e:          # never stops the rest of the load (Stage Mode windows below)
                print("BB Stage set edits after load:", s.name, e)
        free_local_collection_slots()
        _cleanup_legacy_panel_hides()
        if stage_windows():
            for w in stage_windows():
                _WATCH.pop(w.as_pointer(), None)
                engage(w, w.scene)
        else:
            untint_everything()
            _restore_foreign_v3d_panels()
        for w in bpy.context.window_manager.windows:
            s = w.scene
            if s is not None and is_staging(s) and BETWEEN_KEY in s:
                try:
                    w.view_layer.update()      # the keys are read first; the move kept by the save goes on top
                    unstash_between(s)
                except Exception as e:
                    print("BB Stage move between beats:", s.name, e)
    except Exception as e:
        print("BB Stage after load:", e)
    return None


@persistent
def _bbst_save_pre(*_args):
    # Ctrl+S with an orange beat: the move goes into its beat first. The file would hold the object off its keys,
    # and opening it reads the keys over it — the move was lost and the badge stayed orange (audit r1 bug 5)
    for s in stagings():
        try:
            save_unsaved(s)
            stash_between(s)            # a move between two beats goes into the file as it stands
        except Exception as e:
            print("BB Stage save unsaved beat:", s.name, e)
    untint_everything()        # the set is saved with its own colours, never the ghost tint
    for s in stagings():
        try:
            apply_studio_lock(s, False)     # files open clickable without the add-on; the sync re-locks
        except Exception:
            pass
    release_camera_locks()          # Camera mode's people lock, likewise (0.19): save_post's sync puts it back


@persistent
def _bbst_save_post(*_args):
    if stage_on():
        request_sync(0.05)


@persistent
def _bbst_undo(*_args):
    # no _WATCH.clear(): that made every undo rebuild the screen and reset the plan view; the
    # watchdog still notices scene/pane changes, and the sync re-applies visibility
    _TOUCHED.clear()            # the undo brought back another state: the badges are worked out again
    if not bpy.app.timers.is_registered(_bbst_settle_dirty):
        bpy.app.timers.register(_bbst_settle_dirty, first_interval=0.0)
    try:
        if setedit_wrappers():          # set edits: records and exclusions true to the undone state (flags only)
            for s in stagings():
                refresh_set_edits(s, adopt=False, structural=False)
    except Exception as e:
        print("BB Stage set edits after undo:", e)
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


# ------------------------------------------------------------------ camera labels in the plan
#
# Aman, 5 Oct 2026: "put names on the cameras... it is hard to understand which camera we are
# playing with". Blender's own name text is dim and vanishes with the camera above the plan
# cut, so the plan draws its own tag: name, which camera pane shows it, a dot where it stands
# and a tick where it looks — at any height.

_CAM_DRAW_KEY = "bbst_cam_labels"


def _draw_cam_labels():
    ctx = bpy.context
    try:
        win, area, region, rv3d = ctx.window, ctx.area, ctx.region, ctx.region_data
        if win is None or area is None or region is None or rv3d is None or not _in_stage(ctx):
            return
        roles = stage_panes(win)
        if roles.get("WORK") != area:
            return
        scene = ctx.scene
        cams = stage_cams(scene)
        if not cams:
            return
        import blf
        import gpu
        from gpu_extras.batch import batch_for_shader
        from bpy_extras.view3d_utils import location_3d_to_region_2d
        shown = {}
        for role in sorted(r for r in roles if r.startswith("CAM")):
            sp = roles[role].spaces.active
            # the camera the pane really shows: the top pane is the preview and follows the cuts, so its tag
            # sat on the first camera ever added whatever the cut was (audits r5 B2, r6 B11)
            cam = sp.camera if (sp.use_local_camera and sp.camera is not None) else (
                scene.camera if role == "CAM0" else pane_camera(scene, role))
            if cam is not None:
                shown.setdefault(cam.name, []).append("top pane" if role == "CAM0" else "bottom pane")
        ui = ctx.preferences.view.ui_scale * ctx.preferences.system.pixel_size
        font = 0
        blf.size(font, 11 * ui)
        shader = gpu.shader.from_builtin('UNIFORM_COLOR')
        gpu.state.blend_set('ALPHA')
        amber = (1.0, 0.72, 0.15, 1.0)
        # a staging cut into shots holds a camera per shot: name only the one on screen now, the ones the panes
        # show and the selected ones, the rest keep their dot and arrow (forty name tags on one spot hide the plan)
        many = len(cams) > CAM_LIST_FROM
        named = {scene.camera.name if scene.camera is not None else ""} | set(shown)
        named |= {o.name for o in cams if o.select_get()}
        for cam in cams:
            if cam.hide_get() or cam.hide_viewport:
                continue
            mw = cam.matrix_world
            p = location_3d_to_region_2d(region, rv3d, mw.translation)
            if p is None:
                continue
            fwd = mw.to_3x3() @ Vector((0.0, 0.0, -1.0))
            q = location_3d_to_region_2d(region, rv3d, mw.translation + Vector((fwd.x, fwd.y, 0.0)).normalized()
                                         if Vector((fwd.x, fwd.y)).length > 1e-4 else mw.translation)
            r = 4 * ui
            dot = [(p.x - r, p.y - r), (p.x + r, p.y - r), (p.x + r, p.y + r),
                   (p.x - r, p.y - r), (p.x + r, p.y + r), (p.x - r, p.y + r)]
            shader.uniform_float("color", amber)
            batch_for_shader(shader, 'TRIS', {"pos": dot}).draw(shader)
            if q is not None and (q - p).length > 1:      # an arrowhead where it looks
                d = (q - p).normalized()
                n = Vector((-d.y, d.x))
                tip, base = p + d * 26 * ui, p + d * 12 * ui
                arrow = [(tip.x, tip.y), (base.x + n.x * 6 * ui, base.y + n.y * 6 * ui),
                         (base.x - n.x * 6 * ui, base.y - n.y * 6 * ui)]
                batch_for_shader(shader, 'TRIS', {"pos": arrow}).draw(shader)
            if many and cam.name not in named:
                continue
            text = cam.name + (f"  · {' + '.join(shown[cam.name])}" if cam.name in shown else "")
            if cam_moves(cam) and cam_travels(cam):     # 0.18 keys every camera: tag the ones that really move
                text += "  · moves"
            if eyes_target(cam) is not None:
                text += f"  · eyes of {who_label(eyes_target(cam), scene)}"
            if ride_target(cam) is not None:
                text += f"  · with {who_label(ride_target(cam), scene)}"
            w, h = blf.dimensions(font, text)
            x, y = p.x + 9 * ui, p.y + 7 * ui
            pad = 4 * ui
            box = [(x - pad, y - pad), (x + w + pad, y - pad), (x + w + pad, y + h + pad),
                   (x - pad, y - pad), (x + w + pad, y + h + pad), (x - pad, y + h + pad)]
            shader.uniform_float("color", (0.06, 0.06, 0.07, 0.78))
            batch_for_shader(shader, 'TRIS', {"pos": box}).draw(shader)
            blf.color(font, *amber)
            blf.position(font, x, y, 0)
            blf.draw(font, text)
        gpu.state.blend_set('NONE')
    except Exception as e:
        if not _SYNC.get("label_error"):
            _SYNC["label_error"] = True
            print("BB Stage camera labels:", e)


_DRAW_HANDLES = []      # kept here as well: bpy.app.driver_namespace is emptied by every file load


def _add_cam_labels():
    _remove_cam_labels()
    ns = bpy.app.driver_namespace
    ns[_CAM_DRAW_KEY] = bpy.types.SpaceView3D.draw_handler_add(_draw_cam_labels, (), 'WINDOW', 'POST_PIXEL')
    ns[_CAPTION_DRAW_KEY] = bpy.types.SpaceView3D.draw_handler_add(_draw_captions, (), 'WINDOW', 'POST_PIXEL')
    _DRAW_HANDLES[:] = [ns[_CAM_DRAW_KEY], ns[_CAPTION_DRAW_KEY]]


def _remove_cam_labels():
    handles = list(_DRAW_HANDLES)
    for key in (_CAM_DRAW_KEY, _CAPTION_DRAW_KEY):
        h = bpy.app.driver_namespace.get(key)
        if h is not None and not any(h is x for x in handles):
            handles.append(h)
        bpy.app.driver_namespace[key] = None
    for h in handles:
        try:
            bpy.types.SpaceView3D.draw_handler_remove(h, 'WINDOW')
        except (ValueError, RuntimeError):
            pass
    _DRAW_HANDLES.clear()


# ------------------------------------------------------------------ captions in the preview pane
#
# Aman, 11 Oct 2026: the preview pane says what the shot is about, like a subtitle, so a long edit reads
# without the panel. The text is the beat's label and note. Drawn on screen only: playblasts stay clean.

_CAPTION_DRAW_KEY = "bbst_captions"


def caption_beat(scene, frame=None):
    """The beat a frame belongs to: the one being moved into or held (a move belongs to the beat it ends on)."""
    st = scene.bb_st
    n = len(st.beats)
    if not n:
        return None
    f = scene.frame_current if frame is None else frame
    for i, b in enumerate(st.beats):
        if f <= beat_out(b) + 0.5:
            return i
    return n - 1


def _wrap_text(font, text, width, max_lines=6):
    import blf
    lines, cur = [], ""
    for word in text.split():
        trial = (cur + " " + word).strip()
        if cur and blf.dimensions(font, trial)[0] > width:
            lines.append(cur)
            cur = word
        else:
            cur = trial
    if cur:
        lines.append(cur)
    if len(lines) > max_lines:
        lines = lines[:max_lines]
        lines[-1] = lines[-1].rstrip(" .,;") + " …"
    return lines


def _draw_captions():
    ctx = bpy.context
    try:
        win, area, region, rv3d = ctx.window, ctx.area, ctx.region, ctx.region_data
        if win is None or area is None or region is None or rv3d is None or not _in_stage(ctx):
            return
        if stage_panes(win).get("CAM0") != area:
            return
        scene = ctx.scene
        st = scene.bb_st
        if not st.show_captions:
            return
        i = caption_beat(scene)
        if i is None:
            return
        b = st.beats[i]
        title = f"B{i + 1}  {b.label}".strip()
        note = " ".join(b.note.split())
        import blf
        import gpu
        from gpu_extras.batch import batch_for_shader
        from bpy_extras.view3d_utils import location_3d_to_region_2d
        # the camera frame inside the pane: the caption sits on its bottom edge, like a subtitle
        x0, x1, y0 = 0.0, float(region.width), 0.0
        sp = area.spaces.active
        cam = sp.camera if sp.use_local_camera else scene.camera
        if rv3d.view_perspective == 'CAMERA' and cam is not None and cam.type == 'CAMERA':
            pts = [location_3d_to_region_2d(region, rv3d, cam.matrix_world @ v) for v in cam.data.view_frame(scene=scene)]
            if all(p is not None for p in pts):
                x0 = max(x0, min(p.x for p in pts))
                x1 = min(x1, max(p.x for p in pts))
                y0 = max(y0, min(p.y for p in pts))
        if x1 - x0 < 120:
            return
        ui = ctx.preferences.view.ui_scale * ctx.preferences.system.pixel_size
        font = 0
        # sized like a subtitle, as a share of the camera frame's width (Aman, 15 Oct 2026: "make the caption
        # text bigger"); it was a fixed 13-14 px, too small to read the longer notes on a big preview pane
        n_size = min(32 * ui, max(16 * ui, (x1 - x0) * 0.024))
        t_size = n_size * 1.08
        pad = n_size * 0.75
        blf.size(font, n_size)
        lines = _wrap_text(font, note, (x1 - x0) - 2 * pad, max_lines=5) if note else []
        line_h = n_size * 1.35
        height = pad * 0.8 + t_size * 1.25 + len(lines) * line_h + pad * 0.7
        shader = gpu.shader.from_builtin('UNIFORM_COLOR')
        gpu.state.blend_set('ALPHA')
        box = [(x0, y0), (x1, y0), (x1, y0 + height), (x0, y0), (x1, y0 + height), (x0, y0 + height)]
        shader.uniform_float("color", (0.03, 0.03, 0.04, 0.66))
        batch_for_shader(shader, 'TRIS', {"pos": box}).draw(shader)
        y = y0 + height - pad * 0.8 - t_size
        blf.size(font, t_size)
        blf.color(font, 1.0, 0.72, 0.15, 1.0)
        blf.position(font, x0 + pad, y, 0)
        blf.draw(font, title)
        blf.size(font, n_size)
        blf.color(font, 0.96, 0.96, 0.96, 1.0)
        for ln in lines:
            y -= line_h
            blf.position(font, x0 + pad, y, 0)
            blf.draw(font, ln)
        gpu.state.blend_set('NONE')
    except Exception as e:
        if not _SYNC.get("caption_error"):
            _SYNC["caption_error"] = True
            print("BB Stage captions:", e)


# ------------------------------------------------------------------ register

PANEL_CLASSES = [BBST_PT_entry, BBST_PT_header] + MODULE_PANELS

CLASSES = [
    BBST_Beat, BBST_Path, BBST_Move, BBST_Cast, BBST_SetEdit, BBST_Features, BBST_Props,
    BBST_OT_stage_tab, BBST_OT_switchboard, BBST_OT_feature_set, BBST_OT_features_default, BBST_OT_settings,
    BBST_OT_cut_goto, BBST_MT_stagings, BBST_MT_staging_more, BBST_MT_staging_plays_in, BBST_MT_staging_delete,
    BBST_MT_beat_more, BBST_MT_playblast,
    BBST_OT_pose, BBST_OT_char_config, BBST_OT_cast_save, BBST_OT_cast_revert, BBST_OT_cast_lock, BBST_OT_cast_link,
    BBST_OT_set_take, BBST_OT_set_reset, BBST_OT_edit_set, BBST_OT_set_repair, BBST_OT_duplicate,
    BBST_OT_move_timing, BBST_OT_cam_ride, BBST_OT_cam_eyes, BBST_OT_cam_step_off, BBST_OT_lens_key,
    BBST_OT_cam_looks_at, BBST_OT_cam_free_aim, BBST_OT_cam_ride_turn,
    BBST_OT_new_staging, BBST_OT_staging_set, BBST_OT_goto_scene, BBST_OT_delete_staging,
    BBST_OT_split_beats, BBST_OT_duplicate_staging, BBST_OT_make_independent,
    BBST_OT_add_kit, BBST_OT_add_wall, BBST_OT_contact_prop, BBST_OT_contact_drop,
    BBST_OT_pick_standin, BBST_OT_pick_match,
    BBST_OT_add_char, BBST_OT_add_prop, BBST_OT_obj_action, BBST_UL_objects, BBST_OT_turn,
    BBST_OT_beat_add, BBST_OT_beat_save, BBST_OT_beat_goto, BBST_OT_beat_delete,
    BBST_OT_play, BBST_OT_from_start, BBST_OT_step_beat,
    BBST_OT_fit_range, BBST_UL_beats, BBST_UL_cams,
    BBST_OT_cam_add, BBST_OT_cam_moves, BBST_OT_rename, BBST_OT_cam_look, BBST_OT_cam_bind,
    BBST_OT_cut_here, BBST_OT_cut_remove, BBST_OT_beat_insert, BBST_OT_reset_moves,
    BBST_OT_pane_world, BBST_OT_pane_view, BBST_OT_pane_cam, BBST_OT_pane_lens,
    BBST_OT_lens_step, BBST_OT_pane_shading, BBST_OT_pan, BBST_OT_block, BBST_OT_block_easy,
    BBST_OT_mark_ceilings, BBST_OT_detect_floors, BBST_OT_fix_screen, BBST_OT_rebuild_shell,
    BBST_OT_pane_cam_pick, BBST_OT_pane_level,
    BBST_OT_enter_stage, BBST_OT_exit_stage, BBST_OT_place_space, BBST_OT_walk,
    BBST_OT_playblast, BBST_OT_export_pack, BBST_OT_top_map,
    BBST_OT_studio_resize, BBST_GT_turn, BBST_GGT_handles,
    BBST_OT_path_add, BBST_OT_path_edit, BBST_OT_path_done, BBST_OT_path_point,
    BBST_OT_path_reset, BBST_OT_path_remove,
] + PANEL_CLASSES

PROP_CLONES = []

_HANDLERS = (("load_post", "_bbst_on_load"), ("save_pre", "_bbst_save_pre"),
             ("save_post", "_bbst_save_post"), ("undo_post", "_bbst_undo"),
             ("redo_post", "_bbst_undo"), ("depsgraph_update_post", "_bbst_on_depsgraph"),
             ("frame_change_post", "_bbst_on_frame"))
_TIMERS_KEY = "bbst_timers"


def _ensure_handlers():
    """Every handler of this module registered once. They are @persistent, so File > Open keeps them; this puts
    back one that something else removed (an older copy's unregister, a script). Only the registered copy does it:
    a load timer left over from a hot-reloaded copy must not swap its handlers back in."""
    if getattr(bpy.types, "BBST_OT_enter_stage", None) is not BBST_OT_enter_stage:
        return
    for lst_name, fn_name in _HANDLERS:
        lst = getattr(bpy.app.handlers, lst_name)
        fn = globals()[fn_name]
        if not any(h is fn for h in lst):
            for h in [h for h in lst if getattr(h, "__name__", "") == fn_name]:
                lst.remove(h)
            lst.append(fn)


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
    km = kc.keymaps.new(name="Object Mode", space_type='EMPTY')
    km.keymap_items.new("bbst.duplicate", 'D', 'PRESS', shift=True)     # taken set pieces copied whole (0.19)
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
    own = [globals().get("_bbst_watchdog"), globals().get("_bbst_settle_dirty")]   # the watchdog lives as long as the add-on
    for f in list(ns.get(_TIMERS_KEY, [])) + [f for f in own if f is not None]:      # the namespace is emptied by a file load
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
            try:
                bpy.utils.unregister_class(cls)
            except Exception:
                bpy.utils.unregister_class(getattr(bpy.types, cls.__name__))
            bpy.utils.register_class(cls)
    bpy.types.Scene.bb_st = bpy.props.PointerProperty(type=BBST_Props)
    bpy.types.WorkSpace.bbst_tab = bpy.props.EnumProperty(     # the sidebar's mode tab: UI state, never undone
        name="Mode", items=[(k, l, d, i, n) for n, (k, l, d, i) in enumerate(TABS)], default='BLOCK')
    bpy.types.Camera.bbst_lens_mm = bpy.props.IntProperty(
        name="Lens (mm)", min=8, max=300, description="Focal length in whole millimetres",
        get=lambda s: int(round(s.lens)), set=_lens_mm_set,
        options=set())          # never keyed itself: its setter writes the beat keys (0.19, audit r2 L6)
    bpy.types.Object.bbst_step_s = bpy.props.FloatProperty(
        name="Step-off time (s)", min=0.1, max=6.0, step=10, precision=1,
        get=lambda s: step_off(s)[1], set=_step_s_set, options=set(),
        description="How long the camera takes to let go of the eyes once it steps off. Short is a snap "
                    "away from him, long is a slow drift off his gaze")
    bpy.types.Object.bbst_gaze_up = bpy.props.FloatProperty(
        name="Gaze up/down", subtype='ANGLE', min=-math.radians(85), max=math.radians(85),
        get=_gaze_get(0, math.pi / 2), set=_gaze_setter(0, math.pi / 2),
        description="Where this character looks on this beat, up or down from level — Save Beat keeps it")
    bpy.types.Object.bbst_gaze_turn = bpy.props.FloatProperty(
        name="Gaze left/right", subtype='ANGLE', min=-math.radians(120), max=math.radians(120),
        get=_gaze_get(2, 0.0), set=_gaze_setter(2, 0.0),
        description="How far he turns his head from straight ahead on this beat, left or right — Save Beat keeps it")
    bpy.types.Camera.bbst_handheld = bpy.props.FloatProperty(
        name="Handheld", default=0.0, min=0.0, max=3.0, step=10, precision=1, update=_handheld_update,
        description="A hand-held camera: the frame drifts slowly with a little tremor on top, the same amount "
                    "in the picture at any lens. 0 is locked off, 1 a steady hand, 2 and up reactive")
    for attr, kw in _OBJECT_PROPS_019():
        setattr(bpy.types.Object, attr, bpy.props.FloatProperty(**kw))
    for attr, kind, kw in _OBJECT_PROPS_0191():
        setattr(bpy.types.Object, attr, getattr(bpy.props, kind)(**kw))
    _take_over_headers()
    _remove_named_handlers()
    for lst_name, fn_name in _HANDLERS:
        getattr(bpy.app.handlers, lst_name).append(globals()[fn_name])
    _remove_keymaps()
    _add_keymaps()
    _stop_timers()
    _add_cam_labels()
    bpy.app.timers.register(_bbst_watchdog, first_interval=1.0, persistent=True)
    bpy.app.driver_namespace[_TIMERS_KEY] = [_bbst_watchdog]
    bpy.app.timers.register(_bbst_after_load, first_interval=0.5)


def unregister():
    _stop_timers()
    _remove_cam_labels()
    _remove_keymaps()
    _remove_named_handlers()
    _release_headers()
    _restore_foreign_v3d_panels()
    try:
        untint_everything()
        release_camera_locks()
    except Exception:
        pass
    for cls in reversed(CLASSES):
        try:
            bpy.utils.unregister_class(cls)
        except RuntimeError:
            pass
    if hasattr(bpy.types.Scene, "bb_st"):
        del bpy.types.Scene.bb_st
    if hasattr(bpy.types.WorkSpace, "bbst_tab"):
        del bpy.types.WorkSpace.bbst_tab
    if hasattr(bpy.types.Camera, "bbst_lens_mm"):
        del bpy.types.Camera.bbst_lens_mm
    if hasattr(bpy.types.Camera, "bbst_handheld"):
        del bpy.types.Camera.bbst_handheld
    for name in ("bbst_step_s", "bbst_gaze_up", "bbst_gaze_turn"):     # left registered before 0.19 (fuzz F)
        if hasattr(bpy.types.Object, name):
            delattr(bpy.types.Object, name)
    for attr, _kw in _OBJECT_PROPS_019():
        if hasattr(bpy.types.Object, attr):
            delattr(bpy.types.Object, attr)
    for attr, _kind, _kw in _OBJECT_PROPS_0191():
        if hasattr(bpy.types.Object, attr):
            delattr(bpy.types.Object, attr)


if __name__ == "__main__":
    try:
        unregister()
    except Exception:
        pass
    register()
