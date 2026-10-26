# SPDX-License-Identifier: GPL-2.0-or-later
"""BB Lighting - light a Beta Builder set by hand, then save what you did.

A lighting state here is not a collection you switch between. It is a RECORDING of every light
in the rig exactly as you left it: on or off, where it points, its energy, colour, temperature,
size and shadow settings, plus the world and the white balance. You move lights around until the set looks right, you
press Save, you name it, and from then on one click puts the set back into that exact condition.

That is the difference from the collection switching in BB Set Viewer, which this replaces. A
collection can only answer "which lights exist"; a recording answers "what were they all doing".
Two states can share every light and differ only in colour temperature, which is what a day and
an evening pass of the same room actually are.

Lighting Mode locks the set so nothing but the lights can be clicked. It is deliberately not
the BB Set Viewer kiosk: there the whole scene is locked and you cannot touch anything, which is
right for framing a shot and useless for lighting one.

Where it is kept: a Text datablock called "BB Lighting States", as readable JSON. It travels
with the .blend, it can be read and edited by hand in the Text Editor, and it can be diffed.

Glowing materials are part of a state too: a garland that glows at night and not by day, a tube
whose glass lights up only when the tube is on. A material is recorded once it is "tracked": any
material that is glowing when you save a state is tracked from then on, and "Track Emission of
Selected" tracks the materials of the selected objects even while they are dark. What a state
records for a tracked material is every glow value you can type into it: the Emission Color and
Emission Strength of each Principled BSDF, the Color, Strength and mute of each Emission node, and
the glow-like inputs (emission, strength, intensity, glow ...) of node groups placed in it. A value
fed by a link (a texture, a driver node) is the link's business and is not recorded. A material
shared by several objects switches on all of them - give an object its own material if only it
should change.

v0.4.0 (26 Oct 2026): (1) 0.3.0's "looks" are now called set dressing: a collection named
     "DRESSING · Wedding" holds the props that exist only in that state (Aman: the universal part
     is a collection of the props a state needs; Wedding itself belongs to Jai's House alone).
     (2) A file that links its set and lights from another file - a staging file - uses that
     file's states: the "BB Lighting States" text is linked from it, read-only here (change the
     states in the set file), and a state's world is linked on demand. Applying a state there
     changes the linked lights and glows for this session only (they are not stored in this
     file), so each scene remembers its state and it is put back on open and whenever another
     scene comes on screen.
v0.3.0 (26 Oct 2026): looks - things that exist only in some states. A collection named
     "LOOK · Wedding" is switched on when the Wedding state is applied and off (outliner checkbox,
     so it is not drawn, rendered or evaluated) for every other state; "LOOK · Wedding, Party"
     belongs to both. Nothing is recorded - the name is the rule, so a look keeps working through
     Save and Update and can be made by hand. "Put Selected in <state> Look" moves the selection
     into the active state's look; renaming a state renames its looks.
v0.2.5 (21 Oct 2026): Rename works. The dialog showed the state's own name as an editable field
     above New name; typing into that first field cancelled silently. It now shows one field,
     ready to type into, and says when a rename cannot happen.
v0.2.4 (21 Oct 2026): a state records the scene's colour temperature too - the White Balance of
     Render Properties > Color Management (on/off, Temperature, Tint) - and applying it puts that
     back, so a day and a night state can differ in white balance alone. The panel shows the three
     controls under "Colour temperature". States saved before 0.2.4 hold no white balance: they
     leave it as it is and the panel lists them until you apply, set and Update them.
v0.2.3 (20 Oct 2026): glowing materials inside collection instances count too - a facade
     placed as an instance, a house brought in as one empty. Selecting an instance and pressing
     Track tracks what it shows; Select picks the instances that show tracked materials.
v0.2.2 (19 Oct 2026): states record and apply the glow of tracked materials (see above). Old
     states keep working: a state saved before 0.2.2 holds no materials and leaves them alone,
     and the panel says which states have not recorded which tracked materials yet.
v0.2.1 (19 Oct 2026): every world a state names gets a fake user, and keeps it. Blender drops a
     datablock with no users on save, and a night world has no users the moment the scene is
     on the day one - the Cloudy night sky world and its packed HDRI vanished from Jai's file
     on the first save after Day was applied.
v0.2 (18 Oct 2026): a state records WHICH world the scene is on, not just the dials inside it,
     so a day HDRI and a night HDRI are two states and applying one switches scene.world. A
     recorded world that is missing from the file is reported instead of silently leaving the
     wrong sky up. Also: the state rows no longer overlap in a narrow sidebar - the three
     action buttons sat at scale_x 0.6, under their own icon width.
v0.1 (17 Oct 2026): first version - record, apply, update, rename, delete; Lighting Mode.
"""

import json

import bpy
from bpy.app.handlers import persistent
from bpy.props import BoolProperty, EnumProperty, PointerProperty, StringProperty
from bpy.types import Operator, Panel, PropertyGroup

bl_info = {
    "name": "BB Lighting",
    "author": "Beta Builder",
    "version": (0, 4, 0),
    "blender": (4, 2, 0),
    "location": "View3D > Sidebar (N) > BB Light",
    "description": "Light a set by hand and save the result as a named, re-applicable state",
    "category": "Lighting",
}

TEXT_NAME = "BB Lighting States"
RIG = "00 Lighting Rig"
LOCK_KEY = "bb_light_locked"          # scene: what hide_select looked like before Lighting Mode
TRACK_KEY = "bb_light_emission"       # material: True = its glow is recorded by the states
FORMAT = 1

# Everything worth recording about a light. Each entry is (attribute, where it lives).
# "ob" is the object - where the light is and which way it points; "data" is the lamp itself.
LIGHT_FIELDS = (
    ("hide_viewport", "ob"), ("hide_render", "ob"),
    ("location", "ob"), ("rotation_euler", "ob"), ("scale", "ob"),
    ("type", "data"), ("energy", "data"), ("color", "data"),
    ("use_temperature", "data"), ("temperature", "data"),
    ("shadow_soft_size", "data"), ("size", "data"), ("size_y", "data"), ("shape", "data"),
    ("spot_size", "data"), ("spot_blend", "data"), ("angle", "data"),
    ("use_shadow", "data"), ("diffuse_factor", "data"), ("specular_factor", "data"),
    ("volume_factor", "data"),
)

# The scene's colour temperature: Render Properties > Color Management > White Balance.
# The whitepoint colour Blender also shows is worked out from these two, so it is not stored.
VIEW_KEY = "view"
VIEW_FIELDS = ("use_white_balance", "white_balance_temperature", "white_balance_tint")


# ---------------------------------------------------------------------------
# Storage - a Text datablock of JSON, so it is visible and hand-editable
# ---------------------------------------------------------------------------

def _text_block(create=True):
    txt = bpy.data.texts.get(TEXT_NAME)
    if txt is None and create:
        txt = bpy.data.texts.new(TEXT_NAME)
        txt.from_string(json.dumps({"format": FORMAT, "states": []}, indent=1))
    return txt


def _load():
    txt = _text_block(create=False)
    if txt is None:
        return {"format": FORMAT, "states": []}
    try:
        data = json.loads(txt.as_string() or "{}")
    except Exception as exc:
        print("BB Lighting: could not read %s (%s) - starting empty" % (TEXT_NAME, exc))
        return {"format": FORMAT, "states": []}
    data.setdefault("states", [])
    return data


def _save(data):
    txt = _text_block()
    if txt.library is not None:
        raise RuntimeError("the states belong to %s: change them there" % txt.library.name)
    txt.clear()
    txt.write(json.dumps(data, indent=1))


def _states_source():
    """The library the states come from when this file links them (a staging file), else None."""
    txt = _text_block(create=False)
    return txt.library if txt is not None else None


def _refused(op):
    """Operators that write states stop here in a file whose states are linked."""
    lib = _states_source()
    if lib is None:
        return False
    op.report({"ERROR"}, "These states belong to %s - change them there" % lib.name)
    return True


def _set_libraries():
    """Libraries a set or its lights come from; Blender's own bundled asset files are not sets."""
    return [lib for lib in bpy.data.libraries
            if "datafiles" not in lib.filepath.replace("\\", "/").lower().split("/")]


FROM_KEY = "bb_light_states_from"     # scene: the set file whose states this file uses


def _link_states(path=None):
    """A file with no states of its own that links a set which has some: link that set's states.
    A linked text with no users is dropped on save (a fake user does not keep it - tested), so the
    scenes remember the set file and the link is made again on every open: the states here are
    always the set file's current ones."""
    if bpy.data.texts.get(TEXT_NAME) is not None:
        return None
    libs = _set_libraries()
    if path:
        libs = [lib for lib in libs if bpy.path.abspath(lib.filepath) == bpy.path.abspath(path)]
    for lib in libs:
        try:
            with bpy.data.libraries.load(lib.filepath, link=True) as (src, dst):
                if TEXT_NAME not in src.texts:
                    continue
                dst.texts = [TEXT_NAME]
        except Exception as exc:
            print("BB Lighting: could not read %s (%s)" % (lib.filepath, exc))
            continue
        txt = bpy.data.texts.get(TEXT_NAME)
        if txt is not None:
            for scene in bpy.data.scenes:
                scene[FROM_KEY] = lib.filepath
            return txt
    return None


def _link_world(name):
    """A state's world that this file does not have yet, linked from the file the states come from."""
    lib = _states_source()
    if lib is None:
        return None
    try:
        with bpy.data.libraries.load(lib.filepath, link=True) as (src, dst):
            if name not in src.worlds:
                return None
            dst.worlds = [name]
    except Exception as exc:
        print("BB Lighting: could not link world %r (%s)" % (name, exc))
        return None
    return bpy.data.worlds.get(name)


def _state_names(data=None):
    return [s.get("name", "") for s in (data or _load())["states"]]


def _find(data, name):
    for s in data["states"]:
        if s.get("name") == name:
            return s
    return None


# ---------------------------------------------------------------------------
# Which lights a state covers
# ---------------------------------------------------------------------------

def _rig(scene):
    for col in scene.collection.children_recursive:
        if col.name == RIG:
            return col
    return None


def _lights(scene):
    """The lights a state records. The rig if there is one, otherwise every light in the scene.

    Scoping to the rig matters on this project: the gully scenes carry facade review rigs of
    1,800 W keys that have nothing to do with how the set is lit, and a state that quietly
    turned those on or off would wreck a lineup."""
    rig = _rig(scene)
    pool = rig.all_objects if rig is not None else scene.collection.all_objects
    return sorted((ob for ob in pool if ob.type == "LIGHT" and ob.data),
                  key=lambda o: o.name)


# World node values worth recording, by node type. A day and a night look are usually two
# different world datablocks - a daylight HDRI and a night one - so the state records WHICH
# world as well as the dials inside it, and applying a state switches scene.world.
WORLD_NODE_PROPS = {
    "TEX_SKY": ("sun_elevation", "sun_rotation", "sun_intensity", "sun_size",
                "altitude", "air_density", "dust_density", "ozone_density"),
}
WORLD_NODE_INPUTS = ("Color", "Strength", "Location", "Rotation", "Scale")


def _keep_world(world):
    """A world a state records must survive a save. Blender drops any datablock with no users
    when the file is written, and a night world has no users the moment the scene is on the
    day one - measured: the Cloudy night sky world and its packed HDRI vanished from Jai's file
    on the first save after Day was applied. A fake user is what keeps it."""
    if world is not None and not world.use_fake_user:
        world.use_fake_user = True


def _recorded_worlds():
    """Every world any saved state names."""
    try:
        return {s.get("world") for s in _load()["states"] if s.get("world")}
    except Exception:
        return set()


def _world_snapshot(scene):
    """Which world the scene is on, and the dials inside it."""
    out = {}
    world = scene.world
    if world is None:
        return out
    _keep_world(world)
    out["world"] = world.name
    if not world.node_tree:
        return out
    nodes = {}
    for node in world.node_tree.nodes:
        rec = {}
        for name in WORLD_NODE_INPUTS:
            inp = node.inputs.get(name)
            val = getattr(inp, "default_value", None) if inp is not None else None
            if val is None:
                continue
            if hasattr(val, "__len__"):
                rec["in." + name] = [float(v) for v in val]
            else:
                rec["in." + name] = float(val)
        for attr in WORLD_NODE_PROPS.get(node.type, ()):
            if hasattr(node, attr):
                rec[attr] = float(getattr(node, attr))
        if rec:
            nodes[node.name] = rec
    if nodes:
        out["world_nodes"] = nodes
    return out


def _world_restore(scene, snap):
    """Put the scene back on the recorded world, then restore its dials.

    A missing world is reported rather than guessed at: a state recorded in a file that had the
    night HDRI, applied in one that does not, must not silently leave the day sky up and look
    like it worked."""
    if not snap:
        return None
    name = snap.get("world")
    if name:
        world = bpy.data.worlds.get(name) or _link_world(name)
        if world is None:
            return "world %r is not in this file" % name
        if scene.world is not world:
            scene.world = world
        _keep_world(world)
        # the world we just left must survive too, or the next save purges the other state
        for other in bpy.data.worlds:
            if other.name in _recorded_worlds():
                _keep_world(other)
    world = scene.world
    nodes = snap.get("world_nodes") or {}
    if world is None or not world.node_tree or not nodes:
        return None
    for node in world.node_tree.nodes:
        rec = nodes.get(node.name)
        if not rec:
            continue
        for key, val in rec.items():
            try:
                if key.startswith("in."):
                    inp = node.inputs.get(key[3:])
                    if inp is None or not hasattr(inp, "default_value"):
                        continue
                    cur = inp.default_value
                    if hasattr(cur, "__len__"):
                        for i in range(min(len(cur), len(val))):
                            cur[i] = val[i]
                    else:
                        inp.default_value = val
                elif hasattr(node, key):
                    setattr(node, key, val)
            except Exception as exc:
                print("BB Lighting: world %s.%s failed (%s)" % (node.name, key, exc))
    return None


# ---------------------------------------------------------------------------
# Glowing materials - a garland, a tube's glass, a screen
# ---------------------------------------------------------------------------

PRINCIPLED_GLOW = ("Emission Color", "Emission Strength")
EMISSION_GLOW = ("Color", "Strength")
GROUP_GLOW_WORDS = ("emission", "emit", "glow", "strength", "intensity", "bright", "power")
GROUP_GLOW_TYPES = ("VALUE", "RGBA", "INT", "BOOLEAN")


def _value(socket):
    val = socket.default_value
    if hasattr(val, "__len__") and not isinstance(val, str):
        return [float(v) for v in val]
    if isinstance(val, bool):
        return bool(val)
    return float(val)


def _glow_sockets(mat):
    """(node, socket) for every glow value a person can type into this material: the emission
    inputs of each Principled BSDF and Emission node, and the glow-like inputs of node groups.
    A linked socket is fed by something else (a texture, a value node) and is left to it."""
    nt = getattr(mat, "node_tree", None)
    if nt is None:
        return []
    out = []
    for node in nt.nodes:
        if node.type == "BSDF_PRINCIPLED":
            names = PRINCIPLED_GLOW
        elif node.type == "EMISSION":
            names = EMISSION_GLOW
        elif node.type == "GROUP":
            names = None
        else:
            continue
        for sock in node.inputs:
            if sock.is_linked or not hasattr(sock, "default_value"):
                continue
            if names is not None:
                if sock.identifier not in names and sock.name not in names:
                    continue
            elif sock.type not in GROUP_GLOW_TYPES or \
                    not any(w in sock.name.lower() for w in GROUP_GLOW_WORDS):
                continue
            out.append((node, sock))
    return out


def _tree_glows(nt, depth=0):
    for node in nt.nodes:
        if node.mute:
            continue
        if node.type in ("BSDF_PRINCIPLED", "EMISSION"):
            names = PRINCIPLED_GLOW if node.type == "BSDF_PRINCIPLED" else EMISSION_GLOW
            col, strength = node.inputs.get(names[0]), node.inputs.get(names[1])
            if col is None or strength is None:
                continue
            lit = strength.is_linked or float(strength.default_value) > 0.0
            coloured = col.is_linked or max(col.default_value[:3]) > 0.0
            if lit and coloured:
                return True
        elif node.type == "GROUP" and node.node_tree is not None and depth < 3:
            if _tree_glows(node.node_tree, depth + 1):
                return True
    return False


def _is_glowing(mat):
    """Is this material giving off light right now: a non-black colour at a strength above 0."""
    nt = getattr(mat, "node_tree", None)
    return nt is not None and _tree_glows(nt)


def _tracked():
    """Materials whose glow the states record (TRACK_KEY True). False means 'never track'."""
    return sorted((m for m in bpy.data.materials if m.get(TRACK_KEY) and m.library is None),
                  key=lambda m: m.name)


def _object_materials(ob, seen=None, depth=0):
    """The materials an object shows: its own slots, plus - for a collection instance (a facade
    placed many times, a house brought in as one empty) - everything inside the instanced
    collection, nested instances included."""
    out = {}
    for slot in getattr(ob, "material_slots", ()):
        mat = slot.material
        if mat is not None and mat.library is None:
            out[mat.name] = mat
    col = ob.instance_collection if ob.instance_type == "COLLECTION" else None
    if col is not None and depth < 4:
        seen = seen if seen is not None else set()
        if col.name not in seen:
            seen.add(col.name)
            for inner in col.all_objects:
                out.update(_object_materials(inner, seen, depth + 1))
    return out


def _scene_materials(scene):
    """Materials on the objects this scene shows, including what collection instances show;
    excluded and hidden collections are left out, so review rigs and archived strays never get
    tracked by accident."""
    vl = scene.view_layers[0] if len(scene.view_layers) else None
    if getattr(bpy.context, "scene", None) == scene and getattr(bpy.context, "view_layer", None):
        vl = bpy.context.view_layer
    mats = {}
    seen = set()
    for ob in scene.objects:
        if vl is not None:
            try:
                if not ob.visible_get(view_layer=vl):
                    continue
            except Exception:
                pass
        mats.update(_object_materials(ob, seen))
    return mats


def _capture_material(mat):
    rec = {}
    for node, sock in _glow_sockets(mat):
        rec.setdefault(node.name, {})[sock.identifier] = _value(sock)
    nt = getattr(mat, "node_tree", None)
    for node in (nt.nodes if nt is not None else ()):
        if node.type == "EMISSION":
            rec.setdefault(node.name, {})["mute"] = bool(node.mute)
    return rec


def _capture_materials(scene):
    """Start tracking whatever is glowing now (unless someone said never), then record every
    tracked material."""
    for mat in _scene_materials(scene).values():
        if TRACK_KEY not in mat and _is_glowing(mat):
            mat[TRACK_KEY] = True
    return {m.name: _capture_material(m) for m in _tracked()}


def _apply_materials(state):
    """Put every recorded glow back. Returns (restored, missing)."""
    restored, missing = 0, []
    for name, rec in (state.get("materials") or {}).items():
        mat = bpy.data.materials.get(name)
        nt = getattr(mat, "node_tree", None)
        if mat is None or nt is None:
            missing.append("material %s" % name)
            continue
        for node_name, vals in rec.items():
            node = nt.nodes.get(node_name)
            if node is None:
                missing.append("material %s: node %s" % (name, node_name))
                continue
            for key, val in vals.items():
                try:
                    if key == "mute":
                        if node.mute != bool(val):
                            node.mute = bool(val)
                        continue
                    sock = next((s for s in node.inputs if s.identifier == key), None)
                    if sock is None or sock.is_linked or not hasattr(sock, "default_value"):
                        continue
                    cur = sock.default_value
                    if hasattr(cur, "__len__") and not isinstance(cur, str):
                        sock.default_value = [float(v) for v in val][:len(cur)]
                    elif isinstance(cur, bool):
                        sock.default_value = bool(val)
                    elif isinstance(cur, int):
                        sock.default_value = int(val)
                    else:
                        sock.default_value = float(val)
                except Exception as exc:
                    print("BB Lighting: material %s / %s / %s -> %r failed (%s)" % (name, node_name, key, val, exc))
        restored += 1
    return restored, missing


def _view_snapshot(scene):
    """The scene's white balance, as the Color Management panel shows it."""
    vs = scene.view_settings
    out = {}
    for attr in VIEW_FIELDS:
        if hasattr(vs, attr):
            val = getattr(vs, attr)
            out[attr] = bool(val) if isinstance(val, bool) else float(val)
    return out


def _view_restore(scene, rec):
    """Put the recorded white balance back. Fields this Blender does not have are skipped."""
    vs = scene.view_settings
    done = 0
    for attr in VIEW_FIELDS:
        if attr in rec and hasattr(vs, attr):
            try:
                cur = getattr(vs, attr)
                setattr(vs, attr, bool(rec[attr]) if isinstance(cur, bool) else type(cur)(rec[attr]))
                done += 1
            except Exception as exc:
                print("BB Lighting: view %s -> %r failed (%s)" % (attr, rec[attr], exc))
    return done


def _not_recorded(data=None):
    """{state name: [what it has no record of]} - tracked materials, and the white balance for
    states saved before 0.2.4. Only states that miss something are listed."""
    tracked = [m.name for m in _tracked()]
    out = {}
    for st in (data or _load())["states"]:
        have = st.get("materials") or {}
        miss = [n for n in tracked if n not in have]
        if VIEW_KEY not in st:
            miss.append("white balance")
        if miss:
            out[st.get("name", "")] = miss
    return out


def _capture(scene):
    """Read every light in scope, exactly as it stands."""
    lights = {}
    for ob in _lights(scene):
        rec = {}
        for attr, where in LIGHT_FIELDS:
            owner = ob if where == "ob" else ob.data
            if not hasattr(owner, attr):
                continue
            val = getattr(owner, attr)
            if hasattr(val, "__len__") and not isinstance(val, str):
                rec[attr] = [float(v) for v in val]
            elif isinstance(val, bool):
                rec[attr] = bool(val)
            elif isinstance(val, (int, float)):
                rec[attr] = float(val)
            else:
                rec[attr] = str(val)
        lights[ob.name] = rec
    snap = {"lights": lights}
    snap.update(_world_snapshot(scene))
    snap["materials"] = _capture_materials(scene)
    snap[VIEW_KEY] = _view_snapshot(scene)
    return snap


# ---------------------------------------------------------------------------
# Set dressing - the props that exist only in some states (0.3.0 "looks", renamed in 0.4.0)
# ---------------------------------------------------------------------------
# A collection named "DRESSING · <state>" belongs to that state: applying the state includes it,
# applying any other state excludes it (the outliner checkbox - excluded collections are not drawn,
# not rendered and not even evaluated, so a garland's geometry nodes cost nothing in a day state).
# "DRESSING · Wedding, Night party" belongs to both. Nothing is recorded: the name is the rule, so a
# dressing survives every Save and Update and can be made, renamed or emptied by hand. The switch is
# the view layer's own checkbox, so it works on a dressing linked from a set file too.

DRESS_WORD = "DRESSING"


def _dressing_states(col):
    """The state names a dressing collection belongs to, or None if it is not one."""
    n = col.name
    k = len(DRESS_WORD)
    if not n[:k].upper() == DRESS_WORD or (len(n) > k and n[k].isalnum()):
        return None
    rest = n[k:].lstrip(" ·|:-–—")
    return [s.strip() for s in rest.split(",") if s.strip()]


def _dressings(scene):
    return [c for c in scene.collection.children_recursive if _dressing_states(c) is not None]


def _layer_collections(scene, col):
    out = []
    def walk(lc):
        if lc.collection == col:
            out.append(lc)
            return
        for ch in lc.children:
            walk(ch)
    for vl in scene.view_layers:
        walk(vl.layer_collection)
    return out


def _dressing_on(scene, col):
    lcs = _layer_collections(scene, col)
    return bool(lcs) and not all(lc.exclude for lc in lcs)


def _apply_dressings(scene, state_name):
    """Include the dressings that belong to this state, exclude every other one. Returns [(name, on)]."""
    done = []
    key = (state_name or "").strip().lower()
    for col in _dressings(scene):
        on = key in [s.lower() for s in _dressing_states(col)]
        for lc in _layer_collections(scene, col):
            if lc.exclude == on:
                lc.exclude = not on
        done.append((col.name, on))
    return done


def _dressing_home(scene):
    """Where a new dressing collection goes: the rig, else a top-level lighting collection, else the scene."""
    rig = _rig(scene)
    if rig is not None:
        return rig
    for col in scene.collection.children:
        if col.name.lower().replace("_", " ").startswith("00 light"):
            return col
    return scene.collection


def _apply(scene, state):
    """Put every recorded light back the way it was. Returns (restored, missing, extra)."""
    _apply_dressings(scene, state.get("name"))
    lights = state.get("lights", {})
    in_scope = {ob.name: ob for ob in _lights(scene)}
    restored, missing = 0, []
    for name, rec in lights.items():
        ob = in_scope.get(name) or bpy.data.objects.get(name)
        if ob is None or ob.type != "LIGHT":
            missing.append(name)
            continue
        for attr, where in LIGHT_FIELDS:
            if attr not in rec:
                continue
            owner = ob if where == "ob" else ob.data
            if not hasattr(owner, attr):
                continue
            val = rec[attr]
            try:
                cur = getattr(owner, attr)
                if hasattr(cur, "__len__") and not isinstance(cur, str):
                    for i in range(min(len(cur), len(val))):
                        cur[i] = val[i]
                elif isinstance(cur, bool):
                    setattr(owner, attr, bool(val))
                elif isinstance(cur, (int, float)):
                    setattr(owner, attr, type(cur)(val))
                else:
                    setattr(owner, attr, val)
            except Exception as exc:
                print("BB Lighting: %s.%s -> %r failed (%s)" % (ob.name, attr, val, exc))
        restored += 1
    # lights that exist now but were not in the recording are LEFT ALONE, never guessed at
    extra = sorted(set(in_scope) - set(lights))
    world_problem = _world_restore(scene, state)
    if world_problem:
        missing.append(world_problem)
    # glowing materials: recorded ones are put back; tracked ones this state never recorded are
    # left as they are and reported, exactly like lights
    _m_restored, m_missing = _apply_materials(state)
    missing.extend(m_missing)
    recorded = set((state.get("materials") or {}).keys())
    extra = list(extra) + ["material %s" % m.name for m in _tracked() if m.name not in recorded]
    # white balance: put back when recorded; a state from before 0.2.4 leaves it alone
    if VIEW_KEY in state:
        _view_restore(scene, state[VIEW_KEY])
    else:
        extra.append("white balance")
    scene.update_tag()
    vl = getattr(bpy.context, "view_layer", None)
    if vl is not None:
        vl.update()
    return restored, missing, extra


# ---------------------------------------------------------------------------
# Lighting Mode - the set is locked, the lights are not
# ---------------------------------------------------------------------------

def _set_lock(scene, on):
    rig = _rig(scene)
    keep = rig.children_recursive + [rig] if rig is not None else []
    keep_names = {c.name for c in keep}
    if on:
        was = {}
        for col in scene.collection.children_recursive:
            was[col.name] = bool(col.hide_select)
            col.hide_select = col.name not in keep_names
        scene[LOCK_KEY] = json.dumps(was)
    else:
        try:
            was = json.loads(scene.get(LOCK_KEY, "") or "{}")
        except Exception:
            was = {}
        for col in scene.collection.children_recursive:
            col.hide_select = bool(was.get(col.name, False))
        if LOCK_KEY in scene:
            del scene[LOCK_KEY]


def _mode_update(self, context):
    _set_lock(context.scene, self.lighting_mode)


class BBL_Props(PropertyGroup):
    lighting_mode: BoolProperty(
        name="Lighting Mode",
        description="Lock the set so only the lights can be selected. The model is still "
                    "visible, it just cannot be clicked by accident while you work",
        default=False, update=_mode_update,
    )
    active: StringProperty(name="State", default="")
    new_name: StringProperty(name="Name", default="")


def _items(self, context):
    names = _state_names()
    return [(n, n, "Apply %s" % n) for n in names] or [("", "", "")]


# ---------------------------------------------------------------------------
# Operators
# ---------------------------------------------------------------------------

class BBL_OT_save_new(Operator):
    """Record every light exactly as it is now, under a new name"""

    bl_idname = "bb_light.save_new"
    bl_label = "Save Current Lighting"
    bl_options = {"REGISTER", "UNDO"}

    name: StringProperty(name="Name", default="New State")

    def invoke(self, context, event):
        n = len(_state_names())
        self.name = "State %d" % (n + 1) if n else "Day"
        return context.window_manager.invoke_props_dialog(self)

    def execute(self, context):
        if _refused(self):
            return {"CANCELLED"}
        scene = context.scene
        name = " ".join(self.name.split()).strip()
        if not name:
            self.report({"ERROR"}, "Give the state a name")
            return {"CANCELLED"}
        data = _load()
        if _find(data, name):
            self.report({"ERROR"}, "A state called %r already exists - use Update" % name)
            return {"CANCELLED"}
        state = _capture(scene)
        state["name"] = name
        data["states"].append(state)
        _save(data)
        scene.bb_light.active = name
        self.report({"INFO"}, "Saved %r - %d light(s)" % (name, len(state["lights"])))
        return {"FINISHED"}


class BBL_OT_update(Operator):
    """Overwrite this state with the lighting as it stands now"""

    bl_idname = "bb_light.update"
    bl_label = "Update State"
    bl_options = {"REGISTER", "UNDO"}

    name: StringProperty(options={"HIDDEN", "SKIP_SAVE"})

    def invoke(self, context, event):
        return context.window_manager.invoke_confirm(self, event)

    def execute(self, context):
        if _refused(self):
            return {"CANCELLED"}
        data = _load()
        state = _find(data, self.name)
        if state is None:
            self.report({"ERROR"}, "No state called %r" % self.name)
            return {"CANCELLED"}
        fresh = _capture(context.scene)
        state["lights"] = fresh["lights"]
        for key in list(state):
            if key.startswith(("bg_", "sky_")) or key == "world":
                del state[key]
        state.update({k: v for k, v in fresh.items() if k != "lights"})
        _save(data)
        self.report({"INFO"}, "Updated %r - %d light(s)" % (self.name, len(state["lights"])))
        return {"FINISHED"}


class BBL_OT_apply(Operator):
    """Put every light back the way this state recorded it"""

    bl_idname = "bb_light.apply"
    bl_label = "Apply State"
    bl_options = {"REGISTER", "UNDO"}

    name: StringProperty(options={"HIDDEN", "SKIP_SAVE"})

    def execute(self, context):
        data = _load()
        state = _find(data, self.name)
        if state is None:
            self.report({"ERROR"}, "No state called %r" % self.name)
            return {"CANCELLED"}
        restored, missing, extra = _apply(context.scene, state)
        context.scene.bb_light.active = self.name
        _FOLLOW["scene"] = context.scene.as_pointer()
        msg = "%s - %d light(s)" % (self.name, restored)
        n_mat = len(state.get("materials") or {})
        if n_mat:
            msg += ", %d glowing material(s)" % n_mat
        if missing:
            msg += ", %d missing (%s)" % (len(missing), ", ".join(missing[:3]))
        if extra:
            msg += ", %d not in this state and left alone" % len(extra)
        self.report({"WARNING"} if missing else {"INFO"}, msg)
        return {"FINISHED"}


class BBL_OT_rename(Operator):
    """Rename this lighting state"""

    bl_idname = "bb_light.rename"
    bl_label = "Rename State"
    bl_options = {"REGISTER", "UNDO"}

    # which state to rename: set by the button, never shown. Before 0.2.5 the dialog showed it as
    # an editable "Name" field above "New name"; typing the new name into that first field made
    # the operator look for a state that does not exist, and it cancelled without a word.
    name: StringProperty(options={"HIDDEN", "SKIP_SAVE"})
    new_name: StringProperty(name="New name", default="", options={"SKIP_SAVE"})

    def invoke(self, context, event):
        self.new_name = self.name
        return context.window_manager.invoke_props_dialog(self, title="Rename %s" % self.name, confirm_text="Rename")

    def draw(self, context):
        col = self.layout.column()
        col.activate_init = True          # the field is ready to type into, text selected
        col.prop(self, "new_name", text="")

    def execute(self, context):
        if _refused(self):
            return {"CANCELLED"}
        new = " ".join(self.new_name.split()).strip()
        data = _load()
        state = _find(data, self.name)
        if state is None:
            self.report({"ERROR"}, "No state called %r to rename" % self.name)
            return {"CANCELLED"}
        if not new:
            self.report({"ERROR"}, "Give the state a name")
            return {"CANCELLED"}
        if new == self.name:
            return {"CANCELLED"}
        if _find(data, new):
            self.report({"ERROR"}, "A state called %r already exists" % new)
            return {"CANCELLED"}
        state["name"] = new
        _save(data)
        if context.scene.bb_light.active == self.name or not context.scene.bb_light.active:
            context.scene.bb_light.active = new
        # the state's dressing collections follow the new name
        renamed = 0
        for scene in bpy.data.scenes:
            for col in _dressings(scene):
                names = _dressing_states(col)
                if col.library is None and any(n.lower() == self.name.lower() for n in names):
                    col.name = "%s · %s" % (DRESS_WORD, ", ".join(new if n.lower() == self.name.lower() else n for n in names))
                    renamed += 1
        self.report({"INFO"}, "Renamed %r to %r%s" % (self.name, new, " and its set dressing" if renamed else ""))
        return {"FINISHED"}


class BBL_OT_dressing_from_selected(Operator):
    """Move the selected objects into this state's set dressing ("DRESSING · <state>"), made if needed.
They then exist only while this state is applied: every other state switches the collection off"""

    bl_idname = "bb_light.dressing_from_selected"
    bl_label = "Put Selected in Set Dressing"
    bl_options = {"REGISTER", "UNDO"}

    name: StringProperty(options={"HIDDEN", "SKIP_SAVE"})

    def execute(self, context):
        scene = context.scene
        state = (self.name or scene.bb_light.active or "").strip()
        if not state or _find(_load(), state) is None:
            self.report({"ERROR"}, "Apply or save the state first, then select what belongs only to it")
            return {"CANCELLED"}
        obs = [ob for ob in context.selected_objects if ob.library is None]
        if not obs:
            self.report({"WARNING"}, "Select the objects of this file that should exist only in %s" % state)
            return {"CANCELLED"}
        col = next((c for c in _dressings(scene) if c.library is None
                    and [n.lower() for n in _dressing_states(c)] == [state.lower()]), None)
        if col is None:
            col = bpy.data.collections.new("%s · %s" % (DRESS_WORD, state))
            _dressing_home(scene).children.link(col)
            col.color_tag = "COLOR_02"
        in_scene = set(scene.collection.children_recursive) | {scene.collection}
        for ob in obs:
            for c in list(ob.users_collection):
                if c in in_scene and c != col and c.library is None:
                    c.objects.unlink(ob)
            if ob.name not in col.objects:
                col.objects.link(ob)
        _apply_dressings(scene, scene.bb_light.active)
        self.report({"INFO"}, "%d object(s) now live in %s - shown only in %s" % (len(obs), col.name, state))
        return {"FINISHED"}


class BBL_OT_delete(Operator):
    """Delete this lighting state. The lights themselves are not touched"""

    bl_idname = "bb_light.delete"
    bl_label = "Delete State"
    bl_options = {"REGISTER", "UNDO"}

    name: StringProperty(options={"HIDDEN", "SKIP_SAVE"})

    def invoke(self, context, event):
        return context.window_manager.invoke_confirm(self, event)

    def execute(self, context):
        if _refused(self):
            return {"CANCELLED"}
        data = _load()
        state = _find(data, self.name)
        if state is None:
            return {"CANCELLED"}
        data["states"].remove(state)
        _save(data)
        self.report({"INFO"}, "Deleted %r (the lights are untouched)" % self.name)
        return {"FINISHED"}


class BBL_OT_select_lights(Operator):
    """Select every light in the rig, so you can see and move them"""

    bl_idname = "bb_light.select_lights"
    bl_label = "Select All Lights"
    bl_options = {"REGISTER", "UNDO"}

    def execute(self, context):
        lights = _lights(context.scene)
        for ob in context.view_layer.objects:
            ob.select_set(False)
        n = 0
        for ob in lights:
            try:
                ob.select_set(True)
                n += 1
            except RuntimeError:
                pass          # not in this view layer, or still locked
        if lights:
            context.view_layer.objects.active = lights[0]
        self.report({"INFO"}, "Selected %d light(s)" % n)
        return {"FINISHED"}


def _selected_materials(context):
    """Materials of the selected objects; a selected collection instance brings everything it
    shows (so selecting one placed facade tracks the bulbs of every copy of it)."""
    mats = {}
    for ob in context.selected_objects:
        for name, mat in _object_materials(ob).items():
            if getattr(mat, "node_tree", None) is not None:
                mats[name] = mat
    return mats


class BBL_OT_track_emission(Operator):
    """Record the glow of the selected objects' materials in the lighting states from now on.
Do it while they look right for the states you already saved: their glow as it is now is written
into every saved state that has no record of them. Then change them and press Update on the
state that should look different"""

    bl_idname = "bb_light.track_emission"
    bl_label = "Track Emission of Selected"
    bl_options = {"REGISTER", "UNDO"}

    def execute(self, context):
        if _refused(self):
            return {"CANCELLED"}
        mats = _selected_materials(context)
        usable = {n: m for n, m in mats.items() if _glow_sockets(m)}
        if not usable:
            self.report({"WARNING"}, "Nothing to track: select objects whose material has a "
                                     "Principled BSDF or Emission node with a typed-in glow value")
            return {"CANCELLED"}
        data = _load()
        filled = 0
        for name, mat in usable.items():
            mat[TRACK_KEY] = True
            rec = _capture_material(mat)
            for st in data["states"]:
                have = st.setdefault("materials", {})
                if name not in have:
                    have[name] = rec
                    filled += 1
        _save(data)
        skipped = sorted(set(mats) - set(usable))
        msg = "Tracking %d material(s): %s" % (len(usable), ", ".join(sorted(usable)[:4]))
        if filled:
            msg += " - their glow now written into %d state record(s)" % filled
        if skipped:
            msg += " (%d without a glow value skipped)" % len(skipped)
        self.report({"INFO"}, msg)
        return {"FINISHED"}


class BBL_OT_untrack_emission(Operator):
    """Stop recording the glow of the selected objects' materials and take them out of every
saved state. The materials keep the glow they have now, and are never tracked again by
themselves"""

    bl_idname = "bb_light.untrack_emission"
    bl_label = "Stop Tracking Selected"
    bl_options = {"REGISTER", "UNDO"}

    def execute(self, context):
        if _refused(self):
            return {"CANCELLED"}
        mats = _selected_materials(context)
        if not mats:
            self.report({"WARNING"}, "Select the objects whose materials should stop being recorded")
            return {"CANCELLED"}
        data = _load()
        for name, mat in mats.items():
            mat[TRACK_KEY] = False
            for st in data["states"]:
                (st.get("materials") or {}).pop(name, None)
        _save(data)
        self.report({"INFO"}, "No longer tracking %d material(s): %s" % (len(mats), ", ".join(sorted(mats)[:4])))
        return {"FINISHED"}


class BBL_OT_select_emission(Operator):
    """Select every object whose material glow the lighting states record"""

    bl_idname = "bb_light.select_emission"
    bl_label = "Select Tracked Glowing Objects"
    bl_options = {"REGISTER", "UNDO"}

    def execute(self, context):
        names = {m.name for m in _tracked()}
        for ob in context.view_layer.objects:
            ob.select_set(False)
        n = 0
        first = None
        for ob in context.view_layer.objects:
            if names & set(_object_materials(ob)):
                try:
                    ob.select_set(True)
                    n += 1
                    first = first or ob
                except RuntimeError:
                    pass
        if first is not None:
            context.view_layer.objects.active = first
        self.report({"INFO"}, "Selected %d object(s) using %d tracked material(s)" % (n, len(names)))
        return {"FINISHED"}


class BBL_OT_show_text(Operator):
    """Open the saved states as text, to read or edit by hand"""

    bl_idname = "bb_light.show_text"
    bl_label = "Show States As Text"

    def execute(self, context):
        txt = _text_block()
        for area in context.screen.areas:
            if area.type == "TEXT_EDITOR":
                area.spaces.active.text = txt
                self.report({"INFO"}, "Showing %s" % TEXT_NAME)
                return {"FINISHED"}
        self.report({"INFO"}, "Open a Text Editor and choose %r" % TEXT_NAME)
        return {"FINISHED"}


# ---------------------------------------------------------------------------
# Panel
# ---------------------------------------------------------------------------

class BBL_PT_main(Panel):
    bl_space_type = "VIEW_3D"
    bl_region_type = "UI"
    bl_category = "BB Light"
    bl_label = "Lighting States"
    bl_idname = "BBL_PT_main"

    def draw(self, context):
        lay = self.layout
        scene = context.scene
        p = scene.bb_light

        row = lay.row()
        row.scale_y = 1.5
        row.prop(p, "lighting_mode", toggle=True,
                 icon="LOCKED" if p.lighting_mode else "UNLOCKED",
                 text="Lighting Mode  (set locked)" if p.lighting_mode
                      else "Lighting Mode  (set clickable)")
        lay.operator("bb_light.select_lights", icon="LIGHT", text="Select All Lights")

        rig = _rig(scene)
        sub = lay.row()
        sub.scale_y = 0.7
        sub.label(text="%d light(s) in %s" % (len(_lights(scene)), rig.name if rig else "the scene"),
                  icon="OUTLINER_OB_LIGHT")

        data = _load()
        source = _states_source()
        if source is not None:
            # a staging file: the set file owns the states, this file only applies them
            box = lay.box()
            col = box.column(align=True)
            col.label(text="States from %s" % source.name, icon="LINKED")
            sub = col.column(align=True)
            sub.scale_y = 0.8
            sub.label(text="Change or add states in that file.")
            sub.label(text="Each scene here keeps the state you pick.")
        box = lay.box()
        col = box.column(align=True)
        if source is None:
            tracked = _tracked()
            col.label(text="Glowing materials: %d recorded" % len(tracked), icon="SHADING_RENDERED")
            row = col.row(align=True)
            row.operator("bb_light.track_emission", text="Track", icon="ADD")
            row.operator("bb_light.untrack_emission", text="Untrack", icon="REMOVE")
            row.operator("bb_light.select_emission", text="Select", icon="RESTRICT_SELECT_OFF")
        else:
            glows = {n for st in data["states"] for n in (st.get("materials") or {})}
            col.label(text="Glowing materials: %d, from the set file" % len(glows), icon="SHADING_RENDERED")

        # the scene's white balance, the same three controls as Color Management, recorded by
        # every state saved or updated from 0.2.4 on
        vs = scene.view_settings
        if hasattr(vs, "white_balance_temperature"):
            box = lay.box()
            col = box.column(align=True)
            col.prop(vs, "use_white_balance", text="Colour temperature (white balance)")
            sub = col.column(align=True)
            sub.active = vs.use_white_balance
            sub.prop(vs, "white_balance_temperature", text="Temperature")
            sub.prop(vs, "white_balance_tint", text="Tint")

        # set dressing: the props that exist only in some states
        box = lay.box()
        col = box.column(align=True)
        dressings = _dressings(scene)
        names = {s.get("name", "").lower() for s in data["states"]}
        col.label(text="Set dressing: %d (props only some states have)" % len(dressings), icon="OUTLINER_COLLECTION")
        for dc in dressings:
            owners = _dressing_states(dc)
            r = col.row(align=True)
            r.label(text="%s  ->  %s" % (dc.name, ", ".join(owners) or "no state"),
                    icon="CHECKBOX_HLT" if _dressing_on(scene, dc) else "CHECKBOX_DEHLT")
            orphan = [o for o in owners if o.lower() not in names]
            if orphan or not owners:
                w = col.row()
                w.alert = True
                w.scale_y = 0.8
                w.label(text="no state called %s - rename the collection or the state" % (", ".join(orphan) or "(none)"), icon="ERROR")
        r = col.row()
        r.enabled = bool(p.active)
        r.operator("bb_light.dressing_from_selected", icon="ADD",
                   text="Put Selected in %s Dressing" % p.active if p.active
                   else "Put Selected in a Dressing (apply a state first)").name = p.active

        for st_name, miss in _not_recorded(data).items():
            warn = lay.row()
            warn.alert = True
            warn.scale_y = 0.8
            what = ", ".join(miss) if len(miss) <= 2 else "%d items" % len(miss)
            warn.label(text="%s: %s not recorded - apply, set, Update" % (st_name, what), icon="ERROR")

        lay.separator()
        states = data["states"]
        if not states:
            box = lay.box()
            box.scale_y = 0.8
            box.label(text="No saved states yet.", icon="INFO")
            box.label(text="Set the lights how you want them,")
            box.label(text="then press Save Current Lighting.")
            if _set_libraries():
                box.operator("bb_light.link_states", icon="LINKED", text="Use the Set File's States")
        for state in states:
            name = state.get("name", "")
            # A split, not scale_x. Squeezing icon buttons below their natural width makes them
            # overlap each other and the panel edge in a narrow sidebar, which is exactly what
            # scale_x = 0.6 did here. The split gives the name the room and the three actions a
            # fixed share that Blender is free to draw at its own icon width.
            row = lay.row(align=True)
            row.scale_y = 1.3
            if source is not None:
                row.operator("bb_light.apply", text=name, depress=p.active == name, icon="LIGHT_DATA").name = name
                continue
            split = row.split(factor=0.62, align=True)
            op = split.operator("bb_light.apply", text=name,
                                depress=p.active == name, icon="LIGHT_DATA")
            op.name = name
            actions = split.row(align=True)
            actions.operator("bb_light.update", text="", icon="FILE_REFRESH").name = name
            actions.operator("bb_light.rename", text="", icon="GREASEPENCIL").name = name
            actions.operator("bb_light.delete", text="", icon="X").name = name

        lay.separator()
        if source is None:
            row = lay.row()
            row.scale_y = 1.4
            row.operator("bb_light.save_new", icon="ADD", text="Save Current Lighting")
        foot = lay.row()
        foot.scale_y = 0.7
        foot.operator("bb_light.show_text", text=TEXT_NAME, icon="TEXT", emboss=False)


class BBL_OT_link_states(Operator):
    """Use the states of the set file this file links its set and lights from (a staging file).
They stay that file's: change them there, apply them here"""

    bl_idname = "bb_light.link_states"
    bl_label = "Use the Set File's States"
    bl_options = {"REGISTER", "UNDO"}

    def execute(self, context):
        txt = _link_states()
        if txt is None:
            self.report({"WARNING"}, "None of the linked files has lighting states")
            return {"CANCELLED"}
        _FOLLOW["scene"] = None
        self.report({"INFO"}, "%d state(s) from %s" % (len(_state_names()), txt.library.name))
        return {"FINISHED"}


# In a file whose states are linked, applying a state changes linked lights and glows. Blender keeps
# those changes for the session only - they belong to the set file and are not written into this one -
# and every scene of a staging file shows the same linked lights. So each scene keeps the name of its
# state (bb_light.active), and it is put back when the file opens and whenever another scene comes on
# screen. A timer, not a handler: it changes visibility, which a frame or depsgraph handler must not.
_FOLLOW = {"scene": None}


def _window_scene():
    wm = bpy.context.window_manager
    if wm is None or not wm.windows:
        return None
    return wm.windows[0].scene


def _follow_scene():
    try:
        if _states_source() is None:
            _FOLLOW["scene"] = None
            return 1.0
        scene = _window_scene()
        if scene is None or scene.as_pointer() == _FOLLOW["scene"]:
            return 0.5
        _FOLLOW["scene"] = scene.as_pointer()
        name = scene.bb_light.active
        state = _find(_load(), name) if name else None
        if state is not None:
            _apply(scene, state)
    except Exception as exc:
        print("BB Lighting: could not put the scene's state back (%s)" % exc)
    return 0.5


@persistent
def _on_load(_dummy):
    # Lighting Mode is a working state, not something a file should open in
    for scene in bpy.data.scenes:
        if getattr(scene, "bb_light", None) and scene.bb_light.lighting_mode:
            scene.bb_light["lighting_mode"] = False
        if LOCK_KEY in scene:
            _set_lock(scene, False)
    # a staging file: link the set file's states again (they are read fresh from it every time)
    path = next((s.get(FROM_KEY) for s in bpy.data.scenes if s.get(FROM_KEY)), None)
    if path:
        _link_states(path)
    _FOLLOW["scene"] = None         # the linked lights came back as the set file has them


CLASSES = (
    BBL_Props,
    BBL_OT_save_new,
    BBL_OT_update,
    BBL_OT_apply,
    BBL_OT_rename,
    BBL_OT_delete,
    BBL_OT_select_lights,
    BBL_OT_track_emission,
    BBL_OT_untrack_emission,
    BBL_OT_select_emission,
    BBL_OT_show_text,
    BBL_OT_dressing_from_selected,
    BBL_OT_link_states,
    BBL_PT_main,
)

_OWNS = {"registered": False}


def register():
    if hasattr(bpy.types.Scene, "bb_light"):
        print("BB Lighting: another copy is already active - this one stays idle")
        return
    _OWNS["registered"] = True
    for c in CLASSES:
        bpy.utils.register_class(c)
    bpy.types.Scene.bb_light = PointerProperty(type=BBL_Props)
    if _on_load not in bpy.app.handlers.load_post:
        bpy.app.handlers.load_post.append(_on_load)
    if not bpy.app.timers.is_registered(_follow_scene):
        bpy.app.timers.register(_follow_scene, first_interval=1.0, persistent=True)


def unregister():
    if not _OWNS["registered"]:
        return
    _OWNS["registered"] = False
    if _on_load in bpy.app.handlers.load_post:
        bpy.app.handlers.load_post.remove(_on_load)
    if bpy.app.timers.is_registered(_follow_scene):
        bpy.app.timers.unregister(_follow_scene)
    for scene in bpy.data.scenes:
        if LOCK_KEY in scene:
            _set_lock(scene, False)
    del bpy.types.Scene.bb_light
    for c in reversed(CLASSES):
        bpy.utils.unregister_class(c)


if __name__ == "__main__":
    register()
