# SPDX-License-Identifier: GPL-2.0-or-later
"""BB Lighting - light a Beta Builder set by hand, then save what you did.

A lighting state here is not a collection you switch between. It is a RECORDING of every light
in the rig exactly as you left it: on or off, where it points, its energy, colour, temperature,
size and shadow settings, plus the world. You move lights around until the set looks right, you
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
    "version": (0, 2, 1),
    "blender": (4, 2, 0),
    "location": "View3D > Sidebar (N) > BB Light",
    "description": "Light a set by hand and save the result as a named, re-applicable state",
    "category": "Lighting",
}

TEXT_NAME = "BB Lighting States"
RIG = "00 Lighting Rig"
LOCK_KEY = "bb_light_locked"          # scene: what hide_select looked like before Lighting Mode
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
    txt.clear()
    txt.write(json.dumps(data, indent=1))


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
        world = bpy.data.worlds.get(name)
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
    return snap


def _apply(scene, state):
    """Put every recorded light back the way it was. Returns (restored, missing, extra)."""
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

    name: StringProperty()

    def invoke(self, context, event):
        return context.window_manager.invoke_confirm(self, event)

    def execute(self, context):
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

    name: StringProperty()

    def execute(self, context):
        data = _load()
        state = _find(data, self.name)
        if state is None:
            self.report({"ERROR"}, "No state called %r" % self.name)
            return {"CANCELLED"}
        restored, missing, extra = _apply(context.scene, state)
        context.scene.bb_light.active = self.name
        msg = "%s - %d light(s)" % (self.name, restored)
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

    name: StringProperty()
    new_name: StringProperty(name="New name", default="")

    def invoke(self, context, event):
        self.new_name = self.name
        return context.window_manager.invoke_props_dialog(self)

    def execute(self, context):
        new = " ".join(self.new_name.split()).strip()
        data = _load()
        state = _find(data, self.name)
        if state is None or not new:
            return {"CANCELLED"}
        if new != self.name and _find(data, new):
            self.report({"ERROR"}, "A state called %r already exists" % new)
            return {"CANCELLED"}
        state["name"] = new
        _save(data)
        context.scene.bb_light.active = new
        return {"FINISHED"}


class BBL_OT_delete(Operator):
    """Delete this lighting state. The lights themselves are not touched"""

    bl_idname = "bb_light.delete"
    bl_label = "Delete State"
    bl_options = {"REGISTER", "UNDO"}

    name: StringProperty()

    def invoke(self, context, event):
        return context.window_manager.invoke_confirm(self, event)

    def execute(self, context):
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

        lay.separator()
        data = _load()
        states = data["states"]
        if not states:
            box = lay.box()
            box.scale_y = 0.8
            box.label(text="No saved states yet.", icon="INFO")
            box.label(text="Set the lights how you want them,")
            box.label(text="then press Save Current Lighting.")
        for state in states:
            name = state.get("name", "")
            # A split, not scale_x. Squeezing icon buttons below their natural width makes them
            # overlap each other and the panel edge in a narrow sidebar, which is exactly what
            # scale_x = 0.6 did here. The split gives the name the room and the three actions a
            # fixed share that Blender is free to draw at its own icon width.
            row = lay.row(align=True)
            row.scale_y = 1.3
            split = row.split(factor=0.62, align=True)
            op = split.operator("bb_light.apply", text=name,
                                depress=p.active == name, icon="LIGHT_DATA")
            op.name = name
            actions = split.row(align=True)
            actions.operator("bb_light.update", text="", icon="FILE_REFRESH").name = name
            actions.operator("bb_light.rename", text="", icon="GREASEPENCIL").name = name
            actions.operator("bb_light.delete", text="", icon="X").name = name

        lay.separator()
        row = lay.row()
        row.scale_y = 1.4
        row.operator("bb_light.save_new", icon="ADD", text="Save Current Lighting")
        foot = lay.row()
        foot.scale_y = 0.7
        foot.operator("bb_light.show_text", text=TEXT_NAME, icon="TEXT", emboss=False)


@persistent
def _on_load(_dummy):
    # Lighting Mode is a working state, not something a file should open in
    for scene in bpy.data.scenes:
        if getattr(scene, "bb_light", None) and scene.bb_light.lighting_mode:
            scene.bb_light["lighting_mode"] = False
        if LOCK_KEY in scene:
            _set_lock(scene, False)


CLASSES = (
    BBL_Props,
    BBL_OT_save_new,
    BBL_OT_update,
    BBL_OT_apply,
    BBL_OT_rename,
    BBL_OT_delete,
    BBL_OT_select_lights,
    BBL_OT_show_text,
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


def unregister():
    if not _OWNS["registered"]:
        return
    _OWNS["registered"] = False
    if _on_load in bpy.app.handlers.load_post:
        bpy.app.handlers.load_post.remove(_on_load)
    for scene in bpy.data.scenes:
        if LOCK_KEY in scene:
            _set_lock(scene, False)
    del bpy.types.Scene.bb_light
    for c in reversed(CLASSES):
        bpy.utils.unregister_class(c)


if __name__ == "__main__":
    register()
