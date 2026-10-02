bl_info = {
    "name": "BB Map",
    "author": "Beta Builder toolchain",
    "version": (2, 0, 0),
    "blender": (4, 2, 0),
    "location": "3D Viewport > Sidebar (N) > BB Map",
    "description": "City map control for Beta Builder GIS files: working areas, surrounding tiles, level of detail, layers",
    "category": "3D View",
}

# How the map works (files built by bb_city_build.py)
#   * The city is a grid of 2 km tiles. Every tile has its own scene and four level-of-detail collections:
#       LOD0 full · LOD1 medium · LOD2 low · LOD3 skyline (towers as boxes + small imagery).
#   * The master scene holds one instance per tile. This panel decides, per tile, whether it is shown and which
#     LOD collection it instances. Hidden tiles are not evaluated, so they cost memory on disk-load only, not viewport.
#   * Focus = the enabled working areas (script locations), or the scene camera for flights.
#     Tiles within "Surrounding tiles" of the focus are shown. Distance is measured in tiles, centre to centre,
#     so 1 = the four side neighbours, 2 = two out on each side plus the diagonals, and so on.
#     LOD: tiles within "Full detail" get LOD0; every "Detail falloff" tiles further out drops one level.
#   * Other districts can be forced on from the list; outside the radius they use "Forced tile detail".
# Works embedded in the map file (text block bb_map_layers.py) or installed as an add-on.

import math
import textwrap

import bpy

LAYERS = (
    ("satellite", "Satellite", "IMAGE_DATA"),
    ("building", "Buildings", "HOME"),
    ("highway", "Streets", "IPO_LINEAR"),
    ("railway", "Railway", "IPO_CONSTANT"),
    ("waterway", "Waterways", "MOD_OCEAN"),
    ("water", "Water bodies", "MATFLUID"),
    ("leisure", "Parks", "OUTLINER_OB_FORCE_FIELD"),
    ("landuse", "Land use", "MESH_GRID"),
    ("natural", "Natural", "WORLD"),
)
DEFAULT_ON = {"satellite", "building"}
LOD_NAMES = ("LOD0 full", "LOD1 medium", "LOD2 low", "LOD3 skyline")
FACE_BUDGET = 6_000_000
_busy = {"apply": False}


def _icon(name):
    try:
        return name if name in bpy.types.UILayout.bl_rna.functions["prop"].parameters["icon"].enum_items.keys() else "DOT"
    except Exception:
        return "DOT"


# ------------------------------------------------------------------------------------------------ core logic

def master_scene(context=None):
    scn = (context or bpy.context).scene
    if scn is not None and getattr(scn, "bb_city", None) and len(scn.bb_city.cells):
        return scn
    return next((s for s in bpy.data.scenes if len(s.bb_city.cells)), None)


def _tile_collections():
    out = {}
    for c in bpy.data.collections:
        cid, lod = c.get("bb_cell"), c.get("bb_lod")
        if cid is not None and lod is not None and c.get("bb_layer") is None:
            out[(cid, int(lod))] = c
    return out


def compute_lods(scene):
    """Return {cell_id: lod or None} for the current settings."""
    s = scene.bb_city
    cells = list(s.cells)
    focus = []
    if s.focus_mode == "CAMERA" and scene.camera is not None:
        p = scene.camera.matrix_world.translation
        focus = [(p.x / s.cell_size - 0.5, p.y / s.cell_size - 0.5)]
    else:
        ids = {a.cell for a in s.working_areas if a.enabled and a.cell}
        focus = [(c.i, c.j) for c in cells if c.cell_id in ids]
    result = {}
    eps = 1e-6
    for c in cells:
        d = min((math.hypot(c.i - fx, c.j - fy) for fx, fy in focus), default=float("inf"))
        lod = None
        if d <= s.view_radius + eps:
            lod = 0 if d <= s.full_radius + eps else min(3, 1 + int((d - s.full_radius - eps) // s.falloff))
        elif c.forced:
            lod = int(s.forced_lod)
        result[c.cell_id] = lod
    return result


def apply_layers(scene):
    s = scene.bb_city
    for c in bpy.data.collections:
        key = c.get("bb_layer")
        if key is None or c.get("bb_lod") is None:
            continue
        prefix = "detail_" if int(c["bb_lod"]) == 0 else "surround_"
        show = bool(getattr(s, prefix + key, key in DEFAULT_ON))
        if c.hide_viewport == show:
            c.hide_viewport = not show
        if c.hide_render == show:
            c.hide_render = not show


def apply_map(scene):
    if scene is None or _busy["apply"] or not len(scene.bb_city.cells):
        return
    _busy["apply"] = True
    try:
        s = scene.bb_city
        tiles = _tile_collections()
        lods = compute_lods(scene)
        empties = {o.get("bb_cell"): o for o in scene.collection.all_objects if o.get("bb_cell")}
        shown = faces = tex_px = 0
        per_lod = [0, 0, 0, 0]
        for c in s.cells:
            obj = empties.get(c.cell_id)
            want = lods.get(c.cell_id)
            coll = None
            if want is not None:
                for lod in list(range(want, 4)) + list(range(want - 1, -1, -1)):  # fall back to what was built
                    coll = tiles.get((c.cell_id, lod))
                    if coll is not None:
                        want = lod
                        break
            c.current_lod = -1 if coll is None else want
            if obj is None:
                continue
            if coll is None:
                if not obj.hide_viewport:
                    obj.hide_viewport = obj.hide_render = True
                continue
            if obj.instance_collection != coll:
                obj.instance_collection = coll
            if obj.hide_viewport:
                obj.hide_viewport = obj.hide_render = False
            shown += 1
            per_lod[want] += 1
            faces += int(coll.get("bb_faces", 0))
            prefix = "detail_" if want == 0 else "surround_"
            if getattr(s, prefix + "satellite"):
                tex_px += int(coll.get("bb_tex_px", 0))
        s.stat_tiles = shown
        s.stat_faces = faces
        s.stat_tex_mb = tex_px * 4 * 1.33 / 1e6
        s.stat_lods = " · ".join(f"L{i}: {n}" for i, n in enumerate(per_lod) if n) or "nothing shown"
        apply_layers(scene)
    finally:
        _busy["apply"] = False


def _update(self, context):
    apply_map(self.id_data if isinstance(self.id_data, bpy.types.Scene) else master_scene(context))


@bpy.app.handlers.persistent
def _frame_handler(scene, *_):
    try:
        if len(scene.bb_city.cells) and scene.bb_city.focus_mode == "CAMERA" and scene.bb_city.follow_camera:
            apply_map(scene)
    except Exception as e:
        print("BB Map frame update failed:", e)


# ------------------------------------------------------------------------------------------------ data

class BBCityArea(bpy.types.PropertyGroup):
    name: bpy.props.StringProperty()
    cell: bpy.props.StringProperty()
    script: bpy.props.StringProperty()
    enabled: bpy.props.BoolProperty(name="Working area", description="Use this script location as a focus",
                                    update=_update)


class BBCityCell(bpy.types.PropertyGroup):
    name: bpy.props.StringProperty()
    cell_id: bpy.props.StringProperty()
    region: bpy.props.StringProperty()
    scene_name: bpy.props.StringProperty()
    i: bpy.props.IntProperty()
    j: bpy.props.IntProperty()
    cx: bpy.props.FloatProperty()
    cy: bpy.props.FloatProperty()
    is_script: bpy.props.BoolProperty()
    forced: bpy.props.BoolProperty(name="Show", description="Show this district even outside the surrounding radius",
                                   update=_update)
    current_lod: bpy.props.IntProperty(default=-1)


def _layer_props(prefix, label):
    return {f"{prefix}{key}": bpy.props.BoolProperty(name=name, default=key in DEFAULT_ON, update=_update,
                                                     description=f"{name} on {label} tiles")
            for key, name, _ in LAYERS}


_settings_annotations = {
    "cells": bpy.props.CollectionProperty(type=BBCityCell),
    "cells_index": bpy.props.IntProperty(),
    "working_areas": bpy.props.CollectionProperty(type=BBCityArea),
    "cell_size": bpy.props.FloatProperty(default=2000.0),
    "focus_mode": bpy.props.EnumProperty(
        name="Focus", update=_update,
        items=(("AREAS", "Working areas", "Detail follows the enabled script locations"),
               ("CAMERA", "Scene camera", "Detail follows the scene camera (for drone and skyline flights)"))),
    "follow_camera": bpy.props.BoolProperty(
        name="Update every frame", default=True,
        description="In camera focus, recompute tiles on every frame change (playback and final renders)"),
    "view_radius": bpy.props.IntProperty(
        name="Surrounding tiles", min=0, soft_max=10, max=20, default=0, update=_update,
        description="How far out from the focus tiles are shown, in tiles (1 = side neighbours, 2 = two out plus diagonals)"),
    "full_radius": bpy.props.IntProperty(
        name="Full detail", min=0, max=6, default=0, update=_update,
        description="Tiles within this distance of the focus are shown at LOD0 (everything)"),
    "falloff": bpy.props.IntProperty(
        name="Detail falloff", min=1, max=6, default=1, update=_update,
        description="Every this many tiles beyond full detail, drop one level of detail"),
    "forced_lod": bpy.props.EnumProperty(
        name="Forced tile detail", default="2", update=_update,
        items=[(str(i), LOD_NAMES[i], "") for i in range(4)],
        description="Detail used for districts switched on in the list when they are outside the radius"),
    "stat_tiles": bpy.props.IntProperty(),
    "stat_faces": bpy.props.IntProperty(),
    "stat_tex_mb": bpy.props.FloatProperty(),
    "stat_lods": bpy.props.StringProperty(),
}
def _sea_update(self, context):
    for o in bpy.data.objects:
        if o.get("bb_sea"):
            o.hide_viewport = o.hide_render = not self.sea_plane


_settings_annotations["sea_plane"] = bpy.props.BoolProperty(
    name="Sea plane", default=True, update=_sea_update,
    description="A flat sea under the whole map so the Arabian Sea and harbour are not empty sky in skyline shots")
_settings_annotations.update(_layer_props("detail_", "full-detail"))
_settings_annotations.update(_layer_props("surround_", "surrounding"))
BBCitySettings = type("BBCitySettings", (bpy.types.PropertyGroup,), {"__annotations__": _settings_annotations})


# ------------------------------------------------------------------------------------------------ operators

PRESETS = {
    "LIGHT": ("Light", 1, 0, 1, "Working area plus its side neighbours; easy on a laptop"),
    "BALANCED": ("Balanced", 3, 0, 1, "Three tiles out, detail stepping down every tile"),
    "SKYLINE": ("Skyline", 8, 1, 2, "Wide skyline: full detail near the focus, slow falloff, far tiles as towers"),
}


class BB_OT_city_preset(bpy.types.Operator):
    bl_idname = "bb_city.preset"
    bl_label = "Map preset"
    bl_options = {"REGISTER", "UNDO"}
    preset: bpy.props.StringProperty()

    @classmethod
    def description(cls, context, props):
        return PRESETS.get(props.preset, ("", 0, 0, 0, ""))[4]

    def execute(self, context):
        scn = master_scene(context)
        _, radius, full, fall, _ = PRESETS[self.preset]
        s = scn.bb_city
        _busy["apply"] = True
        s.view_radius, s.full_radius, s.falloff = radius, full, fall
        _busy["apply"] = False
        apply_map(scn)
        return {"FINISHED"}


class BB_OT_city_refresh(bpy.types.Operator):
    bl_idname = "bb_city.refresh"
    bl_label = "Refresh map"
    bl_description = "Recompute which tiles show and at what detail (use after moving the camera)"

    def execute(self, context):
        apply_map(master_scene(context))
        return {"FINISHED"}


class BB_OT_city_set_many(bpy.types.Operator):
    bl_idname = "bb_city.set_many"
    bl_label = "Switch many"
    bl_options = {"REGISTER", "UNDO"}
    target: bpy.props.StringProperty()   # "areas" or a region name
    value: bpy.props.BoolProperty()

    def execute(self, context):
        scn = master_scene(context)
        s = scn.bb_city
        _busy["apply"] = True
        if self.target == "areas":
            for a in s.working_areas:
                a.enabled = self.value
        else:
            for c in s.cells:
                if not c.is_script and (self.target == "ALL" or c.region == self.target):
                    c.forced = self.value
        _busy["apply"] = False
        apply_map(scn)
        return {"FINISHED"}


class BB_OT_city_open_scene(bpy.types.Operator):
    bl_idname = "bb_city.open_scene"
    bl_label = "Open scene"
    bl_description = "Switch this window to the scene"
    scene_name: bpy.props.StringProperty()

    def execute(self, context):
        scn = bpy.data.scenes.get(self.scene_name)
        if scn is None or context.window is None:
            return {"CANCELLED"}
        context.window.scene = scn
        return {"FINISHED"}


class BB_OT_city_view_cell(bpy.types.Operator):
    bl_idname = "bb_city.view_cell"
    bl_label = "Look at tile"
    bl_description = "Centre the 3D view on this tile"
    cell_id: bpy.props.StringProperty()

    def execute(self, context):
        scn = master_scene(context)
        cell = next((c for c in scn.bb_city.cells if c.cell_id == self.cell_id), None)
        rv3d = getattr(context.space_data, "region_3d", None)
        if cell is None or rv3d is None:
            return {"CANCELLED"}
        rv3d.view_location = (cell.cx, cell.cy, 0.0)
        rv3d.view_distance = scn.bb_city.cell_size * 2.2
        return {"FINISHED"}


# ------------------------------------------------------------------------------------------------ UI

class BB_UL_city_cells(bpy.types.UIList):
    def draw_item(self, context, layout, data, item, icon, active_data, active_propname, index):
        row = layout.row(align=True)
        row.prop(item, "forced", text="")
        row.label(text=item.name)
        row.label(text="—" if item.current_lod < 0 else f"L{item.current_lod}")
        row.operator("bb_city.view_cell", text="", icon="VIEWZOOM", emboss=False).cell_id = item.cell_id
        row.operator("bb_city.open_scene", text="", icon="SCENE_DATA", emboss=False).scene_name = item.scene_name

    def filter_items(self, context, data, propname):
        items = getattr(data, propname)
        helper = bpy.types.UI_UL_list
        flags = helper.filter_items_by_name(self.filter_name, self.bitflag_filter_item, items, "name", reverse=False)
        if not flags:
            flags = [self.bitflag_filter_item] * len(items)
        flags = [0 if it.is_script else f for f, it in zip(flags, items)]
        return flags, helper.sort_items_by_name(items, "name")


class _Base:
    bl_space_type = "VIEW_3D"
    bl_region_type = "UI"
    bl_category = "BB Map"

    @classmethod
    def poll(cls, context):
        return master_scene(context) is not None


class BB_PT_city(_Base, bpy.types.Panel):
    bl_label = "Mumbai Map"

    def draw(self, context):
        layout = self.layout
        scn = master_scene(context)
        s = scn.bb_city
        if context.scene != scn:
            layout.operator("bb_city.open_scene", text=f"Back to {scn.name}", icon="WORLD").scene_name = scn.name
            layout.label(text="Settings act on the master scene.")
        box = layout.box()
        heavy = s.stat_faces > FACE_BUDGET
        box.label(text=f"{s.stat_tiles} tiles shown", icon="ERROR" if heavy else "INFO")
        box.label(text=s.stat_lods)
        box.label(text=f"~{s.stat_faces / 1e6:.2f} M faces · satellite ~{s.stat_tex_mb:.0f} MB")
        if heavy:
            box.label(text="Heavy for a 16 GB laptop: shrink the radius or raise falloff")
        layout.row().prop(s, "focus_mode", expand=True)
        if s.focus_mode == "CAMERA":
            row = layout.row(align=True)
            row.prop(s, "follow_camera")
            row.operator("bb_city.refresh", text="", icon="FILE_REFRESH")
        row = layout.row(align=True)
        for key, (label, *_rest) in PRESETS.items():
            row.operator("bb_city.preset", text=label).preset = key
        col = layout.column(align=True)
        col.prop(s, "view_radius")
        col.prop(s, "full_radius")
        col.prop(s, "falloff")
        layout.label(text="Detail: L0 full · L1 medium · L2 low · L3 towers", icon="MOD_DECIM")


class BB_PT_city_areas(_Base, bpy.types.Panel):
    bl_label = "Working areas (script)"
    bl_parent_id = "BB_PT_city"

    def draw(self, context):
        layout = self.layout
        scn = master_scene(context)
        s = scn.bb_city
        cells = {c.cell_id: c for c in s.cells}
        row = layout.row(align=True)
        op = row.operator("bb_city.set_many", text="All on")
        op.target, op.value = "areas", True
        op = row.operator("bb_city.set_many", text="All off")
        op.target, op.value = "areas", False
        for a in s.working_areas:
            row = layout.row(align=True)
            row.prop(a, "enabled", text=a.name)
            cell = cells.get(a.cell)
            if cell is not None:
                row.operator("bb_city.view_cell", text="", icon="VIEWZOOM").cell_id = cell.cell_id
                row.operator("bb_city.open_scene", text="", icon="SCENE_DATA").scene_name = cell.scene_name


class BB_PT_city_other(_Base, bpy.types.Panel):
    bl_label = "Other districts"
    bl_parent_id = "BB_PT_city"
    bl_options = {"DEFAULT_CLOSED"}

    def draw(self, context):
        layout = self.layout
        s = master_scene(context).bb_city
        layout.label(text="Tick to show a district anywhere (L = detail now)")
        layout.template_list("BB_UL_city_cells", "", s, "cells", s, "cells_index", rows=8)
        layout.prop(s, "forced_lod")
        regions = sorted({c.region for c in s.cells if c.region})
        for region in regions:
            row = layout.row(align=True)
            row.label(text=region)
            op = row.operator("bb_city.set_many", text="All")
            op.target, op.value = region, True
            op = row.operator("bb_city.set_many", text="None")
            op.target, op.value = region, False


class BB_PT_city_layers(_Base, bpy.types.Panel):
    bl_label = "Layers"
    bl_parent_id = "BB_PT_city"

    def draw(self, context):
        layout = self.layout
        scn = master_scene(context)
        s = scn.bb_city
        col = layout.column(align=True)
        head = col.split(factor=0.6, align=True)
        head.label(text="Layer")
        pair = head.row(align=True)
        pair.label(text="Full")
        pair.label(text="Around")
        for key, name, icon in LAYERS:
            row = col.split(factor=0.6, align=True)
            row.label(text=name, icon=_icon(icon))
            pair = row.row(align=True)
            pair.prop(s, f"detail_{key}", text="")
            pair.prop(s, f"surround_{key}", text="")
        layout.prop(s, "sea_plane", icon=_icon("MATFLUID"))
        if "bb_sat_on_buildings" in scn.keys():
            layout.prop(scn, '["bb_sat_on_buildings"]', text="Satellite on buildings", slider=True)
        credit = scn.get("bb_imagery_credit")
        if credit:
            box = layout.box()
            box.scale_y = 0.7
            for line in textwrap.wrap(str(credit), 42):
                box.label(text=line)


CLASSES = (BBCityArea, BBCityCell, BBCitySettings, BB_OT_city_preset, BB_OT_city_refresh, BB_OT_city_set_many,
           BB_OT_city_open_scene, BB_OT_city_view_cell, BB_UL_city_cells, BB_PT_city, BB_PT_city_areas,
           BB_PT_city_other, BB_PT_city_layers)


def register():
    if hasattr(bpy.types.Scene, "bb_city"):
        return  # already registered (add-on and embedded copy both present)
    for cls in CLASSES:
        bpy.utils.register_class(cls)
    bpy.types.Scene.bb_city = bpy.props.PointerProperty(type=BBCitySettings)
    if _frame_handler not in bpy.app.handlers.frame_change_pre:
        bpy.app.handlers.frame_change_pre.append(_frame_handler)


def unregister():
    if not hasattr(bpy.types.Scene, "bb_city"):
        return
    if _frame_handler in bpy.app.handlers.frame_change_pre:
        bpy.app.handlers.frame_change_pre.remove(_frame_handler)
    del bpy.types.Scene.bb_city
    for cls in reversed(CLASSES):
        bpy.utils.unregister_class(cls)


if __name__ == "__main__":
    register()
