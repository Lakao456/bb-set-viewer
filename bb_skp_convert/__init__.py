# SPDX-License-Identifier: GPL-2.0-or-later
"""BB SketchUp Convert - turn a SketchUp .skp into a Blender .blend, one to one, then make it
lighter and tidy it up.

This file is two things at once, on purpose:

  * **A command-line tool.** Run it with Blender and it does the work. This is how a conversion
    is actually done, and it is what the guide tells an assistant to use.
  * **An add-on in the BB family.** Installed from the BB extensions repository, so it updates
    itself. Whoever is converting a set always has the current version, and an assistant can
    read this very file to see exactly what it will do before running it - the point being that
    every model the art team sends is different, and the assistant is expected to read, adapt
    and decide, not to trust a black box.

Three phases, and the second one does not start on its own.

  PHASE 1 - import and audit (safe, changes nothing in the model)

      blender -b --factory-startup --python <this file> -- audit --skp "<file>.skp"

  PHASE 2 - optimise, only the steps a human asked for

      blender -b "<file>.blend" --python <this file> -- optimise --share --join

  PHASE 3 - organise it and give it a camera

      blender -b "<file>_optimised.blend" --python <this file> -- prepare

Every step in phases 2 and 3 is checked after it runs: the triangle count, the bounding box,
and a few thousand rays fired through the set that record where each one lands, which way the
surface faces and which material is on it. If a step changes any of that, the step is undone
and the file is saved without it. The model always wins over the optimisation.

Never does: cleaning, decimating, rescaling, re-origining, renaming, deleting, recalculating
normals, or editing materials.

Blender 4.2 or newer with the SketchUp Importer add-on. Nothing else to install - NumPy ships
with Blender.
"""
bl_info = {
    "name": "BB SketchUp Convert",
    "author": "Beta Builder toolchain",
    "version": (1, 0, 0),
    "blender": (4, 2, 0),
    "location": "3D Viewport > Sidebar (N) > BB Convert",
    "description": "Import a SketchUp .skp one to one, audit it, optimise it and organise it",
    "category": "Import-Export",
}

import argparse
import hashlib
import json
import math
import os
import random
import sys
import time
from pathlib import Path

import addon_utils
import bpy
import numpy as np
from mathutils import Matrix, Vector

WORLD_NAME = "World Light"
WORLD_COLOUR = (0.55, 0.60, 0.68, 1.0)      # a neutral overcast sky, not a look
WORLD_STRENGTH = 2.0
PROBE_SEED = 20261002
JOIN_MAX_FACES = 200                        # baking a small object costs almost no data
JOIN_CELL = 4.0                             # metres


def say(line=""):
    print("[skp2blend] %s" % line, flush=True)


# ---------------------------------------------------------------------------
# shared helpers
# ---------------------------------------------------------------------------

def mesh_objects():
    return [o for o in bpy.context.scene.objects if o.type == "MESH" and o.data is not None]


def triangles(objs=None):
    total = 0
    for o in (objs if objs is not None else mesh_objects()):
        n = len(o.data.polygons)
        if not n:
            continue
        lt = np.empty(n, dtype=np.int32)
        o.data.polygons.foreach_get("loop_total", lt)
        total += int(np.maximum(lt - 2, 0).sum())
    return total


def faces(objs=None):
    return sum(len(o.data.polygons) for o in (objs if objs is not None else mesh_objects()))


def world_bbox(objs=None):
    lo = np.full(3, np.inf)
    hi = np.full(3, -np.inf)
    for o in (objs if objs is not None else mesh_objects()):
        if not len(o.data.polygons):
            continue
        m = np.array(o.matrix_world.to_4x4())
        pts = np.array([list(c) for c in o.bound_box])
        w = pts @ m[:3, :3].T + m[:3, 3]
        lo = np.minimum(lo, w.min(axis=0))
        hi = np.maximum(hi, w.max(axis=0))
    if not np.isfinite(lo).all():
        return np.zeros(3), np.zeros(3)
    return lo, hi


def object_bbox_centre(o):
    m = np.array(o.matrix_world.to_4x4())
    pts = np.array([list(c) for c in o.bound_box])
    w = pts @ m[:3, :3].T + m[:3, 3]
    return (w.min(axis=0) + w.max(axis=0)) * 0.5


def probe(n_rays):
    """Fire the same rays through the set every time and record what they hit.

    Blender returns the point, the surface normal and the face, so this measures the set as
    it is actually drawn - it does not depend on object names, object count or any maths of
    ours. Same seed, same rays, so ray number 7 is the same ray in every file."""
    scene = bpy.context.scene
    dg = bpy.context.evaluated_depsgraph_get()
    lo, hi = world_bbox()
    centre = Vector(((lo + hi) * 0.5).tolist())
    radius = float(np.linalg.norm(hi - lo)) or 1.0
    rng = random.Random(PROBE_SEED)
    rows = []
    for _ in range(n_rays):
        z = rng.uniform(-1.0, 1.0)
        t = rng.uniform(0.0, 2.0 * math.pi)
        r = math.sqrt(max(0.0, 1.0 - z * z))
        origin = centre + Vector((r * math.cos(t), r * math.sin(t), z)) * (radius * 0.75)
        target = Vector((rng.uniform(float(lo[i]), float(hi[i])) for i in range(3)))
        d = target - origin
        if d.length < 1e-9:
            rows.append(None)
            continue
        hit, loc, nor, idx, obj, _m = scene.ray_cast(dg, origin, d.normalized())
        if not hit or obj is None:
            rows.append(None)
            continue
        mat = ""
        try:
            me = obj.data
            if me.materials:
                slot = me.materials[me.polygons[idx].material_index]
                mat = slot.name if slot else ""
        except Exception:
            mat = "?"
        rows.append((round(loc.x, 4), round(loc.y, 4), round(loc.z, 4),
                     round(nor.x, 3), round(nor.y, 3), round(nor.z, 3), mat))
    return rows


def compare_probes(before, after):
    """How many rays now land somewhere else, face the other way, or hit another material."""
    out = dict(moved=0, turned=0, flipped=0, material=0, appeared=0, vanished=0,
               worst_mm=0.0, worst_deg=0.0, compared=0)
    for x, y in zip(before, after):
        if x is None and y is None:
            continue
        if x is None:
            out["appeared"] += 1
            continue
        if y is None:
            out["vanished"] += 1
            continue
        out["compared"] += 1
        d = math.dist(x[:3], y[:3]) * 1000.0
        out["worst_mm"] = max(out["worst_mm"], d)
        if d > 0.5:                       # half a millimetre: float32 noise lives below this
            out["moved"] += 1
        dot = max(-1.0, min(1.0, sum(x[3 + i] * y[3 + i] for i in range(3))))
        ang = math.degrees(math.acos(dot))
        out["worst_deg"] = max(out["worst_deg"], ang)
        if ang > 5.0:
            out["turned"] += 1
        if ang > 90.0:
            out["flipped"] += 1
        if x[6] != y[6]:
            out["material"] += 1
    return out


def probe_is_clean(c, rays):
    """A handful of rays can legitimately differ: a ray that grazes an edge, or that lands on
    one of two faces sitting in exactly the same place. Anything more is a real change."""
    allowed = max(5, int(rays * 0.001))
    return (c["flipped"] == 0 and c["turned"] <= allowed and c["moved"] <= allowed
            and c["material"] <= allowed and c["appeared"] <= allowed
            and c["vanished"] <= allowed)


def keep_unused_datablocks():
    """Blender does not save materials or images that nothing uses, so a material the art team
    made but has not put on anything would quietly disappear. A fake user keeps them."""
    kept = 0
    for coll in (bpy.data.materials, bpy.data.images):
        for b in coll:
            if b.users == 0 and not b.use_fake_user:
                b.use_fake_user = True
                kept += 1
    return kept


def add_world_light(strength=WORLD_STRENGTH):
    scene = bpy.context.scene
    world = scene.world
    if world is None:
        world = bpy.data.worlds.new(WORLD_NAME)
        scene.world = world
    world.use_nodes = True
    bg = next((n for n in world.node_tree.nodes if n.type == "BACKGROUND"), None)
    if bg is None:
        bg = world.node_tree.nodes.new("ShaderNodeBackground")
        out = next((n for n in world.node_tree.nodes if n.type == "OUTPUT_WORLD"), None) \
            or world.node_tree.nodes.new("ShaderNodeOutputWorld")
        world.node_tree.links.new(bg.outputs[0], out.inputs[0])
    bg.inputs[0].default_value = WORLD_COLOUR
    bg.inputs[1].default_value = strength
    return world.name


# ---------------------------------------------------------------------------
# PHASE 1 - import and audit
# ---------------------------------------------------------------------------

def enable_importer():
    # default_set=True registers the add-on in this session's preferences. The importer reads
    # its own preferences entry while loading, so without this it fails with a KeyError on a
    # --factory-startup run.
    addon_utils.enable("sketchup_importer", default_set=True, persistent=False)
    # hasattr on bpy.ops is not a real check - it answers True for operators that do not exist.
    # Asking the operator to poll is: a missing one raises instead. This matters on a Mac, where
    # Blender 5.2 cannot load the importer at all and the only honest answer is "wrong Blender".
    try:
        bpy.ops.import_scene.skp.poll()
        return True
    except Exception:
        return False


def do_import(skp):
    """Import the .skp as it is.

    max_instance is set absurdly high on purpose. A component placed more often than that
    number sends the importer down a path written for Blender 2.7x: it raises AttributeError
    on 'Object has no attribute layers' and the import dies. Patching that path is possible,
    but it then draws MORE geometry than the model has (measured: 148,573 extra faces on a
    real set), so it is avoided entirely. Every component is imported as real geometry, and
    the 'share identical meshes' step in phase 2 gets the memory back safely."""
    say("importing %s (%.0f MB) - a big set takes a few minutes" % (skp.name, skp.stat().st_size / 1e6))
    t = time.time()
    bpy.ops.import_scene.skp(filepath=str(skp), reuse_material=True, scenes_as_camera=True,
                             max_instance=10 ** 9)
    say("imported in %.0f s" % (time.time() - t))


def hidden_geometry(skp):
    """List what is hidden in the .skp, because the importer skips hidden things silently.

    This is the single biggest way a set arrives incomplete without anyone noticing: on one
    real set the heaviest object in the whole file - a 2.19 million face decoration - was
    hidden, so it simply was not there afterwards.

    Each component definition is read once. Following every placement separately is
    exponential on a big set and never finishes."""
    try:
        from sketchup_importer import sketchup
    except Exception as exc:
        say("note: could not read the .skp directly to look for hidden parts (%s)" % exc)
        return []
    model = sketchup.Model.from_file(str(skp))
    defs = {c.name: c for c in model.component_definitions}
    rows, seen = [], set()

    def scan(ents, hidden_above):
        n = sum(1 for _ in ents.faces)
        for g in ents.groups:
            h = hidden_above or g.hidden
            f = scan(g.entities, h)
            if h and f:
                rows.append(("group " + (g.name or "no name"), f))
            n += f
        for i in ents.instances:
            d = i.definition.name
            if hidden_above or i.hidden:
                rows.append((d, -1))
            if d not in seen and d in defs:
                seen.add(d)
                scan(defs[d].entities, False)
        return n

    try:
        scan(model.entities, False)
    finally:
        model.close()
    return rows


def audit_report(skp=None):
    """Everything that decides whether this set will open on a laptop."""
    objs = mesh_objects()
    lo, hi = world_bbox(objs)
    per_obj = sorted((len(o.data.polygons) for o in objs), reverse=True)

    imgs = [(i.size[0], i.size[1], i.name) for i in bpy.data.images if i.size[0] and i.size[1]]
    tex_mb = sum(w * h * 4 for w, h, _ in imgs) / 1e6

    # how much of the mesh data is a duplicate of other mesh data
    groups = {}
    for me in bpy.data.meshes:
        if not me.users or not len(me.polygons):
            continue
        groups.setdefault(mesh_signature(me), []).append(me)
    dupes = sum(len(v) - 1 for v in groups.values() if len(v) > 1)
    dupe_faces = sum(sum(len(m.polygons) for m in v[1:]) for v in groups.values() if len(v) > 1)

    small = [n for n in per_obj if n < JOIN_MAX_FACES]
    heavy = [n for n in per_obj if n >= 10000]

    rec = {
        "source": skp.name if skp else "",
        "blend": os.path.basename(bpy.data.filepath),
        "blender": bpy.app.version_string,
        "objects": len(objs),
        "meshes": len(bpy.data.meshes),
        "faces": faces(objs),
        "triangles": triangles(objs),
        "materials": len(bpy.data.materials),
        "images": len(imgs),
        "cameras": sum(1 for o in bpy.context.scene.objects if o.type == "CAMERA"),
        "size_m": [round(float(hi[i] - lo[i]), 2) for i in range(3)],
        "texture_mb": round(tex_mb),
        "duplicate_meshes": dupes,
        "duplicate_faces": dupe_faces,
        "small_objects": len(small),
        "small_object_faces": sum(small),
        "heavy_objects": len(heavy),
        "heavy_object_faces": sum(heavy),
        "hidden": hidden_geometry(skp) if skp else [],
    }
    return rec


def mesh_signature(me):
    nv, nl, npo = len(me.vertices), len(me.loops), len(me.polygons)
    lv = np.empty(nl, dtype=np.int32)
    me.loops.foreach_get("vertex_index", lv)
    st = np.empty(npo, dtype=np.int32)
    me.polygons.foreach_get("loop_start", st)
    mi = np.empty(npo, dtype=np.int32)
    me.polygons.foreach_get("material_index", mi)
    h = hashlib.blake2b(digest_size=16)
    for arr in (lv, st, mi):
        h.update(arr.tobytes())
    h.update(repr([m.name if m else "" for m in me.materials]).encode("utf-8"))
    return (nv, npo, nl, me.uv_layers.active is None, h.hexdigest())


def print_audit(rec):
    say()
    say("=" * 70)
    say("WHAT IS IN THIS SET")
    say("=" * 70)
    say("Objects          : %d (pieces of geometry; cameras are counted separately)"
        % rec["objects"])
    say("Triangles        : %d" % rec["triangles"])
    say("Materials        : %d" % rec["materials"])
    say("Textures         : %d, %d MB of picture data" % (rec["images"], rec["texture_mb"]))
    say("SketchUp cameras : %d" % rec["cameras"])
    say("Size             : %.1f x %.1f x %.1f metres" % tuple(rec["size_m"]))
    if rec.get("hidden"):
        say("HIDDEN IN SKETCHUP - these did NOT come across")
        say(" The importer skips anything hidden, with no warning. If any of these belong in")
        say(" the set, unhide them in SketchUp, save, and convert again.")
        for name, f in rec["hidden"][:12]:
            say("   %-46s %s" % (name[:46], "%d faces" % f if f > 0 else "a whole component"))
        if len(rec["hidden"]) > 12:
            say("   ... and %d more" % (len(rec["hidden"]) - 12))
        say()
    say()
    say("WHAT WILL MAKE IT SLOW")
    heavy_tri = rec["triangles"]
    if heavy_tri > 2_000_000:
        say(" * %d triangles. Over about 2 million a laptop starts to struggle." % heavy_tri)
    if rec["objects"] > 5000:
        say(" * %d separate objects. Blender pays for every one of them, every frame."
            % rec["objects"])
    if rec["duplicate_meshes"]:
        say(" * %d of the shapes are exact copies of another shape, holding %d faces. The file"
            % (rec["duplicate_meshes"], rec["duplicate_faces"]))
        say("   is storing the same thing many times over.")
    if rec["small_objects"] > 1000:
        say(" * %d objects are tiny (under %d faces) and hold only %d faces between them."
            % (rec["small_objects"], JOIN_MAX_FACES, rec["small_object_faces"]))
    if rec["texture_mb"] > 300:
        say(" * %d MB of textures. They all have to fit in the graphics memory."
            % rec["texture_mb"])
    if rec["heavy_objects"]:
        share = round(100.0 * rec["heavy_object_faces"] / max(1, rec["faces"]))
        if rec["heavy_objects"] == 1:
            say(" * one very heavy object holds %d faces on its own - about %d%% of the set."
                % (rec["heavy_object_faces"], share))
        else:
            say(" * %d very heavy objects hold %d faces between them - about %d%% of the set."
                % (rec["heavy_objects"], rec["heavy_object_faces"], share))
        say("   That is where the weight really is, and it cannot be reduced without changing")
        say("   the model.")
    say()


def write_report(path, rec, steps=None):
    lines = [
        "# %s - conversion report" % (rec.get("source") or rec.get("blend")),
        "",
        "Blender file: %s" % rec.get("blend", ""),
        "Blender: %s" % rec.get("blender", ""),
        "Written: %s" % time.strftime("%Y-%m-%d %H:%M"),
        "",
        "## The set",
        "",
        "| | |",
        "|---|---|",
        "| Objects | %d |" % rec["objects"],
        "| Triangles | %d |" % rec["triangles"],
        "| Materials | %d |" % rec["materials"],
        "| Textures | %d (%d MB) |" % (rec["images"], rec["texture_mb"]),
        "| SketchUp cameras | %d |" % rec["cameras"],
        "| Size | %.1f x %.1f x %.1f m |" % tuple(rec["size_m"]),
        "",
    ]
    if rec.get("hidden"):
        lines += ["## Hidden in SketchUp, so NOT in this file", ""]
        for name, f in rec["hidden"][:30]:
            lines.append("- %s - %s" % (name, "%d faces" % f if f > 0 else "a whole component"))
        lines += ["", "The importer skips hidden groups and components silently. If any of these",
                  "belong in the set, unhide them in SketchUp, save, and convert again.", ""]
    if steps:
        lines += ["## What was done", ""]
        for s in steps:
            lines.append("- %s" % s)
        lines.append("")
    lines += [
        "## Not done, on purpose",
        "",
        "No cleaning, joining of large objects, decimating, rescaling, re-origining, renaming,",
        "deleting, normal recalculation or material editing. Where geometry was touched at all,",
        "it was checked afterwards by ray casts and triangle counts, and undone if anything moved.",
        "",
    ]
    Path(path).write_text("\n".join(lines), encoding="utf-8")


# ---------------------------------------------------------------------------
# PHASE 2 - the optimisation steps
# ---------------------------------------------------------------------------

def mesh_arrays(me):
    nv, nl, npo = len(me.vertices), len(me.loops), len(me.polygons)
    co = np.empty(nv * 3, dtype=np.float64)
    me.vertices.foreach_get("co", co)
    lv = np.empty(nl, dtype=np.int32)
    me.loops.foreach_get("vertex_index", lv)
    st = np.empty(npo, dtype=np.int32)
    me.polygons.foreach_get("loop_start", st)
    mi = np.empty(npo, dtype=np.int32)
    me.polygons.foreach_get("material_index", mi)
    uv = None
    if me.uv_layers.active is not None:
        uv = np.empty(nl * 2, dtype=np.float64)
        me.uv_layers.active.data.foreach_get("uv", uv)
    return co, uv


def step_share(_args):
    """Store identical shapes once. Nothing moves; the objects simply point at one copy."""
    objs = mesh_objects()
    buckets = {}
    for me in {o.data for o in objs}:
        buckets.setdefault(mesh_signature(me), []).append(me)
    remap = {}
    for group in buckets.values():
        if len(group) < 2:
            continue
        cache = {me: mesh_arrays(me) for me in group}
        keepers = []
        for me in group:
            x = cache[me]
            for k in keepers:
                y = cache[k]
                same_uv = x[1] is None or np.allclose(x[1], y[1], atol=1e-6, rtol=0)
                if same_uv and np.allclose(x[0], y[0], atol=1e-6, rtol=0):
                    remap[me] = k
                    break
            else:
                keepers.append(me)
    before = len(bpy.data.meshes)
    for o in objs:
        if o.data in remap:
            o.data = remap[o.data]
    for me in list(bpy.data.meshes):
        if me.users == 0:
            bpy.data.meshes.remove(me)
    return "identical shapes stored once: %d shapes merged, mesh data %d -> %d" \
        % (len(remap), before, len(bpy.data.meshes))


def step_join(args, skip_mirrored=False):
    """Join the small objects, per patch of the set, so Blender has fewer to push around.

    Heavy objects are left alone: swallowing a 300,000-face prop into a block would break the
    viewport's ability to skip what is off screen, which is the opposite of the point."""
    scene = bpy.context.scene
    cell = args.cell
    candidates = []
    for o in mesh_objects():
        if o.modifiers or o.parent or o.children or o.instance_type != "NONE":
            continue
        n = len(o.data.polygons)
        if n == 0 or n >= args.max_faces:
            continue
        if skip_mirrored and o.matrix_world.determinant() < 0:
            continue
        candidates.append(o)
    if not candidates:
        return "join: nothing small enough to join"

    cells = {}
    for o in candidates:
        c = object_bbox_centre(o)       # where the geometry IS, not where its origin sits
        cells.setdefault((int(c[0] // cell), int(c[1] // cell), int(c[2] // cell)), []).append(o)

    win = bpy.context.window_manager.windows[0] if bpy.context.window_manager.windows else None
    before = len(scene.objects)
    made = mirrored = 0
    for (cx, cy, cz), parts in sorted(cells.items()):
        if len(parts) < 2:
            continue
        for o in parts:
            if o.data.users > 1:
                o.data = o.data.copy()      # never touch a mesh another object still uses
            if o.matrix_world.determinant() < 0:
                mirrored += 1
                # not flipped by hand: Blender's join already reverses a mirrored source, and
                # flipping first turns it inside out (measured on a real set)
        col = parts[0].users_collection[0] if parts[0].users_collection else scene.collection
        name = "Merged %+04d %+04d %+03d" % (cx, cy, cz)
        target = bpy.data.objects.new(name, bpy.data.meshes.new(name))
        col.objects.link(target)
        # a translation only: a mirrored target would make the join flip faces twice
        target.matrix_world = Matrix.Translation(
            ((cx + 0.5) * cell, (cy + 0.5) * cell, (cz + 0.5) * cell))
        target["merged_parts"] = len(parts)
        sel = [target] + parts
        override = dict(active_object=target, object=target,
                        selected_objects=sel, selected_editable_objects=sel)
        if win is not None:
            override["window"] = win
        with bpy.context.temp_override(**override):
            bpy.ops.object.join()
        made += 1
    for me in list(bpy.data.meshes):
        if me.users == 0:
            bpy.data.meshes.remove(me)
    return "small objects joined into %d groups%s: objects %d -> %d (%d of the parts were mirrored)" \
        % (made, " (mirrored parts left out)" if skip_mirrored else "",
           before, len(scene.objects), mirrored)


def step_cap(args):
    """Shrink oversized textures. This DOES change how the set looks, so it is never automatic."""
    cap = args.cap
    done = saved = 0
    for im in bpy.data.images:
        w, h = im.size[0], im.size[1]
        if not w or not h or max(w, h) <= cap:
            continue
        s = cap / float(max(w, h))
        nw, nh = max(1, int(w * s)), max(1, int(h * s))
        saved += (w * h - nw * nh) * 4
        im.scale(nw, nh)
        done += 1
    return "textures capped at %d px: %d resized, about %d MB less picture data" \
        % (cap, done, saved / 1e6)



# ---------------------------------------------------------------------------
# PHASE 3 - organise the set and give it a camera
# ---------------------------------------------------------------------------

FLOWER_WORDS = ("flower", "rose", "bloom", "blossom", "daisy", "jasmine", "pollen", "leaf",
                "leaves", "petal", "garland", "mala", "trail", "canopy", "branch", "ivy",
                "vdw_", "bud", "orchid", "marigold")
STRUCTURE_M = 4.0          # anything this big in X or Y is taken to be part of the building
HEAVY_FACES = 10000        # the props worth being able to switch off on their own
FAMILY_MIN = 20            # a name family needs this many objects to get its own collection
ZONE_MIN = 300             # more nameless objects than this and they are split by area


def name_family(name):
    """Strip Blender's .001 suffixes, SketchUp's #123 and trailing numbers, so that
    'RoseLeaf-2016.047' and 'RoseLeaf-2016' land in the same family."""
    import re
    n = re.sub(r"\.\d{3}$", "", name)
    n = re.sub(r"(_Defintion|_Definition)$", "", n)
    n = re.sub(r"#\d+$", "", n)
    n = re.sub(r"[-_ ]?\d+$", "", n)
    return n.strip(" -_") or "Unnamed"


def new_collection(name, parent):
    c = bpy.data.collections.get(name)
    if c is None:
        c = bpy.data.collections.new(name)
    if c.name not in parent.children:
        parent.children.link(c)
    return c


def move_to(ob, coll):
    for c in list(ob.users_collection):
        c.objects.unlink(ob)
    coll.objects.link(ob)


def drop_art_cameras():
    """The art team's SketchUp scenes arrive as cameras. They are reference, not shots, and
    the raw import keeps them - the file we hand on gets one camera of our own instead."""
    gone = []
    for o in list(bpy.data.objects):
        if o.type == "CAMERA":
            gone.append(o.name)
            data = o.data
            bpy.data.objects.remove(o)
            if data and data.users == 0:
                bpy.data.cameras.remove(data)
    for c in list(bpy.data.collections):
        if not c.objects and not c.children and ("Scenes" in c.name or "Camera" in c.name):
            bpy.data.collections.remove(c)
    return gone


def best_camera_spot():
    """Somewhere inside the set with room to see, rather than the middle of a wall.

    Tries a grid of positions at eye height, fires eight rays out from each, and keeps the one
    with the most space around it. Returns the position and the direction of the longest view."""
    scene = bpy.context.scene
    dg = bpy.context.evaluated_depsgraph_get()
    lo, hi = world_bbox()
    best = None
    for fx in (0.25, 0.375, 0.5, 0.625, 0.75):
        for fy in (0.25, 0.375, 0.5, 0.625, 0.75):
            x = float(lo[0] + (hi[0] - lo[0]) * fx)
            y = float(lo[1] + (hi[1] - lo[1]) * fy)
            # the floor HERE, not the lowest point in the file: a single stray object below
            # the set would otherwise put the camera metres up in the air
            down = scene.ray_cast(dg, Vector((x, y, float(hi[2]) + 1.0)), Vector((0.0, 0.0, -1.0)))
            if not down[0]:
                continue
            pos = Vector((x, y, down[1].z + 1.6))
            if pos.z > float(hi[2]):
                continue
            dists = []
            for k in range(8):
                ang = k * math.pi / 4.0
                d = Vector((math.cos(ang), math.sin(ang), 0.0))
                hit, loc, _n, _i, _o, _m = scene.ray_cast(dg, pos, d)
                dists.append((loc - pos).length if hit else 1e4)
            score = min(dists)
            if score < 0.4:                 # standing inside something
                continue
            if best is None or score > best[0]:
                k = max(range(8), key=lambda i: dists[i])
                ang = k * math.pi / 4.0
                best = (score, pos, Vector((math.cos(ang), math.sin(ang), -0.08)))
    if best is None:            # no floor found anywhere: fall back to the middle of the set
        centre = (lo + hi) * 0.5
        return Vector((float(centre[0]), float(lo[1]), float(centre[2]))), \
            Vector((0.0, 1.0, -0.08)), 0.0
    return best[1], best[2], best[0]


def add_bb_camera(parent):
    """One camera, named the way BB Set Viewer expects, pointing somewhere useful."""
    pos, look, clearance = best_camera_spot()
    data = bpy.data.cameras.new("BB Cam 01")
    data.lens = 24.0
    data.clip_start = 0.05
    data.clip_end = 500.0
    data.dof.use_dof = False
    data.dof.focus_distance = 3.0
    data.dof.aperture_fstop = 2.8
    cam = bpy.data.objects.new("BB Cam 01", data)
    coll = new_collection("Cameras", parent)      # the name the add-on makes and reuses
    coll.objects.link(cam)
    cam.rotation_mode = "XYZ"
    cam.location = pos
    cam.rotation_euler = look.to_track_quat("-Z", "Y").to_euler("XYZ")
    bpy.context.scene.camera = cam
    return cam, clearance


_ZONES = {}


def zone_of(ob):
    """Which patch of the set this object sits in. A 3 x 3 grid over the whole scene, worked
    out once, so the same label means the same place in every collection."""
    if not _ZONES:
        lo, hi = world_bbox()
        _ZONES["lo"], _ZONES["step"] = lo, [max(1e-6, (hi[i] - lo[i]) / 3.0) for i in range(2)]
    c = object_bbox_centre(ob)
    ix = min(2, max(0, int((c[0] - _ZONES["lo"][0]) // _ZONES["step"][0])))
    iy = min(2, max(0, int((c[1] - _ZONES["lo"][1]) // _ZONES["step"][1])))
    return "Zone %s%d" % ("ABC"[ix], iy + 1)


def cmd_prepare(args):
    if not bpy.data.filepath:
        say("ERROR: open the .blend on the command line before --python.")
        return 2
    src = Path(bpy.data.filepath)
    out = Path(args.out).expanduser().resolve() if args.out else \
        src.with_name(src.stem + "_organised.blend")

    base_tris = triangles()
    base_probe = probe(args.rays)
    say("before: %d objects, %d triangles, %d of %d rays hit something"
        % (len(bpy.context.scene.objects), base_tris,
           sum(1 for r in base_probe if r), args.rays))

    gone = drop_art_cameras()
    say("removed %d of the art team's cameras: %s"
        % (len(gone), ", ".join(gone[:6]) + (" ..." if len(gone) > 6 else "")))

    root = bpy.context.scene.collection
    objs = mesh_objects()

    groups = {
        "00 Lighting Rig": [],
        "02 Structure": [],
        "03 Heavy Props": [],
        "04 Flowers and Garlands": [],
        "05 Props": [],
        "06 Merged Clutter": [],
        "07 Unnamed Geometry": [],
    }
    for o in objs:
        n = len(o.data.polygons)
        lower = o.name.lower()
        dims = o.dimensions
        if o.name.startswith("Merged "):
            groups["06 Merged Clutter"].append(o)
        elif max(dims.x, dims.y) >= STRUCTURE_M:
            groups["02 Structure"].append(o)
        elif any(w in lower for w in FLOWER_WORDS):
            groups["04 Flowers and Garlands"].append(o)
        elif n >= HEAVY_FACES:
            groups["03 Heavy Props"].append(o)
        elif lower.startswith("g-no_name") or lower.startswith("component#") \
                or lower.startswith("componente#") or lower.startswith("composant#") \
                or lower.startswith("group#") or lower.startswith("obj"):
            groups["07 Unnamed Geometry"].append(o)
        else:
            groups["05 Props"].append(o)

    new_collection("00 Lighting Rig", root)       # empty, for whoever lights the set
    for label in ("02 Structure", "03 Heavy Props", "04 Flowers and Garlands",
                  "05 Props", "06 Merged Clutter", "07 Unnamed Geometry"):
        members = groups[label]
        if not members:
            continue
        top = new_collection(label, root)
        families = {}
        for o in members:
            families.setdefault(name_family(o.name), []).append(o)
        big = {k: v for k, v in families.items() if len(v) >= FAMILY_MIN}

        # Decide each object's sub-collection: its name family when the name means something,
        # and the area it sits in when it does not - or both, when a family is so large that
        # one collection of it would be no easier to work with than none at all.
        keyed = {}
        for o in members:
            fam = name_family(o.name)
            parts = []
            if fam in big:
                parts.append(fam)
            if (fam not in big and len(members) > ZONE_MIN) or len(families.get(fam, ())) > ZONE_MIN:
                parts.append(zone_of(o))
            keyed[o.name] = " - ".join(parts)

        for o in members:
            k = keyed[o.name]
            move_to(o, new_collection("%s - %s" % (label[3:], k), top) if k else top)
        subs = len({k for k in keyed.values() if k})
        say("  %-26s %6d objects, %9d faces%s"
            % (label, len(members), sum(len(o.data.polygons) for o in members),
               ", split into %d" % subs if subs else ""))

    # the leftover import collections, now empty, only clutter the outliner
    for c in list(bpy.data.collections):
        if not c.objects and not c.children and c.name.startswith("SKP "):
            bpy.data.collections.remove(c)

    cam, clearance = add_bb_camera(root)
    say("camera: %s at (%.1f, %.1f, %.1f), %.1f m of clear space around it"
        % (cam.name, cam.location.x, cam.location.y, cam.location.z, clearance))
    if clearance < 1.0:
        say("  NOTE: that is tight - the set may be partitioned. Move the camera by hand if the")
        say("  first view is inside something.")

    tris = triangles()
    c = compare_probes(base_probe, probe(args.rays))
    say("triangles %d -> %d | rays: moved %d | turned %d | facing the other way %d | "
        "different material %d" % (base_tris, tris, c["moved"], c["turned"], c["flipped"],
                                   c["material"]))
    if tris != base_tris or not probe_is_clean(c, args.rays):
        say("CHECK FAILED - not saving. Organising must not change the geometry.")
        return 5
    say("CHECK PASSED - only the organisation and the cameras changed")

    keep_unused_datablocks()
    bpy.ops.wm.save_as_mainfile(filepath=str(out), compress=True)
    say("saved : %s" % out)
    say()
    say("Collections are a starting point, not gospel - rename or regroup them in the Outliner.")
    say("The next step is bb_set_prep/08_ship.py, which embeds BB Set Viewer, sets the opening")
    say("view and the render settings, and writes the file into the set's send folder.")
    return 0


# ---------------------------------------------------------------------------
# commands
# ---------------------------------------------------------------------------

def cmd_audit(args):
    skp = Path(args.skp).expanduser().resolve()
    if not skp.exists():
        say("ERROR: no such file: %s" % skp)
        return 2
    out = Path(args.out).expanduser().resolve() if args.out else skp.with_suffix(".blend")
    out.parent.mkdir(parents=True, exist_ok=True)

    if not enable_importer():
        say("ERROR: this Blender cannot import SketchUp files.")
        say("Either the SketchUp Importer add-on is not installed, or you are on a Mac running")
        say("Blender 5.2 - the Mac build of the importer only loads in Blender 5.0.1. Convert in")
        say("5.0.1 and open the finished .blend in whichever Blender you normally use.")
        say("Install nothing else.")
        return 3

    bpy.ops.wm.read_homefile(use_empty=True)
    bpy.context.scene.name = skp.stem
    do_import(skp)
    if not mesh_objects():
        say("ERROR: the import produced no geometry.")
        say("Everything in the .skp may be hidden - the importer skips hidden groups. Unhide")
        say("everything in SketchUp, save, and run this again.")
        return 4

    kept = keep_unused_datablocks()
    world = add_world_light()
    try:
        bpy.ops.file.pack_all()
        packed = True
    except RuntimeError as exc:
        packed = False
        say("note: could not pack the textures into the file (%s)." % exc)
    bpy.ops.wm.save_as_mainfile(filepath=str(out), compress=True)

    rec = audit_report(skp)
    print_audit(rec)
    report = out.with_name(out.stem + " - conversion report.md")
    write_report(report, rec, [
        "Imported with Scenes As Cameras and Use Existing Materials; nothing else changed.",
        "World light added: %s." % world,
        "Textures packed into the .blend: %s." % ("yes" if packed else "no"),
        "Unused materials and images kept (fake user): %d." % kept,
    ])
    say("saved : %s" % out)
    say("report: %s" % report.name)
    say()
    say("Phase 1 is done and the model is untouched. Show the numbers above to whoever asked")
    say("for the set, together with the optimisation list from the guide, and wait for them to")
    say("choose. Do not run phase 2 until they have.")
    return 0


def cmd_optimise(args):
    if not bpy.data.filepath:
        say("ERROR: open the .blend on the command line before --python, e.g.")
        say('  blender -b "Set.blend" --python skp_to_blender.py -- optimise --share --join')
        return 2
    wanted = [n for n, on in (("share", args.share), ("join", args.join),
                              ("cap", args.cap > 0)) if on]
    if not wanted:
        say("Nothing asked for. Add --share, --join and/or --cap 1024.")
        return 2

    src = Path(bpy.data.filepath)
    out = Path(args.out).expanduser().resolve() if args.out else \
        src.with_name(src.stem + "_optimised.blend")
    backup = src.with_name(src.stem + "_step_backup.blend")

    # Before anything is saved: Blender does not write datablocks with no users, and this
    # command saves intermediate copies to fall back on. Without the fake users, a material or
    # image the art team made but has not used anywhere would be dropped by the first save.
    kept_now = keep_unused_datablocks()
    if kept_now:
        say("keeping %d unused materials/images that Blender would otherwise drop" % kept_now)

    say("checking the set before touching anything (%d rays). On a set with tens of"
        " thousands of objects this takes a few minutes - it is measuring, not stuck."
        % args.rays)
    base_probe = probe(args.rays)
    base = dict(tris=triangles(), faces=faces(), objects=len(bpy.context.scene.objects))
    lo, hi = world_bbox()
    say("%d objects, %d triangles, %d of %d rays hit something"
        % (base["objects"], base["tris"], sum(1 for r in base_probe if r), args.rays))

    done, reverted = [], []
    for name in wanted:
        say()
        say("--- %s ---" % name)
        bpy.ops.wm.save_as_mainfile(filepath=str(backup), compress=True)
        t = time.time()
        if name == "share":
            note = step_share(args)
        elif name == "join":
            note = step_join(args)
        else:
            note = step_cap(args)
        say("%s (%.0f s)" % (note, time.time() - t))

        if name == "cap":
            done.append(note)               # textures are meant to change; nothing to verify
            continue

        tris = triangles()
        lo2, hi2 = world_bbox()
        box_moved = float(np.abs(np.concatenate([lo2 - lo, hi2 - hi])).max()) * 1000.0
        say("triangles %d -> %d | bounding box moved %.3f mm" % (base["tris"], tris, box_moved))
        c = compare_probes(base_probe, probe(args.rays))
        say("rays: %d compared | moved %d (worst %.3f mm) | turned %d (worst %.2f deg) | "
            "facing the other way %d | different material %d | appeared %d | vanished %d"
            % (c["compared"], c["moved"], c["worst_mm"], c["turned"], c["worst_deg"],
               c["flipped"], c["material"], c["appeared"], c["vanished"]))

        ok = tris == base["tris"] and box_moved < 1.0 and probe_is_clean(c, args.rays)
        if ok:
            say("CHECK PASSED - the set is unchanged")
            done.append(note)
            continue

        say("CHECK FAILED - undoing this step")
        bpy.ops.wm.open_mainfile(filepath=str(backup))
        if name == "join" and not args.no_retry:
            say("retrying the join with the mirrored parts left out...")
            bpy.ops.wm.save_as_mainfile(filepath=str(backup), compress=True)
            note = step_join(args, skip_mirrored=True)
            say(note)
            tris = triangles()
            lo2, hi2 = world_bbox()
            box_moved = float(np.abs(np.concatenate([lo2 - lo, hi2 - hi])).max()) * 1000.0
            c = compare_probes(base_probe, probe(args.rays))
            say("rays: moved %d | turned %d | facing the other way %d | different material %d"
                % (c["moved"], c["turned"], c["flipped"], c["material"]))
            if tris == base["tris"] and box_moved < 1.0 and probe_is_clean(c, args.rays):
                say("CHECK PASSED on the second try")
                done.append(note)
                continue
            say("CHECK FAILED again - the set keeps its separate objects")
            bpy.ops.wm.open_mainfile(filepath=str(backup))
        reverted.append(name)

    keep_unused_datablocks()
    bpy.ops.wm.save_as_mainfile(filepath=str(out), compress=True)
    try:
        if backup.exists():
            backup.unlink()
        b1 = backup.with_suffix(".blend1")
        if b1.exists():
            b1.unlink()
    except OSError:
        pass

    rec = audit_report()
    rec["blend"] = out.name
    say()
    print_audit(rec)
    say("objects %d -> %d | triangles %d -> %d | file %s"
        % (base["objects"], len(bpy.context.scene.objects), base["tris"], rec["triangles"],
           "%.0f MB" % (os.path.getsize(out) / 1e6)))
    if reverted:
        say("steps undone because they changed the set: %s" % ", ".join(reverted))
    report = out.with_name(out.stem + " - conversion report.md")
    write_report(report, rec, done + ["UNDONE (it changed the set): %s" % r for r in reverted])
    say("saved : %s" % out)
    say("report: %s" % report.name)
    say()
    say("The triangle count cannot be reduced without changing the model, so if the set is")
    say("still slow to look at, that is the next conversation - not something this script")
    say("should do behind your back.")
    return 0


def main():
    argv = sys.argv[sys.argv.index("--") + 1:] if "--" in sys.argv else []
    ap = argparse.ArgumentParser(prog="skp_to_blender", description=__doc__)
    sub = ap.add_subparsers(dest="cmd", required=True)

    a1 = sub.add_parser("audit", help="import the .skp and report what is in it")
    a1.add_argument("--skp", required=True)
    a1.add_argument("--out", default="")

    a2 = sub.add_parser("optimise", help="apply the steps you were told to apply")
    a2.add_argument("--out", default="")
    a2.add_argument("--share", action="store_true", help="store identical shapes once")
    a2.add_argument("--join", action="store_true", help="join the small objects")
    a2.add_argument("--cap", type=int, default=0, help="cap texture size in pixels (changes the look)")
    a2.add_argument("--max-faces", type=int, default=JOIN_MAX_FACES)
    a2.add_argument("--cell", type=float, default=JOIN_CELL)
    a2.add_argument("--rays", type=int, default=5000,
                help="how many rays the check fires; it costs time on a set with "
                     "tens of thousands of objects, so lower it if you are impatient")
    a2.add_argument("--no-retry", action="store_true")

    a3 = sub.add_parser("prepare", help="organise the set into collections and give it a camera")
    a3.add_argument("--out", default="")
    a3.add_argument("--rays", type=int, default=3000)

    a = ap.parse_args(argv)
    if a.cmd == "audit":
        return cmd_audit(a)
    if a.cmd == "optimise":
        return cmd_optimise(a)
    return cmd_prepare(a)


# ---------------------------------------------------------------------------
# the add-on side: this file is installed through the BB extensions repository so that it
# updates itself. The panel exists to tell you where the current copy lives, because the
# conversion itself runs from the command line.
# ---------------------------------------------------------------------------

class BBSKP_OT_copy_path(bpy.types.Operator):
    """Put the path of this script on the clipboard, ready to paste into a command"""

    bl_idname = "bb_skp.copy_path"
    bl_label = "Copy Script Path"

    def execute(self, context):
        context.window_manager.clipboard = os.path.abspath(__file__)
        self.report({"INFO"}, os.path.abspath(__file__))
        return {"FINISHED"}


class BBSKP_PT_panel(bpy.types.Panel):
    bl_space_type = "VIEW_3D"
    bl_region_type = "UI"
    bl_category = "BB Convert"
    bl_label = "SketchUp Convert"

    def draw(self, context):
        lay = self.layout
        lay.label(text="Version %s" % ".".join(str(n) for n in bl_info["version"]))
        col = lay.column(align=True)
        col.scale_y = 0.8
        col.label(text="Conversion runs from the command line.")
        col.label(text="Give this script and the guide to your")
        col.label(text="assistant - it reads this file for what")
        col.label(text="it does and how to run it.")
        lay.operator("bb_skp.copy_path", icon="COPYDOWN")


_CLASSES = (BBSKP_OT_copy_path, BBSKP_PT_panel)


def register():
    for c in _CLASSES:
        bpy.utils.register_class(c)


def unregister():
    for c in reversed(_CLASSES):
        bpy.utils.unregister_class(c)


if __name__ == "__main__":
    sys.exit(main())
