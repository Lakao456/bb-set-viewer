"""BB Crowd — procedural crowds for blocking (View3D > Sidebar > BB Crowd).

Controllers: any mesh with the BB Crowd modifier is a crowd controller: a subdivided plane you shape, move and
keyframe; the members are born on it on the first frame and ride with it. Several per scene. In a BB Stage staging
the controller lives in the STAGE layer (a "Crowd" sub-collection), so Stage Mode shows it in every pane.

Influencers: ordinary objects (BB Stage character pegs, props, empties) carry a field on themselves
(Object > bb_crowd): a GAZE weight (+ look at it, − look away) with a reach, a MOVE weight (+ drift toward it,
− step aside to let it through) with a radius. Nothing is added to BB Stage: "From BB Stage" pulls the staging's
characters and props into the list, the settings stay on the objects. The fields of ALL influencers are summed.

The members are ENTITIES (v0.4, Aman 10 Oct 2026): a geometry-nodes simulation zone gives every member a lasting
position, velocity and heading. They are born once (the scatter on the first frame), then only ever walk: toward a
target that the characters' fields shape (a corridor opens ahead of a walker, a pull toward an attractor, a run
from the tower in panic, a small idle wander), with a spring back home, a walking speed cap, a personal space
around every influencer and a separation from neighbours. Nothing teleports, nothing flickers. A simulation plays
forward: Blender caches the frames as it plays; Reset re-seeds from the first frame; Bake freezes the crowd.

The influencers reach the node tree through one hidden mirror mesh per scene: two vertices per influencer (its
position and a point 1 m ahead of it, which gives its facing) bound with Hook modifiers, weights as attributes.

The panel classes are named BBST… on purpose: BB Stage hides every other sidebar tab in Stage Mode and keeps the
ones whose class name starts with BBST, so the BB Crowd tab stays next to it without touching BB Stage.

CHOREOGRAPHED CROWDS (v0.5, 11 Oct 2026): a second kind of crowd where every reaction is authored and nothing
is simulated, folded in from the stand-alone crowd_choreo.py. The crowd is ONE mesh object tagged
bb_crowd_choreo: vertex 2i is where member i stands at rest, vertex 2i+1 is one metre ahead in the direction it
faces, an edge joins them. A CUE is a hidden child mesh with the same pairs: everybody's pose when the cue is
fully played (the height of the second vertex above the first is the member's mood: +1 excited, it bobs; -1
frightened, it shrinks), with three point attributes on the even vertices: part (0/1), onset (0..1, when in the
cue's rise this member starts) and back (0..1, when in the return it goes home). The cue list lives on the crowd
object (Object.bb_crowd_cues) and every cue has two keyable sliders on the "BB Crowd Choreo" modifier: Play
(0 -> 1 plays it, members start in the order of their onset, so a reaction SPREADS) and Back (0 -> 1 sends them
home). Every frame is a pure function of the sliders: no simulation, no bake, scrub anywhere.

    crowd = choreo_make(scene, "Crowd", homes, look_at=(0, 70))
    choreo_add_cue(crowd, "Recoil", gen_back(crowd, (0, 4), 6.0), width=0.3, snap=3.0, kind='BACK')
    choreo_key(crowd, "Recoil", rise=[(2570, 0), (2600, 1)], back=[(2700, 0), (2790, 1)])

Cues STACK: what a member does is its rest pose plus, for every cue, weight x (cue pose - rest pose), for the
position and for the turn alike. choreo_state(crowd) works that out in plain Python (the same maths as the
nodes), and every generator takes base=choreo_state(crowd) to plan a new cue from where the crowd is at that
moment instead of from the rest spots; the New Cue buttons do so on the current frame.

Changes in 0.5.0: the choreographed crowd and its panel "Crowd choreography" (make one by converting a simulated
crowd or by scattering on a plane; a cue list with Play and Back sliders; New Cue: Look at, Make room around,
Step back from, Make way for, Open a lane, Cheer, By hand; Play / Back From Here, Update From Source with the
cue's numbers shown in the panel, Edit Positions with a live preview of the cue, Wave <-> Together and Snap).
One node group per crowd, edited in place, so a slider keeps its identifier (and its keys) when cues are added,
removed, renamed or reordered; it holds one small node per cue, and two helper groups shared by all crowds do
the work ("… · one cue · v1", "… · members · v1"), so adding a cue takes milliseconds however many there are.
Facing is blended as a yaw ANGLE, so a member turning right round sweeps instead of flipping. Generators are pure
functions (gen_look, gen_room, gen_back, gen_way, gen_lane, gen_mood) that keep people 0.55 m apart;
choreo_scatter places an audience in small groups instead of uniform noise. Crowds built by crowd_choreo.py are
adopted as they are (their keys keep playing). register() can be called twice. The simulated crowd is
untouched: its node tree is still the 0.4.2 one, so existing controllers are not rebuilt by this update.
In a choreographed crowd the lens clearance LEAVES OUT the few people right in front of the camera (a zone as wide as
the clearance at the lens, narrowing to nothing at the reach) instead of pushing them aside as the simulated crowd
does: pushed people piled up on the edge of the zone and slid whenever the camera moved.

Changes in 0.5.1 (11 Oct 2026, Aman: "a lot of crowd members that are appearing or disappearing"): the lens clearance
of a choreographed crowd is OFF by default (0) and Convert no longer copies it over. People left out for one camera
come back on the next cut, and anybody who steps into the zone vanishes in the middle of a shot: in a plan view, or
across a cut, that reads as people popping in and out. Keep a camera's place clear instead: no rest spot where a
camera stands (choreo_scatter keep_clear) or a Make room around the camera cue that STAYS. Every drawn person now
carries its member number (instance attribute "member"), so a check can follow one person through the whole film.
"""
import math
import random
import time

import bpy
import bmesh
from mathutils import Matrix, Vector

bl_info = {
    "name": "BB Crowd",
    "author": "Beta Builder",
    "version": (0, 5, 1),
    "blender": (5, 0, 0),
    "location": "View3D > Sidebar > BB Crowd",
    "description": "Crowds for blocking: choreographed reactions (cues) and simulated controllers with character fields",
    "category": "3D View",
}

# Blender drops or replaces bl_info on extension modules after import: keep our own copy for runtime use
VERSION = tuple(bl_info["version"])
SIM_BUILD = "0.4.2"                   # the version that last changed the SIMULATED crowd's node tree

GROUP = "BB Crowd"
MOD = "BB Crowd"
MIRROR_KEY = "bb_crowd_mirror"        # on the mirror object: the scene it serves
CTRL_KEY = "bb_crowd_controller"      # on controllers
GROUP_MARK = "Lens clearance"         # an input only this version has: older groups get retired
BUILD_TAG = "bb_crowd_build"          # on the node group: the add-on version that built it (any other → rebuilt)
ZONE_INPUTS = ["Spacing", "Density", "Seed", "Peg height", "Personal space", "Walk speed", "Run speed", "Reaction",
               "Idle amount", "Idle speed", "Idle turn", "Tower", "Panic", "Flee distance", "Veterans", "Influencers",
               "Show controller", "Peg material", "Lens clearance", "Lens reach"]
CROWD_GREY = (0.30, 0.31, 0.34, 1.0)  # default member colour: a mid grey that stays grey under the studio light


def bbstage():
    import sys
    for name, mod in list(sys.modules.items()):
        if name.endswith("bb_stage") and hasattr(mod, "is_staging") and hasattr(mod, "layer_colls"):
            return mod
    return None


def is_staging(scene):
    st = bbstage()
    return bool(st and st.is_staging(scene))


# ------------------------------------------------------------------ node group
def _sock(node, key, outputs=False):
    socks = node.outputs if outputs else node.inputs
    for s in socks:
        if s.identifier == key:
            return s
    for s in socks:
        if s.name == key:
            return s
    if "_" in key:          # typed identifiers (Value_Vector, A_INT) on versions with one dynamic socket per name
        return _sock(node, key.split("_")[0], outputs)
    raise KeyError(f"{node.name}: no socket {key} in {[s.identifier for s in socks]}")


def build_group(name=GROUP):
    ng = bpy.data.node_groups.new(name, "GeometryNodeTree")
    ng.is_modifier = True
    I = ng.interface
    I.new_socket("Geometry", in_out='INPUT', socket_type='NodeSocketGeometry')
    I.new_socket("Geometry", in_out='OUTPUT', socket_type='NodeSocketGeometry')

    def fin(nm, kind, default=None, mn=None, mx=None, desc=""):
        s = I.new_socket(nm, in_out='INPUT', socket_type=kind)
        if default is not None:
            s.default_value = default
        if mn is not None:
            s.min_value = mn
        if mx is not None:
            s.max_value = mx
        s.description = desc
        return s

    fin("Spacing", 'NodeSocketFloat', 1.1, 0.6, 5.0, "Minimum distance between members at birth (m); pegs are 0.4 m wide")
    fin("Density", 'NodeSocketFloat', 0.9, 0.0, 10.0, "Members per square metre at birth, before spacing thins them")
    fin("Seed", 'NodeSocketInt', 1, 0, 10000)
    fin("Peg height", 'NodeSocketFloat', 1.7, 0.5, 2.3)
    fin("Personal space", 'NodeSocketFloat', 0.9, 0.0, 5.0, "Members keep this far from every influencer (m)")
    fin("Walk speed", 'NodeSocketFloat', 1.5, 0.1, 10.0, "Fastest a member walks (m/s)")
    fin("Run speed", 'NodeSocketFloat', 4.0, 0.1, 15.0, "Fastest a member runs in panic (m/s)")
    fin("Reaction", 'NodeSocketFloat', 0.5, 0.05, 1.0, "How eagerly members head for where the fields want them (spring)")
    fin("Idle amount", 'NodeSocketFloat', 0.12, 0.0, 1.0, "How far members wander on the spot (m)")
    fin("Idle speed", 'NodeSocketFloat', 0.5, 0.0, 5.0, "How fast the idle wander breathes")
    fin("Idle turn", 'NodeSocketFloat', 12.0, 0.0, 90.0, "How far heads wander off their target (degrees)")
    fin("Tower", 'NodeSocketObject', desc="What the crowd watches when nothing pulls their gaze (the Jenga anchor)")
    fin("Panic", 'NodeSocketFloat', 0.0, 0.0, 1.0, "Key this on the collapse: non-veterans run from the tower")
    fin("Flee distance", 'NodeSocketFloat', 6.0, 0.0, 50.0, "How far a panicked member runs at Panic = 1 (m)")
    fin("Veterans", 'NodeSocketFloat', 0.3, 0.0, 1.0, "Share that never reacts to gaze or panic (they still make way)")
    fin("Influencers", 'NodeSocketObject', desc="The scene's BB Crowd influencer mirror (set by the panel)")
    fin("Show controller", 'NodeSocketBool', True, desc="Draw the controller plane under the crowd (off for playblasts)")
    fin("Peg material", 'NodeSocketMaterial', desc="The members' colour (one material per controller, set by the panel)")
    fin("Lens clearance", 'NodeSocketFloat', 1.0, 0.0, 3.0,
        "Members step out of the foreground wedge of the camera the scene is looking through (the cut camera), so a "
        "lens inside the crowd is never blocked. Drawn only: the simulation is not touched. 0 = off")
    fin("Lens reach", 'NodeSocketFloat', 4.0, 0.0, 15.0, "How far in front of the lens the wedge reaches (m)")

    nodes, links = ng.nodes, ng.links
    nodes.clear()

    def N(kind, nm=None, **props):
        n = nodes.new(kind)
        if nm:
            n.name = n.label = nm
        for k, v in props.items():
            setattr(n, k, v)
        return n

    def L(a, ao, b, bi):
        links.new(_sock(a, ao, True) if isinstance(ao, str) else a.outputs[ao],
                  _sock(b, bi) if isinstance(bi, str) else b.inputs[bi])

    def math_(op, nm, a=None, b=None, c=None, **defaults):
        n = N("ShaderNodeMath", nm, operation=op)
        for i, src in enumerate((a, b, c)):
            if src is not None:
                L(src[0], src[1], n, i)
        for i, v in defaults.items():
            n.inputs[int(i[1:])].default_value = v
        return n

    def vop(op, nm, a, ao, b=None, bo=None, scale=None):
        n = N("ShaderNodeVectorMath", nm, operation=op)
        L(a, ao, n, 0)
        if b is not None:
            L(b, bo, n, 1)
        if scale is not None:
            L(scale[0], scale[1], n, "Scale")
        return n

    def vscale_const(nm, a, ao, k):
        n = N("ShaderNodeVectorMath", nm, operation='SCALE')
        L(a, ao, n, 0)
        n.inputs["Scale"].default_value = k
        return n

    def xy(vec_node, out, nm):
        sep = N("ShaderNodeSeparateXYZ", nm + " sep")
        L(vec_node, out, sep, "Vector")
        comb = N("ShaderNodeCombineXYZ", nm + " xy")
        L(sep, "X", comb, "X")
        L(sep, "Y", comb, "Y")
        comb.inputs["Z"].default_value = 0.0
        return comb

    def smooth(nm, src, lo, hi, out_lo=0.0, out_hi=1.0):
        n = N("ShaderNodeMapRange", nm, interpolation_type='SMOOTHSTEP', clamp=True)
        L(src[0], src[1], n, "Value")
        n.inputs["From Min"].default_value = lo
        n.inputs["From Max"].default_value = hi
        n.inputs["To Min"].default_value = out_lo
        n.inputs["To Max"].default_value = out_hi
        return n

    def vmix(nm, fac, fo, a, ao, b, bo):
        n = N("ShaderNodeMix", nm, data_type='VECTOR')
        L(fac, fo, n, "Factor_Float")
        L(a, ao, n, "A_Vector")
        L(b, bo, n, "B_Vector")
        return n

    def attr(nm, kind='FLOAT'):
        a = N("GeometryNodeInputNamedAttribute", "read " + nm, data_type=kind)
        a.inputs["Name"].default_value = nm
        return a

    def store(nm, geo, go_key, kind, val, vo):
        s = N("GeometryNodeStoreNamedAttribute", "store " + nm, data_type=kind, domain='POINT')
        L(geo, go_key, s, "Geometry")
        s.inputs["Name"].default_value = nm
        L(val, vo, s, "Value")
        return s

    VK = {'FLOAT_VECTOR': "Value_Vector", 'FLOAT': "Value_Float"}
    AK = {'FLOAT_VECTOR': "Attribute_Vector", 'FLOAT': "Attribute_Float", 'INT': "Attribute_Int"}
    VV, VF, AV, AF = VK['FLOAT_VECTOR'], VK['FLOAT'], AK['FLOAT_VECTOR'], AK['FLOAT']

    gi = N("NodeGroupInput", "In")
    go = N("NodeGroupOutput", "Out")

    # ================================================================ birth: scatter + per-member constants
    dist = N("GeometryNodeDistributePointsOnFaces", "Scatter", distribute_method='POISSON')
    L(gi, "Geometry", dist, "Mesh")
    L(gi, "Spacing", dist, "Distance Min")
    L(gi, "Density", dist, "Density Max")
    L(gi, "Seed", dist, "Seed")
    idx = N("GeometryNodeInputIndex", "Index")
    pos = N("GeometryNodeInputPosition", "Position")

    def rnd(nm, lo, hi, seed_off):
        r = N("FunctionNodeRandomValue", nm, data_type='FLOAT')
        _sock(r, "Min").default_value = lo
        _sock(r, "Max").default_value = hi
        L(idx, "Index", r, "ID")
        s = math_('ADD', f"seed+{seed_off}", (gi, "Seed"), i1=float(seed_off))
        L(s, "Value", r, "Seed")
        return r

    rnd_vet = rnd("Random veteran", 0.0, 1.0, 0)
    vet_cmp = N("FunctionNodeCompare", "Is veteran", data_type='FLOAT', operation='LESS_THAN')
    L(rnd_vet, "Value", vet_cmp, "A")
    L(gi, "Veterans", vet_cmp, "B")
    vet0 = math_('ADD', "veteran 0/1", (vet_cmp, "Result"), i1=0.0)
    consts = [("vet", vet0), ("rflee", rnd("Random flee", 0.6, 1.4, 1)), ("ryaw", rnd("Random yaw", -0.35, 0.35, 2)),
              ("rh", rnd("Random height", 0.92, 1.08, 3)), ("rside", math_('SIGN', "side ±1", (rnd("Random side", -1.0, 1.0, 4), "Value"))),
              ("rreact", rnd("Random reaction", 0.8, 1.3, 5)), ("rstep", rnd("Random step", 0.75, 1.0, 6))]
    geo, gkey = dist, "Points"
    for nm, node in consts:
        geo = store(nm, geo, gkey, 'FLOAT', node, "Value")
        gkey = "Geometry"
    geo = store("home", geo, gkey, 'FLOAT_VECTOR', pos, "Position")
    zero_v = N("FunctionNodeInputVector", "zero")
    geo = store("vel", geo, "Geometry", 'FLOAT_VECTOR', zero_v, "Vector")
    # born facing the tower
    oi_tower0 = N("GeometryNodeObjectInfo", "Tower info (birth)", transform_space='RELATIVE')
    L(gi, "Tower", oi_tower0, "Object")
    face0 = vop('NORMALIZE', "face tower (birth)", xy(vop('SUBTRACT', "tower - P (birth)", oi_tower0, "Location", pos, "Position"), "Vector", "tp0"), "Vector")
    geo = store("hdg", geo, "Geometry", 'FLOAT_VECTOR', face0, "Vector")
    birth = geo

    # ================================================================ the simulation zone
    si = N("GeometryNodeSimulationInput", "Sim in")
    so = N("GeometryNodeSimulationOutput", "Sim out")
    si.pair_with_output(so)
    L(birth, "Geometry", si, "Item_0")
    dt = (si, "Delta Time")
    sgeo = (si, "Item_0")

    # ---- influencers in this frame
    oi_inf = N("GeometryNodeObjectInfo", "Influencers info", transform_space='RELATIVE')
    L(gi, "Influencers", oi_inf, "Object")
    kind_attr = attr("kind", 'INT')
    is_pos = N("FunctionNodeCompare", "kind == 0", data_type='INT', operation='EQUAL')
    L(kind_attr, AK['INT'], is_pos, "A_INT")
    _sock(is_pos, "B_INT").default_value = 0
    one = N("ShaderNodeValue", "one")
    one.outputs[0].default_value = 1.0
    stat = N("GeometryNodeAttributeStatistic", "count influencers", data_type='FLOAT', domain='POINT')
    L(oi_inf, "Geometry", stat, "Geometry")
    L(is_pos, "Result", stat, "Selection")
    L(one, 0, stat, "Attribute")
    n_inf = (stat, "Sum")

    # ---- per-member reads (fields on the simulated points)
    home = attr("home", 'FLOAT_VECTOR')
    vel = attr("vel", 'FLOAT_VECTOR')
    hdg = attr("hdg", 'FLOAT_VECTOR')
    vet = attr("vet")
    rflee, ryaw, rside, rreact, rstep = attr("rflee"), attr("ryaw"), attr("rside"), attr("rreact"), attr("rstep")
    not_vet = math_('SUBTRACT', "1 - veteran", None, (vet, AF), i0=1.0)

    # ---- repeat over the influencers: sum their fields into acc_off / acc_gaze / acc_ps
    zero_in = N("FunctionNodeInputVector", "zero acc")
    acc0 = store("acc_off", si, "Item_0", 'FLOAT_VECTOR', zero_in, "Vector")
    acc0 = store("acc_gaze", acc0, "Geometry", 'FLOAT_VECTOR', zero_in, "Vector")
    acc0 = store("acc_ps", acc0, "Geometry", 'FLOAT_VECTOR', zero_in, "Vector")
    ri = N("GeometryNodeRepeatInput", "Repeat in")
    ro = N("GeometryNodeRepeatOutput", "Repeat out")
    ri.pair_with_output(ro)
    L(n_inf[0], n_inf[1], ri, "Iterations")
    L(acc0, "Geometry", ri, "Item_0")
    it = (ri, "Iteration")
    i_pos = math_('MULTIPLY', "2i", it, i1=2.0)
    i_hdg = math_('ADD', "2i+1", (i_pos, "Value"), i1=1.0)

    def samp(nm, kind, value_node, value_out, index_node):
        s = N("GeometryNodeSampleIndex", nm, data_type=kind, domain='POINT')
        L(oi_inf, "Geometry", s, "Geometry")
        L(value_node, value_out, s, VK[kind])
        L(index_node, "Value", s, "Index")
        return s

    q_i = samp("Q_i", 'FLOAT_VECTOR', pos, "Position", i_pos)
    q_h = samp("Q_i ahead", 'FLOAT_VECTOR', pos, "Position", i_hdg)
    w_mv = samp("move_i", 'FLOAT', attr("move"), AF, i_pos)
    w_gz = samp("gaze_i", 'FLOAT', attr("gaze"), AF, i_pos)
    r_i = samp("radius_i", 'FLOAT', attr("radius"), AF, i_pos)
    g_i = samp("gaze_radius_i", 'FLOAT', attr("gaze_radius"), AF, i_pos)
    h_i = vop('NORMALIZE', "h_i", xy(vop('SUBTRACT', "ahead - Q", q_h, VV, q_i, VV), "Vector", "h_i"), "Vector")
    d_m = xy(vop('SUBTRACT', "home - Q_i", home, AV, q_i, VV), "Vector", "d_m")
    hn_sep = N("ShaderNodeSeparateXYZ", "h_i sep")
    L(h_i, "Vector", hn_sep, "Vector")
    perp = N("ShaderNodeCombineXYZ", "perp (left)")
    neg_hy = math_('MULTIPLY', "-hy", (hn_sep, "Y"), i1=-1.0)
    L(neg_hy, "Value", perp, "X")
    L(hn_sep, "X", perp, "Y")
    perp.inputs["Z"].default_value = 0.0
    along = vop('DOT_PRODUCT', "along", d_m, "Vector", h_i, "Vector")
    lat = vop('DOT_PRODUCT', "lateral", d_m, "Vector", perp, "Vector")
    lat_abs = math_('ABSOLUTE', "|lat|", (lat, "Value"))
    lat_sign_raw = math_('SIGN', "sign lat", (lat, "Value"))
    tiny = N("FunctionNodeCompare", "lat ~ 0", data_type='FLOAT', operation='LESS_THAN')
    L(lat_abs, "Value", tiny, "A")
    tiny.inputs["B"].default_value = 0.05
    sw_sign = N("GeometryNodeSwitch", "sign or random", input_type='FLOAT')
    L(tiny, "Result", sw_sign, "Switch")
    L(lat_sign_raw, "Value", sw_sign, "False")
    L(rside, AF, sw_sign, "True")
    r_safe = math_('MAXIMUM', "R safe", (r_i, VF), i1=0.2)
    clear = math_('SUBTRACT', "R - |lat|", (r_safe, "Value"), (lat_abs, "Value"))
    clear_c = math_('MAXIMUM', "clear >= 0", (clear, "Value"), i1=0.0)
    along_n0 = math_('DIVIDE', "along/R", (along, "Value"), (r_safe, "Value"))
    along_n = math_('DIVIDE', "along/R/react", (along_n0, "Value"), (rreact, AF))
    win_up = smooth("open ahead", (along_n, "Value"), -0.6, 0.3)
    win_dn = smooth("close far", (along_n, "Value"), 1.5, 2.5, 1.0, 0.0)
    win = math_('MULTIPLY', "window", (win_up, "Result"), (win_dn, "Result"))
    w_abs = math_('ABSOLUTE', "|w move|", (w_mv, VF))
    is_repel = N("FunctionNodeCompare", "w < 0", data_type='FLOAT', operation='LESS_THAN')
    L(w_mv, VF, is_repel, "A")
    is_repel.inputs["B"].default_value = 0.0
    step1 = math_('MULTIPLY', "step amount", (clear_c, "Value"), (win, "Value"))
    step2 = math_('MULTIPLY', "step*|w|", (step1, "Value"), (w_abs, "Value"))
    step3 = math_('MULTIPLY', "step*sign", (step2, "Value"), (sw_sign, "Output"))
    step4 = math_('MULTIPLY', "step*random", (step3, "Value"), (rstep, AF))
    off_step = vop('SCALE', "step offset", perp, "Vector", scale=(step4, "Value"))
    d_len = vop('LENGTH', "|d_m|", d_m, "Vector")
    d_n = math_('DIVIDE', "|d|/R", (d_len, "Value"), (r_safe, "Value"))
    pull_f = smooth("pull falloff", (d_n, "Value"), 0.3, 2.0, 1.0, 0.0)
    half_r = math_('MULTIPLY', "R/2", (r_safe, "Value"), i1=0.5)
    pull1 = math_('MULTIPLY', "pull", (pull_f, "Result"), (half_r, "Value"))
    pull2 = math_('MULTIPLY', "pull*w", (pull1, "Value"), (w_mv, VF))
    pull3 = math_('MULTIPLY', "pull*(1-vet)", (pull2, "Value"), (not_vet, "Value"))
    toward = vop('NORMALIZE', "toward Q_i", d_m, "Vector")
    off_pull = vop('SCALE', "pull offset", toward, "Vector", scale=(math_('MULTIPLY', "-pull", (pull3, "Value"), i1=-1.0), "Value"))
    sw_move = N("GeometryNodeSwitch", "step or pull", input_type='VECTOR')
    L(is_repel, "Result", sw_move, "Switch")
    L(off_pull, "Vector", sw_move, "False")
    L(off_step, "Vector", sw_move, "True")
    acc_off_r = attr("acc_off", 'FLOAT_VECTOR')
    acc_off_new = vop('ADD', "acc_off +", acc_off_r, AV, sw_move, "Output")
    # gaze: a weighted direction toward (or away from) this influencer
    d_g = xy(vop('SUBTRACT', "Q_i - home", q_i, VV, home, AV), "Vector", "d_g")
    g_len = vop('LENGTH', "|d_g|", d_g, "Vector")
    g_safe = math_('MAXIMUM', "Rg safe", (g_i, VF), i1=1.0)
    g_n = math_('DIVIDE', "|d_g|/Rg", (g_len, "Value"), (g_safe, "Value"))
    g_fall = smooth("gaze falloff", (g_n, "Value"), 0.8, 1.0, 1.0, 0.0)
    g_w = math_('MULTIPLY', "gaze*falloff", (w_gz, VF), (g_fall, "Result"))
    gaze_c = vop('SCALE', "gaze contribution", vop('NORMALIZE', "toward gazer", d_g, "Vector"), "Vector", scale=(g_w, "Value"))
    acc_gaze_r = attr("acc_gaze", 'FLOAT_VECTOR')
    acc_gaze_new = vop('ADD', "acc_gaze +", acc_gaze_r, AV, gaze_c, "Vector")
    # personal space from the CURRENT position (a hard push, applied after the step)
    d_p = xy(vop('SUBTRACT', "P - Q_i", pos, "Position", q_i, VV), "Vector", "d_p")
    p_len = vop('LENGTH', "|d_p|", d_p, "Vector")
    gap = math_('SUBTRACT', "personal - |d_p|", (gi, "Personal space"), (p_len, "Value"))
    gap_c = math_('MAXIMUM', "gap >= 0", (gap, "Value"), i1=0.0)
    ps_c = vop('SCALE', "ps contribution", vop('NORMALIZE', "away from Q_i", d_p, "Vector"), "Vector", scale=(gap_c, "Value"))
    acc_ps_r = attr("acc_ps", 'FLOAT_VECTOR')
    acc_ps_new = vop('ADD', "acc_ps +", acc_ps_r, AV, ps_c, "Vector")
    s1 = store("acc_off", ri, "Item_0", 'FLOAT_VECTOR', acc_off_new, "Vector")
    s2 = store("acc_gaze", s1, "Geometry", 'FLOAT_VECTOR', acc_gaze_new, "Vector")
    s3 = store("acc_ps", s2, "Geometry", 'FLOAT_VECTOR', acc_ps_new, "Vector")
    L(s3, "Geometry", ro, "Item_0")
    summed = (ro, "Item_0")

    # ---- after the loop: target, forces, integration (fields read from the summed geometry)
    acc_off = attr("acc_off", 'FLOAT_VECTOR')
    acc_gaze = attr("acc_gaze", 'FLOAT_VECTOR')
    acc_ps = attr("acc_ps", 'FLOAT_VECTOR')
    oi_tower = N("GeometryNodeObjectInfo", "Tower info", transform_space='RELATIVE')
    L(gi, "Tower", oi_tower, "Object")
    d_tower = xy(vop('SUBTRACT', "home - tower", home, AV, oi_tower, "Location"), "Vector", "d_tower")
    flee_dir = vop('NORMALIZE', "flee dir", d_tower, "Vector")
    pa = math_('MULTIPLY', "panic*flee", (gi, "Panic"), (gi, "Flee distance"))
    pb = math_('MULTIPLY', "*(1-vet)", (pa, "Value"), (not_vet, "Value"))
    pc = math_('MULTIPLY', "*random", (pb, "Value"), (rflee, AF))
    off_flee = vop('SCALE', "flee offset", flee_dir, "Vector", scale=(pc, "Value"))
    time = N("GeometryNodeInputSceneTime", "Time")
    t_speed = math_('MULTIPLY', "t*speed", (time, "Seconds"), (gi, "Idle speed"))
    noise = N("ShaderNodeTexNoise", "Idle noise", noise_dimensions='4D')
    noise.inputs["Scale"].default_value = 1.0
    noise.inputs["Detail"].default_value = 1.0
    noise.inputs["Roughness"].default_value = 0.4
    L(vscale_const("home*0.25", home, AV, 0.25), "Vector", noise, "Vector")
    L(t_speed, "Value", noise, "W")
    n_sep = N("ShaderNodeSeparateXYZ", "noise sep")
    L(noise, "Color", n_sep, "Vector")

    def centred(nm, src, so_, amp_node, amp_out):
        c = math_('SUBTRACT', nm + " -0.5", (src, so_), i1=0.5)
        c2 = math_('MULTIPLY', nm + " *4", (c, "Value"), i1=4.0)
        return math_('MULTIPLY', nm + " *amp", (c2, "Value"), (amp_node, amp_out))

    idle_x = centred("idle x", n_sep, "X", gi, "Idle amount")
    idle_y = centred("idle y", n_sep, "Y", gi, "Idle amount")
    off_idle = N("ShaderNodeCombineXYZ", "idle offset")
    L(idle_x, "Value", off_idle, "X")
    L(idle_y, "Value", off_idle, "Y")
    off_idle.inputs["Z"].default_value = 0.0
    t1 = vop('ADD', "home + acc", home, AV, acc_off, AV)
    t2 = vop('ADD', "+ flee", t1, "Vector", off_flee, "Vector")
    target = vop('ADD', "+ idle", t2, "Vector", off_idle, "Vector")
    # spring toward the target, damped; speed capped at walk (run in panic)
    err = vop('SUBTRACT', "target - P", target, "Vector", pos, "Position")
    k = math_('MULTIPLY', "k = reaction*12", (gi, "Reaction"), i1=12.0)
    c_damp = math_('SQRT', "sqrt k", (k, "Value"))
    c2 = math_('MULTIPLY', "damping 2 sqrt k", (c_damp, "Value"), i1=2.0)
    f_spring = vop('SCALE', "spring", err, "Vector", scale=(k, "Value"))
    f_damp = vop('SCALE', "damping", vel, AV, scale=(c2, "Value"))
    force = vop('SUBTRACT', "force", f_spring, "Vector", f_damp, "Vector")
    dv = vop('SCALE', "force*dt", force, "Vector", scale=dt)
    v1 = vop('ADD', "vel + dv", vel, AV, dv, "Vector")
    v1xy = xy(v1, "Vector", "v1")
    vmax_run = vmix("walk→run", math_('MULTIPLY', "panic*(1-vet)", (gi, "Panic"), (not_vet, "Value")), "Value",
                    N("ShaderNodeCombineXYZ", "walk vec"), "Vector", N("ShaderNodeCombineXYZ", "run vec"), "Vector")
    # (combine nodes carry the scalar in X; cheaper than a float mix with typed sockets)
    L(gi, "Walk speed", nodes["walk vec"], "X")
    L(gi, "Run speed", nodes["run vec"], "X")
    vmax_sep = N("ShaderNodeSeparateXYZ", "vmax")
    L(vmax_run, "Result_Vector", vmax_sep, "Vector")
    speed = vop('LENGTH', "|v|", v1xy, "Vector")
    over = math_('DIVIDE', "|v|/vmax", (speed, "Value"), (vmax_sep, "X"))
    over_c = math_('MAXIMUM', "max(1, over)", (over, "Value"), i1=1.0)
    inv = math_('DIVIDE', "1/over", None, (over_c, "Value"), i0=1.0)
    v_cap = vop('SCALE', "v capped", v1xy, "Vector", scale=(inv, "Value"))
    dp = vop('SCALE', "v*dt", v_cap, "Vector", scale=dt)
    p1 = vop('ADD', "P + v dt", pos, "Position", dp, "Vector")
    # the personal-space push is a hard correction, but never more than two walking steps per frame
    push_cap = math_('MULTIPLY', "push cap", (vmax_sep, "X"), dt)
    push_cap2 = math_('MULTIPLY', "push cap*2", (push_cap, "Value"), i1=2.0)
    ps_len = vop('LENGTH', "|acc_ps|", acc_ps, AV)
    ps_over = math_('DIVIDE', "|ps|/cap", (ps_len, "Value"), (push_cap2, "Value"))
    ps_over_c = math_('MAXIMUM', "max(1, ps over)", (ps_over, "Value"), i1=1.0)
    ps_inv = math_('DIVIDE', "1/ps over", None, (ps_over_c, "Value"), i0=1.0)
    ps_capped = vop('SCALE', "ps capped", acc_ps, AV, scale=(ps_inv, "Value"))
    p2 = vop('ADD', "+ personal push", p1, "Vector", ps_capped, "Vector")
    # stay on the controller's floor
    p2s = N("ShaderNodeSeparateXYZ", "p2 sep")
    L(p2, "Vector", p2s, "Vector")
    home_s = N("ShaderNodeSeparateXYZ", "home sep")
    L(home, AV, home_s, "Vector")
    p3 = N("ShaderNodeCombineXYZ", "P new")
    L(p2s, "X", p3, "X")
    L(p2s, "Y", p3, "Y")
    L(home_s, "Z", p3, "Z")
    # heading: along the velocity when walking, the gaze when standing; eased
    face_tower = vop('NORMALIZE', "face tower", xy(vop('SUBTRACT', "tower - home", oi_tower, "Location", home, AV), "Vector", "tower-home"), "Vector")
    g_len2 = vop('LENGTH', "|acc_gaze|", acc_gaze, AV)
    g_amt = math_('MINIMUM', "min(1,|g|)", (g_len2, "Value"), i1=1.0)
    g_amt2 = math_('MULTIPLY', "gaze*(1-vet)", (g_amt, "Value"), (not_vet, "Value"))
    g_dir = vop('NORMALIZE', "gaze dir", acc_gaze, AV)
    face_g = vmix("tower→gaze", g_amt2, "Value", face_tower, "Vector", g_dir, "Vector")
    panic_face = math_('MULTIPLY', "panic face", (gi, "Panic"), (not_vet, "Value"))
    face_s = vmix("→flee", panic_face, "Value", face_g, "Result_Vector", flee_dir, "Vector")
    v_dir = vop('NORMALIZE', "v dir", v_cap, "Vector")
    moving = smooth("moving?", (speed, "Value"), 0.25, 0.6)
    face_t = vmix("stand→walk", moving, "Result", face_s, "Result_Vector", v_dir, "Vector")
    turn = math_('MULTIPLY', "turn rate*dt", dt, i1=4.0)
    turn_c = math_('MINIMUM', "min(1, turn)", (turn, "Value"), i1=1.0)
    h_err = vop('SUBTRACT', "face_t - hdg", face_t, "Result_Vector", hdg, AV)
    h_new = vop('NORMALIZE', "hdg new", vop('ADD', "hdg + turn", hdg, AV, vop('SCALE', "turn step", h_err, "Vector", scale=(turn_c, "Value")), "Vector"), "Vector")
    # write the new state
    setp = N("GeometryNodeSetPosition", "Move members")
    L(ro, "Item_0", setp, "Geometry")
    L(p3, "Vector", setp, "Position")
    sv = store("vel", setp, "Geometry", 'FLOAT_VECTOR', v_cap, "Vector")
    sh = store("hdg", sv, "Geometry", 'FLOAT_VECTOR', h_new, "Vector")
    # separation: nobody inside their neighbour (one relaxation step on the new positions)
    near = N("GeometryNodeIndexOfNearest", "Nearest member")
    L(pos, "Position", near, "Position")
    q_n = N("GeometryNodeSampleIndex", "neighbour pos", data_type='FLOAT_VECTOR', domain='POINT')
    L(sh, "Geometry", q_n, "Geometry")
    L(pos, "Position", q_n, VV)
    L(near, "Index", q_n, "Index")
    d_nb = xy(vop('SUBTRACT', "P - neighbour", pos, "Position", q_n, VV), "Vector", "d_nb")
    nb_len = vop('LENGTH', "|d_nb|", d_nb, "Vector")
    min_gap = math_('MULTIPLY', "spacing*0.8", (gi, "Spacing"), i1=0.8)
    overlap = math_('SUBTRACT', "gap - |d_nb|", (min_gap, "Value"), (nb_len, "Value"))
    overlap_c = math_('MAXIMUM', "overlap >= 0", (overlap, "Value"), i1=0.0)
    overlap_h = math_('MULTIPLY', "half", (overlap_c, "Value"), i1=0.5)
    overlap_cap = math_('MINIMUM', "sep <= one step", (overlap_h, "Value"), (push_cap, "Value"))
    off_sep = vop('SCALE', "separation", vop('NORMALIZE', "away from neighbour", d_nb, "Vector"), "Vector", scale=(overlap_cap, "Value"))
    setp2 = N("GeometryNodeSetPosition", "Separate members")
    L(sh, "Geometry", setp2, "Geometry")
    L(off_sep, "Vector", setp2, "Offset")
    L(setp2, "Geometry", so, "Item_0")
    simmed = (so, "Item_0")

    # ================================================================ draw: pegs on the members
    hdg_out = attr("hdg (draw)", 'FLOAT_VECTOR')
    hdg_out.inputs["Name"].default_value = "hdg"
    ryaw_out = attr("ryaw (draw)")
    ryaw_out.inputs["Name"].default_value = "ryaw"
    rh_out = attr("rh (draw)")
    rh_out.inputs["Name"].default_value = "rh"
    home_out = attr("home (draw)", 'FLOAT_VECTOR')
    home_out.inputs["Name"].default_value = "home"
    noise2 = N("ShaderNodeTexNoise", "Idle noise (draw)", noise_dimensions='4D')
    noise2.inputs["Scale"].default_value = 1.0
    L(vscale_const("home*0.25 (draw)", home_out, AV, 0.25), "Vector", noise2, "Vector")
    L(t_speed, "Value", noise2, "W")
    n_sep2 = N("ShaderNodeSeparateXYZ", "noise sep (draw)")
    L(noise2, "Color", n_sep2, "Vector")
    turn_rad = math_('RADIANS', "idle turn rad", (gi, "Idle turn"))
    idle_yaw = centred("idle yaw", n_sep2, "Z", turn_rad, "Value")
    align = N("FunctionNodeAlignRotationToVector", "Face it", axis='Y', pivot_axis='Z')
    L(hdg_out, AV, align, "Vector")
    yaw_total = math_('ADD', "yaw + idle", (ryaw_out, AF), (idle_yaw, "Value"))
    comb_yaw = N("ShaderNodeCombineXYZ", "yaw euler")
    L(yaw_total, "Value", comb_yaw, "Z")
    yaw = N("FunctionNodeEulerToRotation", "yaw rotation")
    L(comb_yaw, "Vector", yaw, "Euler")
    rot = N("FunctionNodeRotateRotation", "Rotate", rotation_space='LOCAL')
    L(align, "Rotation", rot, "Rotation")
    L(yaw, "Rotation", rot, "Rotate By")
    # the peg: the same shape as a BB Stage character at 1.75 m (tapered body, head, nose on +Y)
    H = 1.75
    r_body, body_h, head_r = 0.13, H * 0.80, H * 0.075
    body = N("GeometryNodeMeshCone", "Body", fill_type='NGON')
    body.inputs["Vertices"].default_value = 16
    body.inputs["Radius Top"].default_value = r_body * 0.85
    body.inputs["Radius Bottom"].default_value = r_body
    body.inputs["Depth"].default_value = body_h
    head = N("GeometryNodeMeshUVSphere", "Head")
    head.inputs["Segments"].default_value = 12
    head.inputs["Rings"].default_value = 8
    head.inputs["Radius"].default_value = head_r
    head_t = N("GeometryNodeTransform", "Head up")
    head_t.inputs["Translation"].default_value = (0.0, 0.0, body_h + head_r * 1.1)
    L(head, "Mesh", head_t, "Geometry")
    nose = N("GeometryNodeMeshCone", "Nose", fill_type='NGON')
    nose.inputs["Vertices"].default_value = 10
    nose.inputs["Radius Top"].default_value = 0.0
    nose.inputs["Radius Bottom"].default_value = head_r * 0.45
    nose.inputs["Depth"].default_value = head_r * 1.08
    nose_t = N("GeometryNodeTransform", "Nose fwd")
    # BB Stage builds its nose with bmesh, whose cone is centred: centre at 1.35 head radii, 1.08 long, so
    # the base sits 0.81 head radii out, inside the head. The Cone NODE starts at its origin (base at 0,
    # tip at +depth), so the same nose is the node cone moved 0.81 head radii out.
    nose_t.inputs["Translation"].default_value = (0.0, head_r * 0.81, body_h + head_r * 1.1)
    nose_t.inputs["Rotation"].default_value = (-math.pi / 2, math.pi / 10, 0.0)   # the 18° turn lines the ten sides up with bmesh
    L(nose, "Mesh", nose_t, "Geometry")
    peg = N("GeometryNodeJoinGeometry", "Peg")
    links.new(body.outputs["Mesh"], peg.inputs[0])
    for n in (head_t, nose_t):
        links.new(n.outputs["Geometry"], peg.inputs[0])
    setmat = N("GeometryNodeSetMaterial", "Peg material")
    L(gi, "Peg material", setmat, "Material")
    L(peg, "Geometry", setmat, "Geometry")
    scale_h = math_('DIVIDE', "height/1.7", (gi, "Peg height"), i1=1.7)
    scale_r = math_('MULTIPLY', "*random h", (scale_h, "Value"), (rh_out, AF))
    scale_v = N("ShaderNodeCombineXYZ", "scale xyz")
    for kk in "XYZ":
        L(scale_r, "Value", scale_v, kk)
    # ================================================================ lens clearance (after the simulation: drawn only)
    # A wedge in front of the scene's active camera (the camera of the current cut): half a metre wide at the
    # lens, widening by 0.3 m per metre, as far as Lens reach. Members inside it are drawn stepped aside to its
    # edge. It is not part of the simulation, so it needs no pre-roll, follows the cuts by itself and never
    # changes where anybody really stands. Off for cameras above the crowd and for top-down cameras.
    cam = N("GeometryNodeInputActiveCamera", "Active camera")
    oi_cam = N("GeometryNodeObjectInfo", "Camera info", transform_space='RELATIVE')
    L(cam, 0, oi_cam, "Object")
    look = N("FunctionNodeRotateVector", "camera forward")
    look.inputs["Vector"].default_value = (0.0, 0.0, -1.0)
    L(oi_cam, "Rotation", look, "Rotation")
    fwd_raw = xy(look, "Vector", "fwd raw")
    fwd_len = vop('LENGTH', "|fwd xy|", fwd_raw, "Vector")
    fwd = vop('NORMALIZE', "fwd", fwd_raw, "Vector")
    level = smooth("camera not top-down", (fwd_len, "Value"), 0.15, 0.35)
    cam_sep = N("ShaderNodeSeparateXYZ", "camera pos sep")
    L(oi_cam, "Location", cam_sep, "Vector")
    low = smooth("camera in the crowd", (cam_sep, "Z"), 2.6, 3.6, 1.0, 0.0)
    d_c = xy(vop('SUBTRACT', "P - camera", pos, "Position", oi_cam, "Location"), "Vector", "d_c")
    along_c = vop('DOT_PRODUCT', "along lens", d_c, "Vector", fwd, "Vector")
    lat_vec = vop('SUBTRACT', "lateral vec", d_c, "Vector", vop('SCALE', "along*fwd", fwd, "Vector", scale=(along_c, "Value")), "Vector")
    lat_c = vop('LENGTH', "|lateral|", lat_vec, "Vector")
    along_pos = math_('MAXIMUM', "along >= 0", (along_c, "Value"), i1=0.0)
    wedge = math_('MULTIPLY_ADD', "0.3*along + 0.5", (along_pos, "Value"), i1=0.3, i2=0.5)
    wedge_w = math_('MULTIPLY', "wedge*clearance", (wedge, "Value"), (gi, "Lens clearance"))
    gap_c = math_('SUBTRACT', "wedge - |lat|", (wedge_w, "Value"), (lat_c, "Value"))
    gap_cc = math_('MAXIMUM', "gap >= 0 (lens)", (gap_c, "Value"), i1=0.0)
    near_w = smooth("starts behind the lens", (along_c, "Value"), -0.6, -0.2)
    reach_m1 = math_('SUBTRACT', "reach - 1", (gi, "Lens reach"), i1=1.0)
    far_t = math_('SUBTRACT', "along - (reach-1)", (along_c, "Value"), (reach_m1, "Value"))
    far_w = smooth("ends at the reach", (far_t, "Value"), 0.0, 1.0, 1.0, 0.0)
    w1 = math_('MULTIPLY', "lens window", (near_w, "Result"), (far_w, "Result"))
    w2 = math_('MULTIPLY', "*level", (w1, "Value"), (level, "Result"))
    w3 = math_('MULTIPLY', "*low", (w2, "Value"), (low, "Result"))
    lens_push = math_('MULTIPLY', "lens push", (gap_cc, "Value"), (w3, "Value"))
    # which way: straight out sideways; a member exactly on the axis takes its own random side
    perp_c = N("ShaderNodeCombineXYZ", "lens perp")
    fs = N("ShaderNodeSeparateXYZ", "fwd sep")
    L(fwd, "Vector", fs, "Vector")
    L(math_('MULTIPLY', "-fwd y", (fs, "Y"), i1=-1.0), "Value", perp_c, "X")
    L(fs, "X", perp_c, "Y")
    perp_c.inputs["Z"].default_value = 0.0
    rside_d = attr("rside (lens)")
    rside_d.inputs["Name"].default_value = "rside"
    perp_side = vop('SCALE', "perp*side", perp_c, "Vector", scale=(rside_d, AF))
    on_axis = N("FunctionNodeCompare", "on the axis", data_type='FLOAT', operation='LESS_THAN')
    L(lat_c, "Value", on_axis, "A")
    on_axis.inputs["B"].default_value = 0.03
    out_dir = N("GeometryNodeSwitch", "out direction", input_type='VECTOR')
    L(on_axis, "Result", out_dir, "Switch")
    L(vop('NORMALIZE', "lateral dir", lat_vec, "Vector"), "Vector", out_dir, "False")
    L(perp_side, "Vector", out_dir, "True")
    lens_off = vop('SCALE', "lens offset", out_dir, "Output", scale=(lens_push, "Value"))
    lens_set = N("GeometryNodeSetPosition", "Clear the lens")
    L(simmed[0], simmed[1], lens_set, "Geometry")
    L(lens_off, "Vector", lens_set, "Offset")
    # the people drawn stepped aside must not land inside a character: half a metre from every influencer's
    # spot, drawn only like the wedge (the simulation keeps its own, wider Personal space)
    inf_d = N("GeometryNodeObjectInfo", "Influencers info (draw)", transform_space="RELATIVE")
    L(gi, "Influencers", inf_d, "Object")
    kind_d = attr("kind (draw)", "INT")
    kind_d.inputs["Name"].default_value = "kind"
    is_pos_d = N("FunctionNodeCompare", "kind == 0 (draw)", data_type="INT", operation="EQUAL")
    L(kind_d, AK["INT"], is_pos_d, "A_INT")
    _sock(is_pos_d, "B_INT").default_value = 0
    spots = N("GeometryNodeSeparateGeometry", "Influencer spots", domain="POINT")
    L(inf_d, "Geometry", spots, "Geometry")
    L(is_pos_d, "Result", spots, "Selection")
    prox = N("GeometryNodeProximity", "Nearest character", target_element="POINTS")
    links.new(spots.outputs[0], prox.inputs[0])
    d_ch = xy(vop("SUBTRACT", "P - character", pos, "Position", prox, "Position"), "Vector", "d_ch")
    ch_gap = math_("SUBTRACT", "0.5 - distance", None, (prox, "Distance"), i0=0.5)
    ch_gap_c = math_("MAXIMUM", "gap >= 0 (character)", (ch_gap, "Value"), i1=0.0)
    ch_valid = N("GeometryNodeSwitch", "any character?", input_type="FLOAT")
    L(prox, "Is Valid", ch_valid, "Switch")
    L(ch_gap_c, "Value", ch_valid, "True")
    ch_off = vop("SCALE", "off the character", vop("NORMALIZE", "away from the character", d_ch, "Vector"), "Vector", scale=(ch_valid, "Output"))
    keep_off = N("GeometryNodeSetPosition", "Keep off the characters")
    L(lens_set, "Geometry", keep_off, "Geometry")
    L(ch_off, "Vector", keep_off, "Offset")

    inst = N("GeometryNodeInstanceOnPoints", "Members")
    L(keep_off, "Geometry", inst, "Points")
    L(setmat, "Geometry", inst, "Instance")
    L(rot, "Rotation", inst, "Rotation")
    L(scale_v, "Vector", inst, "Scale")
    plane_sw = N("GeometryNodeSwitch", "controller shown?", input_type='GEOMETRY')
    L(gi, "Show controller", plane_sw, "Switch")
    L(gi, "Geometry", plane_sw, "True")
    out_join = N("GeometryNodeJoinGeometry", "Crowd + controller")
    links.new(inst.outputs["Instances"], out_join.inputs[0])
    links.new(plane_sw.outputs["Output"], out_join.inputs[0])
    L(out_join, "Geometry", go, "Geometry")
    for i, n in enumerate(nodes):
        n.location = ((i % 16) * 220, -(i // 16) * 240)
    ng[BUILD_TAG] = SIM_BUILD
    return ng


def ensure_group():
    ng = bpy.data.node_groups.get(GROUP)
    current = SIM_BUILD                   # not VERSION: an update that leaves this tree alone must not rebuild it
    if ng is not None and (GROUP_MARK not in ng.interface.items_tree or ng.get(BUILD_TAG) != current):
        ng.name = GROUP + " (old)"        # built by another version: retire it, Sync rebuilds the controllers
        ng = None
    return ng or build_group()


# ------------------------------------------------------------------ influencers (per-object settings + the mirror mesh)
def _infl_update(self, context):
    sync_mirror(context.scene)


class BBCrowdInfluencer(bpy.types.PropertyGroup):
    on: bpy.props.BoolProperty(name="Influences the crowd", default=False, update=_infl_update)
    gaze: bpy.props.FloatProperty(name="Gaze", default=0.0, min=-1.0, max=1.0, update=_infl_update,
                                  description="+1 the crowd looks at this; −1 they look away; 0 ignored")
    gaze_radius: bpy.props.FloatProperty(name="Gaze radius", default=40.0, min=1.0, max=500.0, update=_infl_update,
                                         description="How far the gaze pull reaches (m)")
    move: bpy.props.FloatProperty(name="Move", default=0.0, min=-1.0, max=1.0, update=_infl_update,
                                  description="−1 members step aside to let this through; +1 they drift toward it; 0 ignored")
    radius: bpy.props.FloatProperty(name="Radius", default=2.5, min=0.2, max=30.0, update=_infl_update,
                                    description="Corridor half-width for stepping aside / reach of the pull (m)")


def influencers(scene):
    return [o for o in scene.objects if getattr(o, "bb_crowd", None) is not None and o.bb_crowd.on
            and not o.get(MIRROR_KEY) and crowd_mod(o) is None]


def crowd_coll(scene):
    """Where this scene's crowd objects live: inside the STAGE layer of a staging, at the root otherwise."""
    st = bbstage()
    if st is not None and st.is_staging(scene):
        roots = st.layer_colls(scene, "STAGE")
        if roots:
            name = f"Crowd · {st.staging_label(scene)}"
            c = roots[0].children.get(name)
            if c is None:
                c = bpy.data.collections.get(name) or bpy.data.collections.new(name)
                if c.name not in roots[0].children:
                    roots[0].children.link(c)
            return c
    name = f"CROWD · {scene.name}"
    c = bpy.data.collections.get(name) or bpy.data.collections.new(name)
    if c.name not in scene.collection.children:
        scene.collection.children.link(c)
    return c


def mirror_of(scene, create=True):
    mine = [o for o in scene.objects if o.get(MIRROR_KEY) == scene.name]
    ob = mine[0] if mine else None
    for extra in mine[1:]:
        _remove_object(extra)
    if ob is None and create:
        me = bpy.data.meshes.new(f"BB Crowd · influencers · {scene.name}")
        ob = bpy.data.objects.new(f"BB Crowd · influencers · {scene.name}", me)
        ob[MIRROR_KEY] = scene.name
        ob.hide_render = True
        ob.hide_select = True
        ob.display_type = 'WIRE'
        crowd_coll(scene).objects.link(ob)
    return ob


def _remove_object(ob):
    data = ob.data
    bpy.data.objects.remove(ob, do_unlink=True)
    if data is not None and data.users == 0:
        try:
            bpy.data.meshes.remove(data)
        except Exception:
            pass


def sync_mirror(scene):
    """Rebuild the mirror mesh: two hooked vertices per influencer, weights as vertex attributes."""
    infl = influencers(scene)
    mir = mirror_of(scene)
    me = mir.data
    mir.matrix_world = Matrix.Identity(4)
    for m in list(mir.modifiers):
        mir.modifiers.remove(m)
    bm = bmesh.new()
    for _ in infl:
        v0 = bm.verts.new((0.0, 0.0, 0.0))
        v1 = bm.verts.new((0.0, 1.0, 0.0))
        bm.edges.new((v0, v1))
    bm.to_mesh(me)
    bm.free()
    for nm, kind in (("kind", 'INT'), ("gaze", 'FLOAT'), ("gaze_radius", 'FLOAT'), ("move", 'FLOAT'), ("radius", 'FLOAT')):
        if nm not in me.attributes:
            me.attributes.new(nm, kind, 'POINT')
    for i, ob in enumerate(infl):
        s = ob.bb_crowd
        for j, (kind, gaze, grad, move, rad) in enumerate(((0, s.gaze, s.gaze_radius, s.move, s.radius), (1, 0.0, 0.0, 0.0, 0.0))):
            vi = 2 * i + j
            me.attributes["kind"].data[vi].value = kind
            me.attributes["gaze"].data[vi].value = gaze
            me.attributes["gaze_radius"].data[vi].value = grad
            me.attributes["move"].data[vi].value = move
            me.attributes["radius"].data[vi].value = rad
        h = mir.modifiers.new(f"Hook · {ob.name}", 'HOOK')
        h.object = ob
        h.vertex_indices_set([2 * i, 2 * i + 1])
        h.matrix_inverse = Matrix.Identity(4)
        h.center = (0.0, 0.0, 0.0)
        h.falloff_type = 'NONE'
    me.update()
    for z in zones(scene):
        set_input(crowd_mod(z), "Influencers", mir)
    for c in choreo_crowds(scene):          # choreographed crowds keep off the same characters (drawn only)
        s = ch_sock(c, "Influencers")
        if s is not None and s.value != mir:
            s.value = mir
            c.update_tag()
    return mir


# ------------------------------------------------------------------ helpers
def crowd_mod(ob):
    if ob is None or ob.type != 'MESH':
        return None
    m = ob.modifiers.get(MOD)
    return m if (m is not None and m.type == 'NODES' and m.node_group is not None) else None


def sock_of(mod, name):
    ident = mod.node_group.interface.items_tree[name].identifier
    return getattr(mod.properties.inputs, ident)


def set_input(mod, name, value):
    sock_of(mod, name).value = value
    try:
        mod.id_data.update_tag()        # a .value change alone is not always picked up by the depsgraph
    except Exception:
        pass


def key_input(mod, name, value, frame):
    s = sock_of(mod, name)
    s.value = value
    s.keyframe_insert("value", frame=frame)


def member_count(context, ob):
    dg = context.evaluated_depsgraph_get()
    return sum(1 for i in dg.object_instances if i.is_instance and i.parent and i.parent.original == ob)


def zones(scene):
    return [o for o in scene.objects if crowd_mod(o) is not None]


def active_zone(context):
    ob = context.scene.bb_crowd_obj
    if crowd_mod(ob) is None or ob.name not in context.scene.objects:
        zs = zones(context.scene)
        ob = zs[0] if zs else None
    return ob


def _zone_poll(self, ob):
    return crowd_mod(ob) is not None


def plane_mesh(name, w, d, nx, ny):
    me = bpy.data.meshes.new(name)
    bm = bmesh.new()
    bmesh.ops.create_grid(bm, x_segments=nx, y_segments=ny, size=1.0)
    for v in bm.verts:
        v.co.x *= w / 2.0
        v.co.y *= d / 2.0
    bm.to_mesh(me)
    bm.free()
    return me


def peg_material_for(ob):
    """One material per controller, so each crowd can have its own colour."""
    m = crowd_mod(ob)
    mat = None
    try:
        mat = sock_of(m, "Peg material").value
    except Exception:
        pass
    if mat is None:
        name = f"BB Crowd peg · {ob.name}"
        mat = bpy.data.materials.get(name)
        if mat is None:
            mat = bpy.data.materials.new(name)
            mat.diffuse_color = CROWD_GREY
            mat.use_nodes = True
            bsdf = next((n for n in mat.node_tree.nodes if n.type == 'BSDF_PRINCIPLED'), None)
            if bsdf is not None:
                bsdf.inputs["Base Color"].default_value = CROWD_GREY
        set_input(m, "Peg material", mat)
    return mat


def upgrade_zone(scene, ob):
    """A controller made with an older version: give it the current group and the mirror."""
    m = crowd_mod(ob)
    ng = ensure_group()
    if m.node_group is not ng:
        old = {}
        for nm in ZONE_INPUTS:
            try:
                old[nm] = sock_of(m, nm).value
            except Exception:
                pass
        m.node_group = ng
        # the modifier keeps values by socket identifier, and identifiers are reused across versions:
        # write every input explicitly (the old value by name, else the new group's default)
        for item in ng.interface.items_tree:
            if item.item_type != 'SOCKET' or item.in_out != 'INPUT' or item.socket_type == 'NodeSocketGeometry':
                continue
            if item.name == "Influencers":
                continue
            v = old.get(item.name, getattr(item, "default_value", None))
            try:
                set_input(m, item.name, v)
            except Exception:
                pass
    ob[CTRL_KEY] = True
    set_input(m, "Influencers", mirror_of(scene))
    peg_material_for(ob)


def sim_start(scene):
    return scene.simulation_frame_start if scene.use_custom_simulation_range else scene.frame_start


def reset_sim(context, ob):
    """Drop the cached simulation of this controller and go back to the first frame, so it is re-born."""
    sc = context.scene
    try:
        for o in sc.objects:
            o.select_set(False)
        ob.select_set(True)
        context.view_layer.objects.active = ob
        if hasattr(bpy.ops.object, "simulation_nodes_cache_delete"):
            bpy.ops.object.simulation_nodes_cache_delete(selected=True)
    except Exception:
        pass
    sc.frame_set(sim_start(sc))


# ================================================================== choreographed crowds (v0.5)
CH_GROUP = "BB Crowd Choreo"
CH_MOD = "BB Crowd Choreo"
CH_TAG = "bb_crowd_choreo"            # on the crowd object
CUE_TAG = "bb_crowd_cue"              # on a cue object: its name as a cue
CH_BACK = " · back"
CH_GREY = (0.42, 0.44, 0.47, 1.0)
CH_SIG = "bb_crowd_choreo_build"      # on the node group: the cue list its nodes were built for
CH_BUILD = 3                          # bump when the choreography NODES change: crowds are rebuilt on their next sync
CH_HELPERS = {"cue": f"{CH_GROUP} · one cue · v{CH_BUILD}",          # shared by every crowd: what one cue adds
              "members": f"{CH_GROUP} · members · v{CH_BUILD}"}      # shared by every crowd: everybody drawn as a peg
CH_TURN_BIAS = 1e-5                   # a turn of exactly 180 degrees goes to the left (nodes and choreo_state agree)
MIN_GAP = 0.55                        # generators: nobody ends closer than this to anybody else (m)
LINE_CLEAR = 0.45                     # Make way for: this much stays clear on each side of the walker's line (m)
CH_PANELS = (("cues", "Cues: 0 = at rest, 1 = played. The second slider sends them back"),
             ("members", "Members"),
             ("cams", "Cameras and characters (drawn only)"))
# name, socket type, default, min, max, tooltip, panel
CH_INPUTS = (
    ("Peg height", 'NodeSocketFloat', 1.70, 0.5, 2.3, "How tall a person in the crowd is (m), measured like a BB Stage character", "members"),
    ("Height variation", 'NodeSocketFloat', 0.07, 0.0, 0.3, "People are up to this fraction taller or shorter than the height", "members"),
    ("Idle turn", 'NodeSocketFloat', 2.0, 0.0, 45.0, "How far a standing person's head wanders, slowly (degrees). Keep it small", "members"),
    ("Idle speed", 'NodeSocketFloat', 0.12, 0.0, 5.0, "How fast the head wanders", "members"),
    ("Bob height", 'NodeSocketFloat', 0.07, 0.0, 0.5, "How high an excited person bounces (m)", "members"),
    ("Bob rate", 'NodeSocketFloat', 2.1, 0.1, 6.0, "Bounces per second of an excited person", "members"),
    ("Peg material", 'NodeSocketMaterial', None, None, None, "The colour of the people in this crowd", "members"),
    ("Seed", 'NodeSocketInt', 1, 0, 10000, "Shuffles who is taller, who bounces when", "members"),
    ("Lens clearance", 'NodeSocketFloat', 0.0, 0.0, 3.0,
     "0 = off (the default). Above 0, people standing right in front of the camera you are looking through are NOT "
     "DRAWN: this far to each side at the lens, narrowing to nothing at the reach. They come back on the next camera "
     "cut, so people pop in and out. Better: Make room around the camera, and let that cue stay", "cams"),
    ("Lens reach", 'NodeSocketFloat', 3.0, 0.0, 15.0, "How far in front of the lens people are left out (m)", "cams"),
    ("Keep off", 'NodeSocketFloat', 0.5, 0.0, 2.0, "Nobody is drawn closer than this to a character on the Influencers list (m)", "cams"),
    ("Influencers", 'NodeSocketObject', None, None, None, "The characters to keep off (set by the add-on)", "cams"),
    ("Preview", 'NodeSocketInt', 0, 0, 1000000, "Set by Edit Positions: shows one reaction fully played while it is edited", "cams"),
)
CH_INPUT_NAMES = {row[0] for row in CH_INPUTS} | {"Geometry"}
CUE_KINDS = [
    ('HAND', "By hand", "People placed by hand in Edit Positions"),
    ('LOOK', "Look at", "People turn to look at something"),
    ('ROOM', "Make room around", "People step back to leave a clear space around something"),
    ('BACK', "Step back from", "People recoil from something"),
    ('WAY', "Make way for", "People step aside just ahead of somebody walking through and close in behind"),
    ('LANE', "Open a lane", "People clear a straight corridor between two things"),
    ('MOOD', "Cheer", "People get excited (or frightened) on the spot"),
]
CUE_LABEL = {k: label for k, label, _d in CUE_KINDS}
CUE_ICON = {'HAND': 'EDITMODE_HLT', 'LOOK': 'HIDE_OFF', 'ROOM': 'PIVOT_BOUNDBOX', 'BACK': 'BACK', 'WAY': 'TRACKING',
            'LANE': 'ARROW_LEFTRIGHT', 'MOOD': 'FUND'}
# the numbers of each kind, as the panel shows them on the cue (property of the cue, label)
CUE_NUMBERS = {
    'LOOK': (("radius", "Within (m)"), ("share", "How many"), ("near_bias", "Nearly everybody close by"), ("seed", "Shuffle")),
    'ROOM': (("radius", "Clear space (m)"), ("seed", "Shuffle")),
    'BACK': (("reach", "Within (m)"), ("amount", "Step (m)"), ("share", "How many"), ("duck", "Frightened"), ("cheer", "Excited"),
             ("face_away", "Turn away"), ("seed", "Shuffle")),
    'WAY': (("reach", "Within (m)"), ("amount", "Sidestep (m)"), ("look", "Watch the walker"), ("seed", "Shuffle")),
    'LANE': (("half_width", "Half width (m)"), ("seed", "Shuffle")),
    'MOOD': (("radius", "Within (m)"), ("mood", "Mood"), ("share", "How many"), ("seed", "Shuffle")),
}
_CH_QUIET = {"on": False}             # True while the add-on itself writes cue properties (their updates stay quiet)
_EDIT_PREV = {}                       # crowd name -> what was selected before Edit Positions


def choreo_mod(ob):
    """The choreography modifier of a crowd object, or None."""
    if ob is None or ob.type != 'MESH':
        return None
    m = ob.modifiers.get(CH_MOD)
    return m if (m is not None and m.type == 'NODES') else None


def choreo_crowds(scene):
    """The choreographed crowds of a scene."""
    return [o for o in scene.objects if o.type == 'MESH' and o.get(CH_TAG)]


def choreo_members(crowd):
    """How many people the crowd has."""
    return len(crowd.data.vertices) // 2


def choreo_rest(crowd, i):
    """(where member i stands, the unit vector it faces) at rest, in the crowd's own space."""
    v = crowd.data.vertices
    p = v[2 * i].co.copy()
    f = v[2 * i + 1].co - p
    f.z = 0.0
    return p, (f.normalized() if f.length > 1e-6 else Vector((0.0, 1.0, 0.0)))


def choreo_cue(crowd, name):
    """The crowd's cue of this name (an item of crowd.bb_crowd_cues), or None."""
    for c in crowd.bb_crowd_cues:
        if c.name == name:
            return c
    return None


def cue_sliders(crowd, cue):
    """(Play, Back): the cue's two keyable values on the crowd's modifier, or (None, None) before choreo_sync."""
    m = choreo_mod(crowd)
    if m is None or m.node_group is None or not cue.sock or not cue.sock_back:
        return None, None
    return getattr(m.properties.inputs, cue.sock, None), getattr(m.properties.inputs, cue.sock_back, None)


def ch_sock(crowd, name):
    """A named input of the crowd's modifier that is not a cue slider (Peg height, Keep off, …), or None."""
    m = choreo_mod(crowd)
    if m is None or m.node_group is None:
        return None
    cue_ids = set()
    for c in crowd.bb_crowd_cues:
        cue_ids.add(c.sock)
        cue_ids.add(c.sock_back)
    for it in m.node_group.interface.items_tree:
        if it.item_type == 'SOCKET' and it.in_out == 'INPUT' and it.name == name and it.identifier not in cue_ids:
            return getattr(m.properties.inputs, it.identifier, None)
    return None


def choreo_editing(crowd):
    """The cue that Edit Positions is showing right now, or None."""
    s = ch_sock(crowd, "Preview")
    uid = int(s.value) if s is not None else 0
    if uid:
        for c in crowd.bb_crowd_cues:
            if c.uid == uid:
                return c
    return None


def _scene_of(ob):
    sc = bpy.context.scene
    if sc is not None and sc.objects.get(ob.name) == ob:
        return sc
    return ob.users_scene[0] if ob.users_scene else sc


def _cue_clean_name(crowd, name, skip=None):
    """A cue name that is not empty, not the name of another cue and not the name of a crowd setting."""
    name = " ".join(str(name).split())
    while name.endswith(CH_BACK.strip()):
        name = name[:-len(CH_BACK.strip())].rstrip(" ·")
    name = name or "Cue"
    if name in CH_INPUT_NAMES:
        name += " cue"
    me = skip.as_pointer() if skip is not None else None
    taken = {c.name for c in crowd.bb_crowd_cues if c.as_pointer() != me}
    base, k = name, 2
    while name in taken:
        name = f"{base} {k}"
        k += 1
    return name


def _cue_name_update(self, context):
    if _CH_QUIET["on"]:
        return
    crowd = self.id_data
    name = _cue_clean_name(crowd, self.name, skip=self)
    if name != self.name:
        _CH_QUIET["on"] = True
        try:
            self.name = name
        finally:
            _CH_QUIET["on"] = False
    choreo_sync(crowd)              # renames the cue object and its two sliders; their keys stay


def _cue_shape_update(self, context):
    """Wave <-> Together and Snap take effect at once: they are two values on the cue's node."""
    if _CH_QUIET["on"]:
        return
    crowd = self.id_data
    m = choreo_mod(crowd)
    ng = m.node_group if m is not None else None
    node = ng.nodes.get(f"cue {self.uid}") if ng is not None else None
    if node is not None and "Width" in node.inputs and "Snap" in node.inputs:
        node.inputs["Width"].default_value = self.width
        node.inputs["Snap"].default_value = self.snap
    else:
        choreo_sync(crowd, force=True)
    crowd.update_tag()


class BBCrowdCue(bpy.types.PropertyGroup):
    """One reaction of a choreographed crowd: a row of the cue list (Object.bb_crowd_cues)."""
    name: bpy.props.StringProperty(name="Reaction", update=_cue_name_update,
                                   description="What this reaction is called. Double-click to rename it")
    obj: bpy.props.PointerProperty(type=bpy.types.Object, name="Cue object",
                                   description="The hidden object that holds where everybody stands in this reaction")
    uid: bpy.props.IntProperty(default=0)
    sock: bpy.props.StringProperty()            # identifier of the Play slider on the modifier
    sock_back: bpy.props.StringProperty()       # identifier of the Back slider
    kind: bpy.props.EnumProperty(name="Kind", items=CUE_KINDS, default='HAND')
    width: bpy.props.FloatProperty(
        name="Wave ↔ Together", default=0.4, min=0.02, max=1.0, subtype='FACTOR', update=_cue_shape_update,
        description="Low: the reaction travels through the crowd like a wave, each person moving in their own short "
                    "moment. High: everybody moves together")
    snap: bpy.props.FloatProperty(
        name="Snap", default=2.0, min=1.0, max=5.0, update=_cue_shape_update,
        description="How sudden each person's move is. 1 = even, 2 = quick start and soft settle, 3 and up = a startle")
    seconds: bpy.props.FloatProperty(name="Seconds", default=1.5, min=0.04, soft_max=20.0, step=10, precision=1,
                                     description="How long Play From Here and Back From Here take")
    # what made it, so Update From Source can make it again (the panel shows these: change one, press Update)
    source: bpy.props.PointerProperty(type=bpy.types.Object, name="Reacts to", description="What the crowd reacts to in this reaction")
    source_b: bpy.props.PointerProperty(type=bpy.types.Object, name="Lane ends at", description="Where the lane ends")
    point: bpy.props.FloatVectorProperty(size=3)         # where the source was (crowd space); used when it is gone
    point_b: bpy.props.FloatVectorProperty(size=3)
    frame: bpy.props.IntProperty(name="On frame", default=1, description="The frame on which the source is read: where it stands then is what the crowd reacts to")
    win_a: bpy.props.IntProperty(name="Walk starts", default=0, description="The frame the walk starts on")
    win_b: bpy.props.IntProperty(name="Walk ends", default=0, description="The frame the walk ends on")
    key_a: bpy.props.IntProperty(default=0)              # the walk its Play and Back keys were made for
    key_b: bpy.props.IntProperty(default=0)
    radius: bpy.props.FloatProperty(name="Within (m)", default=6.0, min=0.3, soft_max=80.0, description="How far around the source this reaction reaches")
    reach: bpy.props.FloatProperty(name="Within (m)", default=6.0, min=0.3, soft_max=60.0, description="People this close react")
    amount: bpy.props.FloatProperty(name="Step (m)", default=1.0, min=0.0, soft_max=5.0, description="How far the nearest people step; less further away")
    share: bpy.props.FloatProperty(name="How many", default=1.0, min=0.0, max=1.0, subtype='FACTOR', description="The share of the people in reach that reacts")
    near_bias: bpy.props.BoolProperty(name="Nearly everybody close by", default=True, description="Close to it nearly everybody looks; far away only the share above")
    duck: bpy.props.FloatProperty(name="Frightened", default=0.25, min=0.0, max=1.0, subtype='FACTOR', description="The share that shrinks")
    cheer: bpy.props.FloatProperty(name="Excited", default=0.2, min=0.0, max=1.0, subtype='FACTOR', description="The share that bounces")
    face_away: bpy.props.FloatProperty(name="Turn away", default=0.0, min=0.0, max=1.0, subtype='FACTOR', description="The share that also turns their back")
    look: bpy.props.FloatProperty(name="Watch the walker", default=0.5, min=0.0, max=1.0, subtype='FACTOR', description="The share that turns to the walker")
    half_width: bpy.props.FloatProperty(name="Half width (m)", default=1.4, min=0.3, soft_max=10.0, description="Clear space on each side of the lane's line")
    mood: bpy.props.FloatProperty(name="Mood", default=1.0, min=-1.0, max=1.0, description="+1 excited: they bounce. -1 frightened: they shrink")
    seed: bpy.props.IntProperty(name="Shuffle", default=0, min=0, description="Another number, another pick of who does what")


def _ch_data_path(m, ident):
    return f'modifiers["{bpy.utils.escape_identifier(m.name)}"].properties.inputs.{ident}.value'


def _ch_fcurves(crowd, idents):
    """[(channelbag, fcurve)]: the crowd's keys on the sliders with these identifiers."""
    ad = crowd.animation_data
    act = ad.action if ad is not None else None
    m = choreo_mod(crowd)
    if act is None or m is None:
        return []
    paths = {_ch_data_path(m, i) for i in idents if i}
    slot = getattr(ad, "action_slot", None)
    out = []
    for layer in act.layers:
        for strip in layer.strips:
            for cb in strip.channelbags:
                if slot is not None and getattr(cb, "slot_handle", slot.handle) != slot.handle:
                    continue
                for fc in cb.fcurves:
                    if fc.data_path in paths:
                        out.append((cb, fc))
    return out


def _choreo_adopt(crowd):
    """A crowd built by the stand-alone crowd_choreo.py script has cue objects but no cue list: list them, so the
    panel shows them and their sliders (found by name in choreo_sync) keep their keys."""
    cues = crowd.bb_crowd_cues
    known = {c.obj for c in cues if c.obj is not None}
    legacy = sorted((o for o in crowd.children if o.get(CUE_TAG) and o.type == 'MESH' and o not in known),
                    key=lambda o: int(o.get("bb_cue_order", 0)))
    if not legacy:
        return 0
    _CH_QUIET["on"] = True
    try:
        for ob in legacy:
            name = _cue_clean_name(crowd, ob[CUE_TAG])
            uid = max((c.uid for c in cues), default=0) + 1
            it = cues.add()
            it.name, it.obj, it.uid, it.kind = name, ob, uid, 'HAND'
            it.width = min(1.0, max(0.02, float(ob.get("bb_cue_width", 0.4))))
            it.snap = min(5.0, max(1.0, float(ob.get("bb_cue_snap", 2.0))))
    finally:
        _CH_QUIET["on"] = False
    return len(legacy)


def choreo_sync(crowd, force=False):
    """Bring the crowd's modifier in line with its cue list: call after any change (cheap when nothing changed).

    One node group per crowd, kept for good. Sliders are added, renamed and removed one by one, so the others keep
    their identifiers, and with them their values and keys. A removed cue takes its keys with it. The nodes are
    rebuilt only when the cue list really changed."""
    if crowd is None or crowd.type != 'MESH' or not crowd.get(CH_TAG):
        return None
    m = choreo_mod(crowd) or crowd.modifiers.new(CH_MOD, 'NODES')
    ng = m.node_group
    gname = f"{CH_GROUP} · {crowd.name}"
    fresh = ng is None
    if fresh:
        ng = bpy.data.node_groups.new(gname, "GeometryNodeTree")
        ng.is_modifier = True
        m.node_group = ng
    else:
        # a crowd duplicated in Blender (Shift+D) still shares the node group and the cue objects of the one it
        # was copied from: it gets its own, so that editing or deleting a cue here leaves the other crowd alone
        if ng.users > 1 and any(o != crowd and getattr(choreo_mod(o), "node_group", None) == ng for o in bpy.data.objects):
            ng = ng.copy()                  # same sliders, same identifiers: values and keys carry over
            m.node_group = ng
            ad = crowd.animation_data       # and its own keys, if the copy still shares the action
            if ad is not None and ad.action is not None and ad.action.users > 1:
                slot = ad.action_slot.identifier if getattr(ad, "action_slot", None) is not None else ""
                ad.action = ad.action.copy()
                if slot and (ad.action_slot is None or ad.action_slot.identifier != slot) and slot in ad.action.slots:
                    ad.action_slot = ad.action.slots[slot]
        for cue in crowd.bb_crowd_cues:
            ob = cue.obj
            if ob is not None and ob.parent is not None and ob.parent != crowd and ob.parent.get(CH_TAG):
                own = ob.copy()
                own.data = ob.data.copy()
                own.parent = crowd
                for c in crowd.users_collection:
                    c.objects.link(own)
                cue.obj = own
        if ng.name != gname and bpy.data.node_groups.get(gname) is None:
            ng.name = gname                 # the crowd was renamed (or duplicated)
    _choreo_adopt(crowd)
    cues = crowd.bb_crowd_cues
    I = ng.interface
    made = []                               # (identifier, value): written on the modifier explicitly below

    def sockets():
        return [it for it in I.items_tree if it.item_type == 'SOCKET']

    kinds = {(it.in_out, it.socket_type) for it in sockets()}
    if ('INPUT', 'NodeSocketGeometry') not in kinds:
        I.new_socket("Geometry", in_out='INPUT', socket_type='NodeSocketGeometry')
    if ('OUTPUT', 'NodeSocketGeometry') not in kinds:
        I.new_socket("Geometry", in_out='OUTPUT', socket_type='NodeSocketGeometry')
    panels = {}
    for key, title in CH_PANELS:
        p = next((it for it in I.items_tree if it.item_type == 'PANEL' and it.name == title), None)
        panels[key] = p if p is not None else I.new_panel(title)
    p_cues = panels["cues"].as_pointer()

    def in_cue_panel(it):
        return it.parent is not None and it.parent.as_pointer() == p_cues

    # the crowd's own settings
    for name, kind, default, mn, mx, desc, pkey in CH_INPUTS:
        s = next((it for it in sockets() if it.in_out == 'INPUT' and it.name == name and not in_cue_panel(it)), None)
        if s is None:
            s = I.new_socket(name, in_out='INPUT', socket_type=kind, parent=panels[pkey])
            if default is not None:
                s.default_value = default
                made.append((s.identifier, default))
            if mn is not None:
                s.min_value, s.max_value = mn, mx
        if s.description != desc:
            s.description = desc
        if name == "Preview" and not s.hide_in_modifier:
            s.hide_in_modifier = True
    # one Play and one Back slider per cue
    by_id = {it.identifier: it for it in sockets() if it.in_out == 'INPUT'}
    used = set()
    for cue in cues:
        if not cue.uid:
            cue.uid = max((c.uid for c in cues), default=0) + 1
        for field, label, desc in (
                ("sock", cue.name, f"Play '{cue.name}': 0 = nobody has reacted, 1 = everybody has"),
                ("sock_back", cue.name + CH_BACK, f"Send the people of '{cue.name}' back to where they stood: 0 = still there, 1 = all back")):
            s = by_id.get(getattr(cue, field)) if getattr(cue, field) else None
            if s is not None and (s.identifier in used or not in_cue_panel(s)):
                s = None
            if s is None:                   # a crowd from crowd_choreo.py: its sliders are found by name
                s = next((it for it in by_id.values() if in_cue_panel(it) and it.name == label and it.identifier not in used
                          and not any(it.identifier in (c.sock, c.sock_back) for c in cues)), None)
            if s is None:
                s = I.new_socket(label, in_out='INPUT', socket_type='NodeSocketFloat', parent=panels["cues"])
                s.default_value, s.min_value, s.max_value = 0.0, 0.0, 1.0
                s.subtype = 'FACTOR'
                by_id[s.identifier] = s
                made.append((s.identifier, 0.0))
            if s.name != label:
                s.name = label
            if s.description != desc:
                s.description = desc
            if getattr(cue, field) != s.identifier:
                setattr(cue, field, s.identifier)
            used.add(s.identifier)
        ob = cue.obj
        if ob is not None:
            if ob.get(CUE_TAG) != cue.name:
                ob[CUE_TAG] = cue.name
            want = f"{crowd.name} · cue · {cue.name}"
            if ob.name != want and bpy.data.objects.get(want) is None:
                ob.name = want
    # sliders of cues that are gone: out, with their keys
    dead = [it for it in by_id.values() if in_cue_panel(it) and it.identifier not in used]
    if dead:
        for cb, fc in _ch_fcurves(crowd, [it.identifier for it in dead]):
            cb.fcurves.remove(fc)
        for it in dead:
            by_id.pop(it.identifier, None)
            I.remove(it)
    # the sliders follow the order of the list
    order = [i for cue in cues for i in (cue.sock, cue.sock_back)]
    for want, ident in enumerate(order):
        s = by_id.get(ident)
        if s is not None and s.position != want:
            I.move_to_parent(s, panels["cues"], want)
    # nodes
    sig = _choreo_signature(crowd)
    if force or fresh or ng.get(CH_SIG) != sig or not _choreo_nodes_ok(crowd, ng):
        _choreo_build_nodes(crowd, ng)
        ng[CH_SIG] = sig
    else:
        for cue in cues:                    # a renamed cue: its node says so too
            node = ng.nodes.get(f"cue {cue.uid}")
            if node is not None and node.label != cue.name:
                node.label = cue.name
    # a modifier keeps values by socket identifier: every input made now is written explicitly
    for ident, value in made:
        s = getattr(m.properties.inputs, ident, None)
        if s is not None:
            s.value = value
    crowd.update_tag()
    return m


def _cue_ok(cue):
    return cue.obj is not None and cue.obj.type == 'MESH' and bool(cue.sock) and bool(cue.sock_back)


def _choreo_signature(crowd):
    """What the crowd's own nodes depend on: the build of the node trees and which cues there are (not their
    order, names or timing)."""
    return "|".join([f"build {CH_BUILD}"]
                    + sorted(f"{c.uid}:{c.sock}:{c.sock_back}" for c in crowd.bb_crowd_cues if _cue_ok(c)))


def _choreo_nodes_ok(crowd, ng):
    fin = ng.nodes.get("Members")
    if ng.nodes.get("Out") is None or fin is None or getattr(fin, "node_tree", None) is None:
        return False
    for c in crowd.bb_crowd_cues:
        if not _cue_ok(c):
            continue
        n = ng.nodes.get(f"cue {c.uid}")
        if n is None or getattr(n, "node_tree", None) is None or n.inputs["Cue"].default_value != c.obj:
            return False
    return True


class _NB:
    """Shorthands for building the choreography trees."""
    AK = {'FLOAT_VECTOR': "Attribute_Vector", 'FLOAT': "Attribute_Float", 'INT': "Attribute_Int"}

    def __init__(self, ng):
        self.nodes, self.links = ng.nodes, ng.links

    def N(self, kind, nm=None, **props):
        n = self.nodes.new(kind)
        if nm:
            n.name = n.label = nm
        for k, v in props.items():
            setattr(n, k, v)
        return n

    def L(self, a, ao, b, bi):
        self.links.new(_sock(a, ao, True) if isinstance(ao, str) else a.outputs[ao],
                       _sock(b, bi) if isinstance(bi, str) else b.inputs[bi])

    def math(self, op, nm, a=None, b=None, c=None, clamp=False, **defaults):
        n = self.N("ShaderNodeMath", nm, operation=op)
        for i, src in enumerate((a, b, c)):
            if src is not None:
                self.L(src[0], src[1], n, i)
        for i, v in defaults.items():
            n.inputs[int(i[1:])].default_value = v
        n.use_clamp = clamp
        return n

    def vop(self, op, nm, a, ao, b=None, bo=None, scale=None):
        n = self.N("ShaderNodeVectorMath", nm, operation=op)
        self.L(a, ao, n, 0)
        if b is not None:
            self.L(b, bo, n, 1)
        if scale is not None:
            self.L(scale[0], scale[1], n, "Scale")
        return n

    def xy(self, vec_node, out, nm):
        sep = self.N("ShaderNodeSeparateXYZ", nm + " sep")
        self.L(vec_node, out, sep, "Vector")
        comb = self.N("ShaderNodeCombineXYZ", nm + " xy")
        self.L(sep, "X", comb, "X")
        self.L(sep, "Y", comb, "Y")
        comb.inputs["Z"].default_value = 0.0
        return comb, sep

    def smooth(self, nm, src, lo, hi, out_lo=0.0, out_hi=1.0):
        n = self.N("ShaderNodeMapRange", nm, interpolation_type='SMOOTHSTEP', clamp=True)
        self.L(src[0], src[1], n, "Value")
        n.inputs["From Min"].default_value = lo
        n.inputs["From Max"].default_value = hi
        n.inputs["To Min"].default_value = out_lo
        n.inputs["To Max"].default_value = out_hi
        return n

    def attr(self, nm, kind='FLOAT'):
        a = self.N("GeometryNodeInputNamedAttribute", "read " + nm, data_type=kind)
        a.inputs["Name"].default_value = nm
        return a

    def sample(self, nm, geo, go_key, kind, value, vo, index):
        s = self.N("GeometryNodeSampleIndex", nm, data_type=kind, domain='POINT')
        self.L(geo, go_key, s, "Geometry")
        self.L(value, vo, s, "Value")
        self.L(index[0], index[1], s, "Index")
        return s

    def rest_facing(self, gi, geo_key):
        """(unit facing at rest, its x and y): from each member's pair of vertices in the crowd mesh."""
        self.idx = self.N("GeometryNodeInputIndex", "Index")
        self.pos = self.N("GeometryNodeInputPosition", "Position")
        self.nxt = self.math('ADD', "index + 1", (self.idx, "Index"), i1=1.0)
        look0 = self.sample("look at rest", gi, geo_key, 'FLOAT_VECTOR', self.pos, "Position", (self.nxt, "Value"))
        f0_xy, _s = self.xy(self.vop('SUBTRACT', "look - stand", look0, "Value", self.pos, "Position"), "Vector", "facing at rest")
        f0 = self.vop('NORMALIZE', "facing dir at rest", f0_xy, "Vector")
        f0s = self.N("ShaderNodeSeparateXYZ", "facing at rest x y")
        self.L(f0, "Vector", f0s, "Vector")
        return f0, f0s

    def tidy(self, per_row=20):
        for i, n in enumerate(self.nodes):
            n.location = ((i % per_row) * 220, -(i // per_row) * 240)


def _helper_socket(I, nm, kind, in_out='INPUT', default=None, mn=None, mx=None, desc=""):
    s = I.new_socket(nm, in_out=in_out, socket_type=kind)
    if default is not None:
        s.default_value = default
    if mn is not None:
        s.min_value, s.max_value = mn, mx
    if desc:
        s.description = desc
    return s


def _build_cue_group(ng):
    """What ONE cue adds for every member, on top of what the cues before it add: a move, a turn, a mood."""
    I = ng.interface
    _helper_socket(I, "Crowd", 'NodeSocketGeometry')
    _helper_socket(I, "Cue", 'NodeSocketObject', desc="The cue object: everybody's pose when the cue is fully played")
    _helper_socket(I, "Play", 'NodeSocketFloat', default=0.0, mn=0.0, mx=1.0)
    _helper_socket(I, "Back", 'NodeSocketFloat', default=0.0, mn=0.0, mx=1.0)
    _helper_socket(I, "Width", 'NodeSocketFloat', default=0.4, mn=0.02, mx=1.0, desc="Wave <-> Together")
    _helper_socket(I, "Snap", 'NodeSocketFloat', default=2.0, mn=1.0, mx=5.0)
    _helper_socket(I, "Number", 'NodeSocketInt', default=0, desc="The cue's number, for Edit Positions")
    _helper_socket(I, "Preview", 'NodeSocketInt', default=0, desc="The number of the cue being edited, 0 = none")
    _helper_socket(I, "Move so far", 'NodeSocketVector')
    _helper_socket(I, "Turn so far", 'NodeSocketFloat')
    _helper_socket(I, "Mood so far", 'NodeSocketFloat')
    _helper_socket(I, "Move", 'NodeSocketVector', in_out='OUTPUT')
    _helper_socket(I, "Turn", 'NodeSocketFloat', in_out='OUTPUT')
    _helper_socket(I, "Mood", 'NodeSocketFloat', in_out='OUTPUT')
    nb = _NB(ng)
    N, L, math_, vop, xy, smooth, attr, sample = nb.N, nb.L, nb.math, nb.vop, nb.xy, nb.smooth, nb.attr, nb.sample
    AF = nb.AK['FLOAT']
    ng.nodes.clear()
    gi = N("NodeGroupInput", "In")
    go = N("NodeGroupOutput", "Out")
    _f0, f0s = nb.rest_facing(gi, "Crowd")
    idx, pos, nxt = nb.idx, nb.pos, nb.nxt
    # Edit Positions shows ONE cue fully played, whatever the sliders say (Preview = that cue's number)
    prev_on = N("FunctionNodeCompare", "previewing?", data_type='INT', operation='GREATER_THAN')
    L(gi, "Preview", prev_on, "A_INT")
    _sock(prev_on, "B_INT").default_value = 0
    not_prev = math_('SUBTRACT', "1 - previewing", None, (prev_on, "Result"), i0=1.0)
    is_this = N("FunctionNodeCompare", "this cue previewed", data_type='INT', operation='EQUAL')
    L(gi, "Preview", is_this, "A_INT")
    L(gi, "Number", is_this, "B_INT")
    oi = N("GeometryNodeObjectInfo", "Cue object", transform_space='RELATIVE')
    L(gi, "Cue", oi, "Object")
    stand = sample("stand", oi, "Geometry", 'FLOAT_VECTOR', pos, "Position", (idx, "Index"))
    lookk = sample("look", oi, "Geometry", 'FLOAT_VECTOR', pos, "Position", (nxt, "Value"))
    part = sample("part", oi, "Geometry", 'FLOAT', attr("part"), AF, (idx, "Index"))
    onset = sample("onset", oi, "Geometry", 'FLOAT', attr("onset"), AF, (idx, "Index"))
    back = sample("back", oi, "Geometry", 'FLOAT', attr("back"), AF, (idx, "Index"))
    wv, sv = (gi, "Width"), (gi, "Snap")
    omw = math_('SUBTRACT', "1-W", None, wv, i0=1.0)
    # rise: a = clamp((R - onset*(1-W)) / W); eased with a quick start and a soft settle: 1 - (1-a)^snap
    o1 = math_('MULTIPLY', "onset*(1-W)", (onset, "Value"), (omw, "Value"))
    a0 = math_('SUBTRACT', "R - onset", (gi, "Play"), (o1, "Value"))
    a1 = math_('DIVIDE', "/W", (a0, "Value"), wv, clamp=True)
    inv = math_('SUBTRACT', "1-a", None, (a1, "Value"), i0=1.0)
    pw = math_('POWER', "(1-a)^snap", (inv, "Value"), sv)
    a = math_('SUBTRACT', "ease", None, (pw, "Value"), i0=1.0)
    # the head turns first: facing completes in 60 % of the member's window
    w06 = math_('MULTIPLY', "0.6W", wv, i1=0.6)
    af0 = math_('DIVIDE', "face /0.6W", (a0, "Value"), (w06, "Value"), clamp=True)
    af = smooth("face ease", (af0, "Value"), 0.0, 1.0)
    # return: b = smoothstep((B - back*(1-W)) / W)
    b1 = math_('MULTIPLY', "back*(1-W)", (back, "Value"), (omw, "Value"))
    b0 = math_('SUBTRACT', "B - back", (gi, "Back"), (b1, "Value"))
    b2 = math_('DIVIDE', "b/W", (b0, "Value"), wv, clamp=True)
    b = smooth("back ease", (b2, "Value"), 0.0, 1.0, 1.0, 0.0)          # 1 - smoothstep
    w_s = math_('MULTIPLY', "weight (sliders)", (math_('MULTIPLY', "a*(1-b)", (a, "Value"), (b, "Result")), "Value"), (part, "Value"))
    wf_s = math_('MULTIPLY', "face weight (sliders)", (math_('MULTIPLY', "af*(1-b)", (af, "Result"), (b, "Result")), "Value"), (part, "Value"))
    w = math_('MULTIPLY_ADD', "weight", (w_s, "Value"), (not_prev, "Value"), (is_this, "Result"))
    wf = math_('MULTIPLY_ADD', "face weight", (wf_s, "Value"), (not_prev, "Value"), (is_this, "Result"))
    d_xy, _d = xy(vop('SUBTRACT', "stand - rest", stand, "Value", pos, "Position"), "Vector", "move")
    mv = vop('SCALE', "move*w", d_xy, "Vector", scale=(w, "Value"))
    # facing: the signed angle from the rest facing to the cue's facing, so a turn SWEEPS (adding the vectors, as
    # crowd_choreo.py did, snaps through zero on a turn right round). A turn of exactly 180 degrees has no side of
    # its own: the hair added to the cross product sends it to the left, the same way every time (choreo_state too).
    lk = vop('SUBTRACT', "look - stand", lookk, "Value", stand, "Value")
    lks = N("ShaderNodeSeparateXYZ", "facing sep")
    L(lk, "Vector", lks, "Vector")
    cross = math_('SUBTRACT', "cross", (math_('MULTIPLY', "f0x*fy", (f0s, "X"), (lks, "Y")), "Value"),
                  (math_('MULTIPLY', "f0y*fx", (f0s, "Y"), (lks, "X")), "Value"))
    dot = math_('MULTIPLY_ADD', "dot", (f0s, "Y"), (lks, "Y"), (math_('MULTIPLY', "f0x*fx", (f0s, "X"), (lks, "X")), "Value"))
    cross_b = math_('MULTIPLY_ADD', "cross + hair", (math_('MINIMUM', "dot when facing back", (dot, "Value"), i1=0.0), "Value"),
                    None, (cross, "Value"), i1=-CH_TURN_BIAS)        # nothing is added to a turn of less than 90 degrees
    ang = math_('ARCTAN2', "turn", (cross_b, "Value"), (dot, "Value"))
    yw = math_('MULTIPLY', "turn*w", (ang, "Value"), (wf, "Value"))
    md = math_('MULTIPLY', "mood*w", (lks, "Z"), (w, "Value"))
    L(vop('ADD', "move so far + move", gi, "Move so far", mv, "Vector"), "Vector", go, "Move")
    L(math_('ADD', "turn so far + turn", (gi, "Turn so far"), (yw, "Value")), "Value", go, "Turn")
    L(math_('ADD', "mood so far + mood", (gi, "Mood so far"), (md, "Value")), "Value", go, "Mood")
    nb.tidy(12)
    return ng


def _build_members_group(ng):
    """From the crowd mesh and what the cues add up to: everybody moved, turned and drawn as a peg."""
    I = ng.interface
    _helper_socket(I, "Geometry", 'NodeSocketGeometry')
    _helper_socket(I, "Move", 'NodeSocketVector', desc="The sum of the cues' moves")
    _helper_socket(I, "Turn", 'NodeSocketFloat', desc="The sum of the cues' turns (radians)")
    _helper_socket(I, "Mood", 'NodeSocketFloat', desc="The sum of the cues' moods")
    for name, kind, default, mn, mx, desc, _panel in CH_INPUTS:
        if name != "Preview":
            _helper_socket(I, name, kind, default=default, mn=mn, mx=mx, desc=desc)
    _helper_socket(I, "Geometry", 'NodeSocketGeometry', in_out='OUTPUT')
    nb = _NB(ng)
    N, L, math_, vop, xy, smooth, attr = nb.N, nb.L, nb.math, nb.vop, nb.xy, nb.smooth, nb.attr
    nodes, links = ng.nodes, ng.links
    AK = nb.AK
    AV, AF = AK['FLOAT_VECTOR'], AK['FLOAT']
    nodes.clear()
    gi = N("NodeGroupInput", "In")
    go = N("NodeGroupOutput", "Out")
    f0, f0s = nb.rest_facing(gi, "Geometry")
    idx, pos = nb.idx, nb.pos
    # heading = the rest facing turned by the sum of weight x angle (cues stack: see choreo_state)
    sn = math_('SINE', "sin yaw", (gi, "Turn"))
    cs = math_('COSINE', "cos yaw", (gi, "Turn"))
    hx = math_('SUBTRACT', "hx", (math_('MULTIPLY', "f0x*cos", (f0s, "X"), (cs, "Value")), "Value"),
               (math_('MULTIPLY', "f0y*sin", (f0s, "Y"), (sn, "Value")), "Value"))
    hy = math_('MULTIPLY_ADD', "hy", (f0s, "X"), (sn, "Value"), (math_('MULTIPLY', "f0y*cos", (f0s, "Y"), (cs, "Value")), "Value"))
    hdg_v = N("ShaderNodeCombineXYZ", "facing")
    L(hx, "Value", hdg_v, "X")
    L(hy, "Value", hdg_v, "Y")
    hdg_v.inputs["Z"].default_value = 0.0
    s1 = N("GeometryNodeStoreNamedAttribute", "store hdg", data_type='FLOAT_VECTOR', domain='POINT')
    L(gi, "Geometry", s1, "Geometry")
    s1.inputs["Name"].default_value = "hdg"
    L(hdg_v, "Vector", s1, "Value")
    s2 = N("GeometryNodeStoreNamedAttribute", "store mood", data_type='FLOAT', domain='POINT')
    L(s1, "Geometry", s2, "Geometry")
    s2.inputs["Name"].default_value = "mood"
    L(gi, "Mood", s2, "Value")
    cued = N("GeometryNodeSetPosition", "Play the cues")
    L(s2, "Geometry", cued, "Geometry")
    L(gi, "Move", cued, "Offset")
    odd = math_('FLOORED_MODULO', "index mod 2", (idx, "Index"), i1=2.0)
    is_look = N("FunctionNodeCompare", "is a look point", data_type='FLOAT', operation='GREATER_THAN')
    L(odd, "Value", is_look, "A")
    is_look.inputs["B"].default_value = 0.5
    members = N("GeometryNodeDeleteGeometry", "members only", domain='POINT')
    L(cued, "Geometry", members, "Geometry")
    L(is_look, "Result", members, "Selection")
    pts = N("GeometryNodeMeshToPoints", "to points", mode='VERTICES')
    L(members, "Geometry", pts, "Mesh")
    # everybody carries their own number onto what is drawn, so a check can follow one person through the film
    who = N("GeometryNodeStoreNamedAttribute", "store member", data_type='INT', domain='POINT')
    L(pts, "Points", who, "Geometry")
    who.inputs["Name"].default_value = "member"
    L(idx, "Index", who, "Value")

    # ================================================================ per-member constants (stable: from the index)
    def rnd(nm, lo, hi, seed_off):
        r = N("FunctionNodeRandomValue", nm, data_type='FLOAT')
        _sock(r, "Min").default_value = lo
        _sock(r, "Max").default_value = hi
        L(idx, "Index", r, "ID")
        s = math_('ADD', f"seed+{seed_off}", (gi, "Seed"), i1=float(seed_off))
        L(s, "Value", r, "Seed")
        return r

    r_h = rnd("Random height", -1.0, 1.0, 3)
    r_side = math_('SIGN', "side", (rnd("Random side", -1.0, 1.0, 4), "Value"))
    r_phase = rnd("Random phase", 0.0, 1.0, 7)
    r_rate = rnd("Random rate", 0.85, 1.2, 8)
    r_amp = rnd("Random bounce", 0.55, 1.0, 9)
    time = N("GeometryNodeInputSceneTime", "Time")
    hdg = attr("hdg", 'FLOAT_VECTOR')
    mood = attr("mood")

    # ================================================================ idle: a slow wander of the head, nothing else
    t_speed = math_('MULTIPLY', "t*speed", (time, "Seconds"), (gi, "Idle speed"))
    noise = N("ShaderNodeTexNoise", "Idle noise", noise_dimensions='4D')
    noise.inputs["Scale"].default_value = 1.0
    noise.inputs["Detail"].default_value = 0.0
    n_in = N("ShaderNodeVectorMath", "P*0.2", operation='SCALE')
    L(pos, "Position", n_in, 0)
    n_in.inputs["Scale"].default_value = 0.2
    L(n_in, "Vector", noise, "Vector")
    L(t_speed, "Value", noise, "W")
    n_sep = N("ShaderNodeSeparateXYZ", "noise sep")
    L(noise, "Color", n_sep, "Vector")
    turn_rad = math_('RADIANS', "idle turn rad", (gi, "Idle turn"))
    yc = math_('SUBTRACT', "yaw noise -0.5", (n_sep, "Z"), i1=0.5)
    idle_yaw = math_('MULTIPLY', "idle yaw", (math_('MULTIPLY', "yaw x2", (yc, "Value"), i1=2.0), "Value"), (turn_rad, "Value"))

    # ================================================================ mood: excited members bounce, frightened ones duck
    up = math_('MAXIMUM', "mood up", (mood, AF), i1=0.0)
    down = math_('MAXIMUM', "mood down >= -1", (math_('MINIMUM', "mood down", (mood, AF), i1=0.0), "Value"), i1=-1.0)
    ph = math_('ADD', "t*rate + phase", (math_('MULTIPLY', "t*rate", (time, "Seconds"),
                                              (math_('MULTIPLY', "rate*var", (gi, "Bob rate"), (r_rate, "Value")), "Value")), "Value"),
               (r_phase, "Value"))
    wave = math_('SINE', "sin", (math_('MULTIPLY', "2pi", (ph, "Value"), i1=2.0 * math.pi), "Value"))
    hop = math_('MAXIMUM', "hop >= 0", (wave, "Value"), i1=0.0)
    bob = math_('MULTIPLY', "*height", (math_('MULTIPLY', "*amp", (math_('MULTIPLY', "hop*mood", (hop, "Value"), (up, "Value")), "Value"),
                                              (r_amp, "Value")), "Value"), (gi, "Bob height"))
    lift = N("ShaderNodeCombineXYZ", "bob")
    L(bob, "Value", lift, "Z")
    duck = math_('MULTIPLY_ADD', "1 + 0.32*down", (down, "Value"), i1=0.32, i2=1.0)
    moved = N("GeometryNodeSetPosition", "Mood")
    L(who, "Geometry", moved, "Geometry")
    L(lift, "Vector", moved, "Offset")

    # ================================================================ lens clearance (drawn only), as in the simulated crowd
    cam = N("GeometryNodeInputActiveCamera", "Active camera")
    oi_cam = N("GeometryNodeObjectInfo", "Camera info", transform_space='RELATIVE')
    L(cam, 0, oi_cam, "Object")
    lookv = N("FunctionNodeRotateVector", "camera forward")
    lookv.inputs["Vector"].default_value = (0.0, 0.0, -1.0)
    L(oi_cam, "Rotation", lookv, "Rotation")
    fwd_raw, _s = xy(lookv, "Vector", "fwd raw")
    fwd_len = vop('LENGTH', "|fwd xy|", fwd_raw, "Vector")
    fwd = vop('NORMALIZE', "fwd", fwd_raw, "Vector")
    level = smooth("camera not top-down", (fwd_len, "Value"), 0.15, 0.35)
    cam_sep = N("ShaderNodeSeparateXYZ", "camera pos sep")
    L(oi_cam, "Location", cam_sep, "Vector")
    low = smooth("camera in the crowd", (cam_sep, "Z"), 2.6, 3.6, 1.0, 0.0)
    d_c, _s = xy(vop('SUBTRACT', "P - camera", pos, "Position", oi_cam, "Location"), "Vector", "d_c")
    along_c = vop('DOT_PRODUCT', "along lens", d_c, "Vector", fwd, "Vector")
    lat_vec = vop('SUBTRACT', "lateral vec", d_c, "Vector", vop('SCALE', "along*fwd", fwd, "Vector", scale=(along_c, "Value")), "Vector")
    lat_c = vop('LENGTH', "|lateral|", lat_vec, "Vector")
    # The zone right in front of the lens: as wide as the clearance at the lens, narrowing to nothing at the reach.
    # People in it are NOT DRAWN. (Until build 1 they were pushed to its edge instead: they piled up there one
    # inside the other, and slid sideways whenever the camera moved.)
    reach_ok = math_('MAXIMUM', "reach >= 0.1", (gi, "Lens reach"), i1=0.1)
    ratio = math_('DIVIDE', "along / reach", (along_c, "Value"), (reach_ok, "Value"))
    taper = math_('MINIMUM', "taper <= 1", (math_('MULTIPLY_ADD', "1 - along/reach", (ratio, "Value"), i1=-1.0, i2=1.0), "Value"), i1=1.0)
    half = math_('MULTIPLY', "half width here", (math_('MAXIMUM', "taper >= 0", (taper, "Value"), i1=0.0), "Value"), (gi, "Lens clearance"))
    gap_c = math_('SUBTRACT', "half - |lat|", (half, "Value"), (lat_c, "Value"))
    gap_cc = math_('MAXIMUM', "gap >= 0 (lens)", (gap_c, "Value"), i1=0.0)
    near_w = smooth("starts just behind the lens", (along_c, "Value"), -0.45, -0.25)
    w2 = math_('MULTIPLY', "*level", (near_w, "Result"), (level, "Result"))
    w3 = math_('MULTIPLY', "*low", (w2, "Value"), (low, "Result"))
    lens_in = math_('MULTIPLY', "inside the lens zone", (gap_cc, "Value"), (w3, "Value"))
    in_zone = N("FunctionNodeCompare", "in front of the lens", data_type='FLOAT', operation='GREATER_THAN')
    L(lens_in, "Value", in_zone, "A")
    in_zone.inputs["B"].default_value = 0.004
    lens_set = N("GeometryNodeDeleteGeometry", "Leave out in front of the lens", domain='POINT')
    L(moved, "Geometry", lens_set, "Geometry")
    L(in_zone, "Result", lens_set, "Selection")

    # ================================================================ keep off the characters (drawn only)
    inf_d = N("GeometryNodeObjectInfo", "Influencers info", transform_space='RELATIVE')
    L(gi, "Influencers", inf_d, "Object")
    kind_d = attr("kind", 'INT')
    is_pos_d = N("FunctionNodeCompare", "kind == 0", data_type='INT', operation='EQUAL')
    L(kind_d, AK['INT'], is_pos_d, "A_INT")
    _sock(is_pos_d, "B_INT").default_value = 0
    spots = N("GeometryNodeSeparateGeometry", "Influencer spots", domain='POINT')
    L(inf_d, "Geometry", spots, "Geometry")
    L(is_pos_d, "Result", spots, "Selection")
    prox = N("GeometryNodeProximity", "Nearest character", target_element='POINTS')
    links.new(spots.outputs[0], prox.inputs[0])
    d_ch, _s = xy(vop('SUBTRACT', "P - character", pos, "Position", prox, "Position"), "Vector", "d_ch")
    ch_gap = math_('SUBTRACT', "keep off - distance", (gi, "Keep off"), (prox, "Distance"))
    ch_gap_c = math_('MAXIMUM', "gap >= 0 (character)", (ch_gap, "Value"), i1=0.0)
    ch_valid = N("GeometryNodeSwitch", "any character?", input_type='FLOAT')
    L(prox, "Is Valid", ch_valid, "Switch")
    L(ch_gap_c, "Value", ch_valid, "True")
    ch_off = vop('SCALE', "off the character", vop('NORMALIZE', "away from the character", d_ch, "Vector"), "Vector", scale=(ch_valid, "Output"))
    keep_off = N("GeometryNodeSetPosition", "Keep off the characters")
    L(lens_set, "Geometry", keep_off, "Geometry")
    L(ch_off, "Vector", keep_off, "Offset")

    # ================================================================ the peg: BB Stage's character, part for part
    H = 1.75
    r_body, body_h, head_r = 0.13, H * 0.80, H * 0.075
    body = N("GeometryNodeMeshCone", "Body", fill_type='NGON')
    body.inputs["Vertices"].default_value = 16
    body.inputs["Radius Top"].default_value = r_body * 0.85
    body.inputs["Radius Bottom"].default_value = r_body
    body.inputs["Depth"].default_value = body_h
    head = N("GeometryNodeMeshUVSphere", "Head")
    head.inputs["Segments"].default_value = 12
    head.inputs["Rings"].default_value = 8
    head.inputs["Radius"].default_value = head_r
    head_t = N("GeometryNodeTransform", "Head up")
    head_t.inputs["Translation"].default_value = (0.0, 0.0, body_h + head_r * 1.1)
    L(head, "Mesh", head_t, "Geometry")
    nose = N("GeometryNodeMeshCone", "Nose", fill_type='NGON')
    nose.inputs["Vertices"].default_value = 10
    nose.inputs["Radius Top"].default_value = 0.0
    nose.inputs["Radius Bottom"].default_value = head_r * 0.45
    nose.inputs["Depth"].default_value = head_r * 1.08
    nose_t = N("GeometryNodeTransform", "Nose fwd")
    # the node cone starts at its origin (base at 0, tip at +depth); BB Stage's nose base sits 0.81 head radii out
    nose_t.inputs["Translation"].default_value = (0.0, head_r * 0.81, body_h + head_r * 1.1)
    nose_t.inputs["Rotation"].default_value = (-math.pi / 2, math.pi / 10, 0.0)
    L(nose, "Mesh", nose_t, "Geometry")
    peg = N("GeometryNodeJoinGeometry", "Peg")
    links.new(body.outputs["Mesh"], peg.inputs[0])
    for n in (head_t, nose_t):
        links.new(n.outputs["Geometry"], peg.inputs[0])
    setmat = N("GeometryNodeSetMaterial", "Peg material")
    L(gi, "Peg material", setmat, "Material")
    L(peg, "Geometry", setmat, "Geometry")

    align = N("FunctionNodeAlignRotationToVector", "Face it", axis='Y', pivot_axis='Z')
    L(hdg, AV, align, "Vector")
    comb_yaw = N("ShaderNodeCombineXYZ", "yaw euler")
    L(idle_yaw, "Value", comb_yaw, "Z")
    yaw = N("FunctionNodeEulerToRotation", "yaw rotation")
    L(comb_yaw, "Vector", yaw, "Euler")
    rot = N("FunctionNodeRotateRotation", "Rotate", rotation_space='LOCAL')
    L(align, "Rotation", rot, "Rotation")
    L(yaw, "Rotation", rot, "Rotate By")
    h_var = math_('MULTIPLY_ADD', "1 + var*r", (r_h, "Value"), (gi, "Height variation"), i2=1.0)
    scale_h = math_('MULTIPLY', "height/1.75 * var", (math_('DIVIDE', "height/1.75", (gi, "Peg height"), i1=H), "Value"), (h_var, "Value"))
    scale_z = math_('MULTIPLY', "*duck", (scale_h, "Value"), (duck, "Value"))
    scale_v = N("ShaderNodeCombineXYZ", "scale xyz")
    L(scale_h, "Value", scale_v, "X")
    L(scale_h, "Value", scale_v, "Y")
    L(scale_z, "Value", scale_v, "Z")
    inst = N("GeometryNodeInstanceOnPoints", "Members")
    L(keep_off, "Geometry", inst, "Points")
    L(setmat, "Geometry", inst, "Instance")
    L(rot, "Rotation", inst, "Rotation")
    L(scale_v, "Vector", inst, "Scale")
    L(inst, "Instances", go, "Geometry")
    nb.tidy(20)
    return ng


def _choreo_helper(which):
    """The two node groups all choreographed crowds share, built once per file: 'cue' works out what ONE cue adds
    for every member, 'members' draws everybody. A crowd's own tree is then one small node per cue, so adding a
    cue stays quick however many there are (Blender rebuilds a tree in time that grows with its square)."""
    name = CH_HELPERS[which]
    tag = f"{which}:{CH_BUILD}"
    ng = bpy.data.node_groups.get(name)
    if ng is not None and (ng.get(CH_SIG) != tag or not len(ng.nodes)):
        ng.name = name + " (old)"
        ng = None
    if ng is None:
        ng = bpy.data.node_groups.new(name, "GeometryNodeTree")
        (_build_cue_group if which == "cue" else _build_members_group)(ng)
        ng[CH_SIG] = tag
    return ng


def _choreo_build_nodes(crowd, ng):
    """(Re)build the crowd's own nodes for its cue list: a chain of one node per cue, then the members. The
    interface is not touched here, so the sliders keep their identifiers, values and keys."""
    cue_g, mem_g = _choreo_helper("cue"), _choreo_helper("members")
    nodes, links = ng.nodes, ng.links
    nodes.clear()
    gi = nodes.new("NodeGroupInput")
    gi.name = gi.label = "In"
    go = nodes.new("NodeGroupOutput")
    go.name = go.label = "Out"
    cue_ids = {i for c in crowd.bb_crowd_cues for i in (c.sock, c.sock_back)}
    by_name = {it.name: it.identifier for it in ng.interface.items_tree
               if it.item_type == 'SOCKET' and it.in_out == 'INPUT' and it.identifier not in cue_ids}

    def out_of(identifier):
        return next(s for s in gi.outputs if s.identifier == identifier)

    geo = next(s for s in gi.outputs if s.type == 'GEOMETRY')
    fin = nodes.new("GeometryNodeGroup")
    fin.node_tree = mem_g
    fin.name = fin.label = "Members"
    links.new(geo, fin.inputs["Geometry"])
    for name, _kind, _default, _mn, _mx, _desc, _panel in CH_INPUTS:
        if name != "Preview":
            links.new(out_of(by_name[name]), fin.inputs[name])
    prev = None
    for cue in crowd.bb_crowd_cues:
        if not _cue_ok(cue):
            continue
        n = nodes.new("GeometryNodeGroup")
        n.node_tree = cue_g
        n.name = f"cue {cue.uid}"
        n.label = cue.name
        n.inputs["Cue"].default_value = cue.obj
        n.inputs["Width"].default_value = cue.width        # Wave <-> Together and Snap: set live by the panel
        n.inputs["Snap"].default_value = cue.snap
        n.inputs["Number"].default_value = cue.uid
        links.new(geo, n.inputs["Crowd"])
        links.new(out_of(cue.sock), n.inputs["Play"])
        links.new(out_of(cue.sock_back), n.inputs["Back"])
        links.new(out_of(by_name["Preview"]), n.inputs["Preview"])
        if prev is not None:
            for a, b in (("Move", "Move so far"), ("Turn", "Turn so far"), ("Mood", "Mood so far")):
                links.new(prev.outputs[a], n.inputs[b])
        prev = n
    if prev is not None:
        for a in ("Move", "Turn", "Mood"):
            links.new(prev.outputs[a], fin.inputs[a])
    links.new(fin.outputs["Geometry"], next(s for s in go.inputs if s.type == 'GEOMETRY'))
    for i, n in enumerate(nodes):
        n.location = ((i % 8) * 260, -(i // 8) * 420)
    return ng


# ------------------------------------------------------------------ choreographed crowds: making, cues, timing
def _peg_material(name, color=CH_GREY):
    mat = bpy.data.materials.get(name)
    if mat is None:
        mat = bpy.data.materials.new(name)
        mat.diffuse_color = color
        mat.use_nodes = True
        bsdf = next((n for n in mat.node_tree.nodes if n.type == 'BSDF_PRINCIPLED'), None)
        if bsdf is not None:
            bsdf.inputs["Base Color"].default_value = color
    return mat


def choreo_make(scene, name, homes, look_at=None, collection=None, world=None, material=None, facings=None):
    """A choreographed crowd. homes: [(x, y)] or [(x, y, z)] where each member stands, in the crowd's own space;
    look_at: the (x, y) everybody watches at rest (None: they face +Y); facings: [(fx, fy)] per member instead of
    look_at; collection: where the object goes (default: the scene's crowd collection); world: the object's
    matrix (default: identity). Returns the crowd object, with its modifier in place and no cues yet."""
    verts, edges = [], []
    for i, h in enumerate(homes):
        x, y = float(h[0]), float(h[1])
        z = float(h[2]) if len(h) > 2 else 0.0
        if facings is not None:
            fx, fy = float(facings[i][0]), float(facings[i][1])
        elif look_at is not None:
            fx, fy = float(look_at[0]) - x, float(look_at[1]) - y
        else:
            fx, fy = 0.0, 1.0
        fl = math.hypot(fx, fy)
        fx, fy = (fx / fl, fy / fl) if fl > 1e-6 else (0.0, 1.0)
        verts += [(x, y, z), (x + fx, y + fy, z)]
        edges.append((2 * i, 2 * i + 1))
    me = bpy.data.meshes.new(name)
    me.from_pydata(verts, edges, [])
    me.update()
    ob = bpy.data.objects.new(name, me)
    ob.matrix_world = world.copy() if world is not None else Matrix.Identity(4)
    ob[CH_TAG] = True
    (collection if collection is not None else crowd_coll(scene)).objects.link(ob)
    if material is None:
        material = _peg_material(f"BB Crowd peg · {ob.name}")
    choreo_sync(ob)
    ch_sock(ob, "Peg material").value = material
    sync_mirror(scene)                      # the characters to keep off: every crowd of the scene gets the mirror
    inf = ch_sock(ob, "Influencers")
    if inf.value is None:
        inf.value = mirror_of(scene, create=False)
    picked = getattr(scene, "bb_crowd_choreo", None)        # the panel works on the first crowd made, until another is picked
    if hasattr(scene, "bb_crowd_choreo") and (picked is None or scene.objects.get(picked.name) != picked):
        scene.bb_crowd_choreo = ob
    _FIRST_CROWD["at"] = 0.0
    ob.update_tag()
    return ob


def _cue_mesh(crowd, name, members):
    """The mesh of a cue: the crowd's pairs, with the members of the cue moved, turned and given their mood."""
    n = choreo_members(crowd)
    co = [0.0] * (6 * n)
    crowd.data.vertices.foreach_get("co", co)
    verts, edges = [], []
    part, onset, back = [0.0] * (2 * n), [0.0] * (2 * n), [0.0] * (2 * n)
    for i in range(n):
        px, py, pz = co[6 * i], co[6 * i + 1], co[6 * i + 2]
        fx, fy = co[6 * i + 3] - px, co[6 * i + 4] - py
        fl = math.hypot(fx, fy)
        fx, fy = (fx / fl, fy / fl) if fl > 1e-6 else (0.0, 1.0)
        spec = members.get(i)
        qx, qy, mood = px, py, 0.0
        if spec is not None:
            mv = spec.get("move") or (0.0, 0.0)
            qx, qy = px + float(mv[0]), py + float(mv[1])
            face = spec.get("face")
            if face is not None:
                gl = math.hypot(face[0], face[1])
                if gl > 1e-6:
                    fx, fy = face[0] / gl, face[1] / gl
            mood = float(spec.get("mood", 0.0) or 0.0)
            part[2 * i] = 1.0
            onset[2 * i] = min(1.0, max(0.0, float(spec.get("onset", 0.0))))
            back[2 * i] = min(1.0, max(0.0, float(spec.get("back", spec.get("onset", 0.0)))))
        verts += [(qx, qy, pz), (qx + fx, qy + fy, pz + mood)]
        edges.append((2 * i, 2 * i + 1))
    me = bpy.data.meshes.new(name)
    me.from_pydata(verts, edges, [])
    for an, vals in (("part", part), ("onset", onset), ("back", back)):
        a = me.attributes.new(an, 'FLOAT', 'POINT')
        a.data.foreach_set("value", vals)
    me.update()
    return me


def _cue_write(crowd, cue, members):
    """Replace what a cue holds (Update From Source). The cue object stays, so nothing else changes."""
    ob = cue.obj
    old = ob.data
    ob.data = _cue_mesh(crowd, ob.name, members)
    if old is not None and old.users == 0:
        bpy.data.meshes.remove(old)
    ob.update_tag()
    crowd.update_tag()


def choreo_add_cue(crowd, name, members, width=0.4, snap=2.0, kind='HAND', **params):
    """Add a cue. members: {i: dict(move=(dx, dy), face=(fx, fy) or None, mood=0.0, onset=0..1, back=0..1)};
    everybody else is left out of the cue. Cues STACK: `move` is a step from the member's rest spot that is added
    on top of whatever the other cues do, and `face` is the rest facing turned by the angle this cue adds to
    theirs (None: it adds no turn). To plan a cue from where the crowd is while other cues are played, give the
    generator base=choreo_state(crowd). width: the share of the cue's rise one member's own move takes (small =
    a crisp wave through the crowd, 1 = all together). snap: 1 = even, 2 = quick start and soft settle, 3 = a
    startle. kind and params (radius=…, source=…, frame=…) are remembered on the cue for Update From Source.
    Returns the cue (an item of crowd.bb_crowd_cues; fetch it again by name after adding or removing others)."""
    sync = params.pop("sync", True)
    cues = crowd.bb_crowd_cues
    name = _cue_clean_name(crowd, name)
    oname = f"{crowd.name} · cue · {name}"
    ob = bpy.data.objects.new(oname, _cue_mesh(crowd, oname, members or {}))
    ob[CUE_TAG] = name
    ob.parent = crowd                    # same space as the crowd: the vertices line up one to one
    ob.hide_render = True
    ob.hide_viewport = True              # shown only while Edit Positions is on
    ob.display_type = 'WIRE'
    for c in crowd.users_collection:
        c.objects.link(ob)
    uid = max((c.uid for c in cues), default=0) + 1
    _CH_QUIET["on"] = True
    try:
        it = cues.add()
        it.name, it.obj, it.uid, it.kind = name, ob, uid, kind
        it.width = min(1.0, max(0.02, float(width)))
        it.snap = min(5.0, max(1.0, float(snap)))
        known = it.bl_rna.properties
        for k, v in params.items():
            if k in known:
                setattr(it, k, v)
            else:
                it[k] = v
    finally:
        _CH_QUIET["on"] = False
    crowd.bb_crowd_cue_index = len(cues) - 1
    if sync:
        choreo_sync(crowd)
    return cues[len(cues) - 1]


def choreo_remove_cue(crowd, name):
    """Remove a cue: its object, its two sliders and their keys. The other cues play exactly as before."""
    cues = crowd.bb_crowd_cues
    for i, c in enumerate(cues):
        if c.name != name:
            continue
        ob = c.obj
        prev = ch_sock(crowd, "Preview")
        if prev is not None and c.uid and int(prev.value) == c.uid:
            prev.value = 0
        cues.remove(i)
        if ob is not None:
            _remove_object(ob)
        crowd.bb_crowd_cue_index = max(0, min(crowd.bb_crowd_cue_index, len(cues) - 1))
        choreo_sync(crowd)
        return True
    return False


def choreo_rename_cue(crowd, old, new):
    """Rename a cue: its object and its two sliders follow, the keys stay. Returns the name it got."""
    c = choreo_cue(crowd, old)
    if c is None:
        raise KeyError(f"{crowd.name} has no cue called '{old}'")
    c.name = new                          # the property's update does the rest (choreo_sync)
    return c.name


def choreo_key(crowd, name, rise=(), back=(), ease=0.33):
    """rise / back: [(frame, value 0..1)] for the cue's Play and Back sliders. Straight ramps with soft shoulders
    (ease = 0: plain straight lines): the members' own easing is inside the node tree, the ramp only says how
    fast the reaction travels."""
    cue = choreo_cue(crowd, name)
    if cue is None:
        raise KeyError(f"{crowd.name} has no cue called '{name}'")
    play, bk = cue_sliders(crowd, cue)
    if play is None or bk is None:
        choreo_sync(crowd)
        play, bk = cue_sliders(crowd, cue)
    for s, keys in ((play, rise), (bk, back)):
        for f, v in keys or ():
            s.value = float(v)
            s.keyframe_insert("value", frame=f)
    for _cb, fc in _ch_fcurves(crowd, (cue.sock, cue.sock_back)):
        kps = sorted(fc.keyframe_points, key=lambda k: k.co.x)
        for j, kp in enumerate(kps):
            if ease <= 0.0:
                kp.interpolation = 'LINEAR'
                continue
            kp.interpolation = 'BEZIER'
            kp.handle_left_type = kp.handle_right_type = 'FREE'
            left = (kp.co.x - kps[j - 1].co.x) if j else 10.0
            right = (kps[j + 1].co.x - kp.co.x) if j + 1 < len(kps) else 10.0
            kp.handle_left = (kp.co.x - left * ease, kp.co.y)
            kp.handle_right = (kp.co.x + right * ease, kp.co.y)
        fc.update()
    _cue_show_frame(crowd, cue)
    return cue


def _cue_show_frame(crowd, cue):
    """After keys changed: the two sliders show their keyed value on the current frame."""
    frame = _scene_of(crowd).frame_current
    play, bk = cue_sliders(crowd, cue)
    for s, ident in ((play, cue.sock), (bk, cue.sock_back)):
        for _cb, fc in _ch_fcurves(crowd, (ident,)):
            s.value = fc.evaluate(frame)
    crowd.update_tag()


def choreo_clear_keys(crowd, name, which=('PLAY', 'BACK')):
    """Remove the timing of a cue: the keys of its Play and Back sliders go and both rest at 0."""
    cue = choreo_cue(crowd, name)
    if cue is None:
        raise KeyError(f"{crowd.name} has no cue called '{name}'")
    play, bk = cue_sliders(crowd, cue)
    for tag, s, ident in (('PLAY', play, cue.sock), ('BACK', bk, cue.sock_back)):
        if tag not in which:
            continue
        for cb, fc in _ch_fcurves(crowd, (ident,)):
            cb.fcurves.remove(fc)
        if s is not None:
            s.value = 0.0
    crowd.update_tag()
    return cue


def choreo_weights(crowd, frame=None):
    """{cue name: (play, back)}: what the sliders are on a frame (default: the current one). Keyed sliders are
    read from their F-curves, the others from the value they hold."""
    if frame is None:
        frame = _scene_of(crowd).frame_current
    out = {}
    for c in crowd.bb_crowd_cues:
        vals = []
        for s, ident in zip(cue_sliders(crowd, c), (c.sock, c.sock_back)):
            v = float(s.value) if s is not None else 0.0
            for _cb, fc in _ch_fcurves(crowd, (ident,)):
                v = fc.evaluate(frame)
            vals.append(min(1.0, max(0.0, v)))
        out[c.name] = (vals[0], vals[1])
    return out


def choreo_state(crowd, weights=None, frame=None):
    """(positions, facings): where every member stands and which way it faces, in the crowd's own space, with
    the cues played as far as `weights` = {cue name: (play, back)} says (None: the sliders on `frame`, default
    the current frame; a cue left out counts as not played). Pure Python with the maths of the node tree: each
    member's own window from its onset, the 1-(1-a)^snap ease, the facing done in 60 % of the window, the return
    in the order of `back`; the moves of the cues add up and so do their turns. The two drawn-only steps aside
    (the lens, the characters) are not in it. This is what a generator takes as `base` to plan a cue from where
    the crowd is at that moment."""
    if weights is None:
        weights = choreo_weights(crowd, frame)
    n = choreo_members(crowd)
    co = [0.0] * (6 * n)
    crowd.data.vertices.foreach_get("co", co)
    f0 = []
    for i in range(n):
        fx, fy = co[6 * i + 3] - co[6 * i], co[6 * i + 4] - co[6 * i + 1]
        fl = math.hypot(fx, fy)
        f0.append((fx / fl, fy / fl) if fl > 1e-9 else (0.0, 0.0))
    dx, dy, yaw = [0.0] * n, [0.0] * n, [0.0] * n
    for c in crowd.bb_crowd_cues:
        play, back = weights.get(c.name, (0.0, 0.0))
        me = c.obj.data if (c.obj is not None and c.obj.type == 'MESH') else None
        if me is None or len(me.vertices) != 2 * n or play <= 0.0 or any(a not in me.attributes for a in ("part", "onset", "back")):
            continue
        wd, snap = c.width, c.snap
        cc = [0.0] * (6 * n)
        me.vertices.foreach_get("co", cc)
        part, onset, bk = [0.0] * (2 * n), [0.0] * (2 * n), [0.0] * (2 * n)
        me.attributes["part"].data.foreach_get("value", part)
        me.attributes["onset"].data.foreach_get("value", onset)
        me.attributes["back"].data.foreach_get("value", bk)
        for i in range(n):
            pt = part[2 * i]
            if pt == 0.0:
                continue
            t = min(1.0, max(0.0, (back - bk[2 * i] * (1.0 - wd)) / wd))
            b = (1.0 - t * t * (3.0 - 2.0 * t)) * pt
            if b == 0.0:
                continue
            a0 = play - onset[2 * i] * (1.0 - wd)
            a = min(1.0, max(0.0, a0 / wd))
            w = (1.0 - (1.0 - a) ** snap) * b
            t = min(1.0, max(0.0, a0 / (0.6 * wd)))
            wf = t * t * (3.0 - 2.0 * t) * b
            k = 6 * i
            if w:
                dx[i] += (cc[k] - co[k]) * w
                dy[i] += (cc[k + 1] - co[k + 1]) * w
            if wf:
                lx, ly = cc[k + 3] - cc[k], cc[k + 4] - cc[k + 1]
                dot = f0[i][0] * lx + f0[i][1] * ly
                yaw[i] += math.atan2(f0[i][0] * ly - f0[i][1] * lx - CH_TURN_BIAS * min(dot, 0.0), dot) * wf
    positions = [Vector((co[6 * i] + dx[i], co[6 * i + 1] + dy[i], co[6 * i + 2])) for i in range(n)]
    facings = []
    for i in range(n):
        fx, fy = f0[i] if f0[i] != (0.0, 0.0) else (0.0, 1.0)
        cs, sn = math.cos(yaw[i]), math.sin(yaw[i])
        facings.append(Vector((fx * cs - fy * sn, fx * sn + fy * cs, 0.0)))
    return positions, facings


def choreo_set_look(crowd, look_at):
    """Change what everybody watches at rest: look_at is an (x, y) in the crowd's own space. Every cue keeps the
    turn it adds (its facing is turned along with the rest facing), so nothing else changes; a Look at cue then
    wants Update From Source."""
    n = choreo_members(crowd)
    co = [0.0] * (6 * n)
    crowd.data.vertices.foreach_get("co", co)
    turn = []
    for i in range(n):
        k = 6 * i
        ox, oy = co[k + 3] - co[k], co[k + 4] - co[k + 1]
        nx, ny = float(look_at[0]) - co[k], float(look_at[1]) - co[k + 1]
        nl = math.hypot(nx, ny)
        if nl < 1e-6 or math.hypot(ox, oy) < 1e-6:
            turn.append((1.0, 0.0))
            continue
        a = math.atan2(ox * ny - oy * nx, ox * nx + oy * ny)
        turn.append((math.cos(a), math.sin(a)))
        co[k + 3], co[k + 4] = co[k] + nx / nl, co[k + 1] + ny / nl
    crowd.data.vertices.foreach_set("co", co)
    crowd.data.update()
    for c in crowd.bb_crowd_cues:
        me = c.obj.data if (c.obj is not None and c.obj.type == 'MESH') else None
        if me is None or len(me.vertices) != 2 * n:
            continue
        cc = [0.0] * (6 * n)
        me.vertices.foreach_get("co", cc)
        for i in range(n):
            k = 6 * i
            cs, sn = turn[i]
            fx, fy = cc[k + 3] - cc[k], cc[k + 4] - cc[k + 1]
            cc[k + 3], cc[k + 4] = cc[k] + fx * cs - fy * sn, cc[k + 1] + fx * sn + fy * cs
        me.vertices.foreach_set("co", cc)
        me.update()
        c.obj.update_tag()
    crowd.update_tag()


# ------------------------------------------------------------------ choreographed crowds: generators (pure functions)
# Every generator returns {member: dict(move, face, mood, onset, back)} for choreo_add_cue and touches nothing.
# With base=None it plans from the rest spots. With base=choreo_state(crowd) it plans from where everybody stands
# and faces at that moment (who is in reach, the distances, the spacing): `move` is then the step from THERE, and
# `face` is the rest facing turned by the angle still missing, so that added to what the cues already played do,
# the member ends on the intended spot and facing.
def _homes(crowd):
    """Rest spots [(x, y)] of a crowd object, or of a plain list of spots."""
    data = getattr(crowd, "data", None)
    if data is not None and hasattr(data, "vertices"):
        n = len(data.vertices)
        co = [0.0] * (3 * n)
        data.vertices.foreach_get("co", co)
        return [(co[6 * i], co[6 * i + 1]) for i in range(n // 2)]
    return [(float(p[0]), float(p[1])) for p in crowd]


def _plan_from(crowd, base):
    """(where everybody stands now [(x, y)], how they face now [(fx, fy)], how they face at rest [(fx, fy)])."""
    rest = _homes(crowd)
    data = getattr(crowd, "data", None)
    if data is not None and hasattr(data, "vertices"):
        co = [0.0] * (3 * len(data.vertices))
        data.vertices.foreach_get("co", co)
        rf = []
        for i in range(len(rest)):
            fx, fy = co[6 * i + 3] - co[6 * i], co[6 * i + 4] - co[6 * i + 1]
            fl = math.hypot(fx, fy)
            rf.append((fx / fl, fy / fl) if fl > 1e-9 else (0.0, 1.0))
    else:
        rf = [(0.0, 1.0)] * len(rest)
    if base is None:
        return rest, rf, rf
    pos, fac = base
    return [(float(p[0]), float(p[1])) for p in pos], [(float(f[0]), float(f[1])) for f in fac], rf


def _turn_to(rest_f, now_f, want):
    """The facing to store on a cue so that the member ends up facing `want`: the rest facing turned by the angle
    from the facing it has now to the one wanted (with no base the two are the same and this is `want`)."""
    if want is None or math.hypot(want[0], want[1]) < 1e-6:
        return None
    a = math.atan2(now_f[0] * want[1] - now_f[1] * want[0], now_f[0] * want[0] + now_f[1] * want[1])
    cs, sn = math.cos(a), math.sin(a)
    return rest_f[0] * cs - rest_f[1] * sn, rest_f[0] * sn + rest_f[1] * cs


def _rand(seed, n, k):
    """k numbers in 0..1 for each of n members: the same for a seed whoever takes part, so changing a radius
    does not reshuffle who ducks."""
    rng = random.Random(int(seed) * 7919 + 101)
    return [[rng.random() for _ in range(k)] for _ in range(n)]


class _Path:
    """A point or a polyline in the crowd's space, and how far along it (0..1) every vertex is: by length, or by
    `times` (one number per vertex) when the line was sampled from somebody's walk."""

    def __init__(self, points, times=None):
        try:
            float(points[0])
            self.pts = [(float(points[0]), float(points[1]))]
        except TypeError:
            self.pts = [(float(p[0]), float(p[1])) for p in points]
        n = len(self.pts)
        cum = [0.0]
        for k in range(n - 1):
            cum.append(cum[-1] + math.dist(self.pts[k], self.pts[k + 1]))
        self.length = cum[-1]
        if times is not None and len(times) == n and n > 1:
            t0, span = float(times[0]), (float(times[-1]) - float(times[0])) or 1.0
            self.u = [(float(t) - t0) / span for t in times]
        else:
            self.u = [c / (self.length or 1.0) for c in cum]

    def nearest(self, x, y):
        """(distance, nearest x, nearest y, how far along 0..1, tangent x, tangent y)."""
        pts = self.pts
        if len(pts) == 1:
            return math.hypot(x - pts[0][0], y - pts[0][1]), pts[0][0], pts[0][1], 0.0, 0.0, 0.0
        best = None
        for k in range(len(pts) - 1):
            ax, ay = pts[k]
            dx, dy = pts[k + 1][0] - ax, pts[k + 1][1] - ay
            l2 = dx * dx + dy * dy
            t = 0.0 if l2 < 1e-12 else min(1.0, max(0.0, ((x - ax) * dx + (y - ay) * dy) / l2))
            qx, qy = ax + dx * t, ay + dy * t
            d = math.hypot(x - qx, y - qy)
            if best is None or d < best[0] - 1e-9:
                best = (d, qx, qy, k, t, dx, dy)
        d, qx, qy, k, t, dx, dy = best
        tl = math.hypot(dx, dy)
        return d, qx, qy, self.u[k] + (self.u[k + 1] - self.u[k]) * t, (dx / tl if tl > 1e-9 else 0.0), (dy / tl if tl > 1e-9 else 0.0)


def _out_dir(r, x, y, d, qx, qy, tx, ty):
    """Unit direction straight out from the nearest point of a path; on the path itself, a side picked by r (0..1)."""
    if d > 1e-4:
        return (x - qx) / d, (y - qy) / d
    if tx or ty:
        s = 1.0 if r < 0.5 else -1.0
        return -ty * s, tx * s
    return math.cos(r * 2.0 * math.pi), math.sin(r * 2.0 * math.pi)


def _settle(homes, movers, project=None, keep_clear=(), recruit=False, gap=MIN_GAP, passes=400, allowed=None):
    """Make the movers of a cue keep their distance. homes: [(x, y)] where every member stands (at rest, or
    right now when the cue is planned on top of others); movers: {i: (x, y)} where the cue wants them. Returns
    {i: (x, y)}: nobody in it ends closer than `gap` to anybody else's target or spot, or inside a keep_clear
    circle [(x, y, radius)], or (project(i, x, y) -> (x, y)) inside the area the cue clears.

    Relaxation passes push people apart: one or two are enough in a loose crowd, a packed one takes more and
    stops when it no longer improves. With recruit, people standing in the way shuffle aside too and join the cue
    (a crowd making room ripples outward); without it they stand firm. Whoever is still too close after that
    takes the nearest free spot. allowed(i, x, y) -> bool says where member i may end up at all: a cue that
    clears a line uses it to keep everybody on their own side of it (nobody is sent across the walker's way)."""
    if not movers:
        return {}
    g = gap + 0.01
    pos = [[float(h[0]), float(h[1])] for h in homes]
    mv = set()
    for i, t in movers.items():
        pos[i] = [float(t[0]), float(t[1])]
        mv.add(i)

    def cell_of(x, y):
        return math.floor(x / g), math.floor(y / g)

    cells = [cell_of(p[0], p[1]) for p in pos]
    grid = {}
    for j, c in enumerate(cells):
        grid.setdefault(c, []).append(j)

    def place(i, x, y):
        pos[i][0], pos[i][1] = x, y
        c = cell_of(x, y)
        if c != cells[i]:
            grid[cells[i]].remove(i)
            grid.setdefault(c, []).append(i)
            cells[i] = c

    def constrain(i):
        x, y = pos[i]
        for _ in range(2):
            if project is not None:
                x, y = project(i, x, y)
            for cx, cy, cr in keep_clear:
                dx, dy = x - cx, y - cy
                d = math.hypot(dx, dy)
                if d < cr + 0.01:
                    if d < 1e-6:
                        dx, dy, d = math.cos(i * 2.4), math.sin(i * 2.4), 1.0
                    x, y = cx + dx / d * (cr + 0.02), cy + dy / d * (cr + 0.02)
        place(i, x, y)

    def close(i, x, y, reach):
        gx, gy = cell_of(x, y)
        for ix in (gx - 1, gx, gx + 1):
            for iy in (gy - 1, gy, gy + 1):
                for j in grid.get((ix, iy), ()):
                    if j != i:
                        dx, dy = x - pos[j][0], y - pos[j][1]
                        d = math.hypot(dx, dy)
                        if d < reach:
                            yield j, dx, dy, d

    order = sorted(mv)
    for i in order:
        constrain(i)
    best, stale = None, 0
    for _pass in range(passes):
        shift, overlap = {}, 0.0
        for i in order:
            x, y = pos[i]
            for j, dx, dy, d in close(i, x, y, g):
                push = g - d
                overlap += push
                if d < 1e-6:                    # on the same spot: any direction, opposite for the two
                    a = (min(i, j) * 7 + max(i, j) * 13) * 0.61803
                    s = 1.0 if i < j else -1.0
                    dx, dy, d = math.cos(a) * s, math.sin(a) * s, 1.0
                ux, uy = dx / d, dy / d
                if j in mv:
                    k = 0.5                     # the other one takes its half on its own turn
                elif recruit:
                    k = 0.5
                    sj = shift.setdefault(j, [0.0, 0.0])
                    sj[0] -= ux * push * 0.5
                    sj[1] -= uy * push * 0.5
                else:
                    k = 1.0
                si = shift.setdefault(i, [0.0, 0.0])
                si[0] += ux * push * k
                si[1] += uy * push * k
        if not shift:
            break
        if best is None or overlap < best * 0.99:
            best, stale = overlap, 0
        else:
            stale += 1
            if stale >= 12:                     # it no longer improves: somebody is wedged in
                break
        grown = False
        for i, (sx, sy) in shift.items():
            if i not in mv:
                mv.add(i)
                grown = True
            pos[i][0] += sx
            pos[i][1] += sy
            constrain(i)
        if grown:
            order = sorted(mv)

    # whoever is still too close takes the nearest free spot, looking first where they were heading
    def free(i, x, y):
        for _hit in close(i, x, y, gap + 0.002):
            return False
        for cx, cy, cr in keep_clear:
            if math.hypot(x - cx, y - cy) < cr:
                return False
        if project is not None:
            px, py = project(i, x, y)
            if abs(px - x) + abs(py - y) > 1e-4:
                return False
        if allowed is not None and not allowed(i, x, y):
            return False
        return True

    for i in sorted(mv):
        x, y = pos[i]
        if free(i, x, y):
            continue
        hx, hy = homes[i]
        base = math.atan2(y - hy, x - hx) if abs(x - hx) + abs(y - hy) > 1e-6 else i * 2.4
        spot = None
        for ring in range(1, 201):
            r = 0.1 * ring
            n = max(8, int(2.0 * math.pi * r / 0.25))
            for s in range(n):
                a = base + ((s + 1) // 2) * (1 if s % 2 else -1) * 2.0 * math.pi / n
                cx, cy = x + r * math.cos(a), y + r * math.sin(a)
                if free(i, cx, cy):
                    spot = (cx, cy)
                    break
            if spot is not None:
                break
        if spot is not None:
            place(i, spot[0], spot[1])
    return {i: (pos[i][0], pos[i][1]) for i in mv}


def gen_look(crowd, point, radius, share=0.7, near_bias=True, seed=0, base=None):
    """Look at: members within `radius` of `point` turn to face it. Who takes part is random with probability
    `share` (with near_bias: the people close by nearly all do, the far ones at `share`); the nearest turn first,
    each with a personal delay. Nobody moves."""
    homes, now_f, rest_f = _plan_from(crowd, base)
    px, py = float(point[0]), float(point[1])
    radius = max(float(radius), 1e-6)
    rnd = _rand(seed, len(homes), 3)
    out = {}
    for i, (x, y) in enumerate(homes):
        d = math.hypot(px - x, py - y)
        if d > radius:
            continue
        chance = share * (2.0 - d / radius) if near_bias else share
        if rnd[i][0] >= chance:
            continue
        out[i] = dict(move=(0.0, 0.0), face=_turn_to(rest_f[i], now_f[i], (px - x, py - y)), mood=0.0,
                      onset=min(1.0, 0.75 * d / radius + 0.25 * rnd[i][1]), back=rnd[i][2])
    return out


def gen_room(crowd, points, radius, seed=0, keep_clear=(), base=None):
    """Make room around: `points` is a point or a polyline; members closer than `radius` to it step straight
    out to just beyond the radius, the nearest first, without turning their backs. People standing where they
    land shuffle out of the way."""
    homes, _now_f, _rest_f = _plan_from(crowd, base)
    path = _Path(points)
    radius = float(radius)
    rnd = _rand(seed, len(homes), 2)
    movers = {}
    for i, (x, y) in enumerate(homes):
        d, qx, qy, _u, tx, ty = path.nearest(x, y)
        if d >= radius:
            continue
        nx, ny = _out_dir(rnd[i][1], x, y, d, qx, qy, tx, ty)
        r = radius + 0.05 + 0.2 * rnd[i][0]
        movers[i] = (qx + nx * r, qy + ny * r)

    def project(i, x, y):
        d, qx, qy, _u, tx, ty = path.nearest(x, y)
        if d >= radius + 0.03:
            return x, y
        nx, ny = _out_dir(rnd[i][1], x, y, d, qx, qy, tx, ty)
        return qx + nx * (radius + 0.05), qy + ny * (radius + 0.05)

    def allowed(i, x, y):
        hx, hy = homes[i]
        d0, q0x, q0y = path.nearest(hx, hy)[:3]
        d1, q1x, q1y = path.nearest(x, y)[:3]
        if d0 < 0.05 or d1 < 1e-6:
            return True
        return ((hx - q0x) * (x - q1x) + (hy - q0y) * (y - q1y)) / (d0 * d1) > -0.3      # still on its own side of it

    settled = _settle(homes, movers, project, keep_clear, recruit=True, allowed=allowed)
    dist = {i: path.nearest(homes[i][0], homes[i][1])[0] for i in settled}
    far = max([radius] + list(dist.values())) or 1.0
    return {i: dict(move=(t[0] - homes[i][0], t[1] - homes[i][1]), face=None, mood=0.0,
                    onset=dist[i] / far, back=1.0 - dist[i] / far) for i, t in settled.items()}


def gen_back(crowd, source, reach, amount=1.0, share=1.0, duck=0.25, cheer=0.2, face_away=0.0, seed=0, keep_clear=(),
             base=None):
    """Step back from: members within `reach` of `source` step away from it by `amount` (m) times a falloff that
    is strongest next to the source, each with a variation of their own (60–120 %). `share` of them take part
    (the others stand firm); of those, a share `duck` is frightened (mood -1), a share `cheer` excited (mood +1)
    and a share `face_away` also turns away. The nearest react first and come back last."""
    homes, now_f, rest_f = _plan_from(crowd, base)
    sx, sy = float(source[0]), float(source[1])
    reach = max(float(reach), 1e-6)
    rnd = _rand(seed, len(homes), 5)
    movers, away = {}, {}
    for i, (x, y) in enumerate(homes):
        d = math.hypot(x - sx, y - sy)
        if d >= reach or rnd[i][0] >= share:
            continue
        ux, uy = _out_dir(rnd[i][4], x, y, d, sx, sy, 0.0, 0.0)
        step = amount * (1.0 - d / reach) * (0.6 + 0.6 * rnd[i][1])
        movers[i] = (x + ux * step, y + uy * step)
        away[i] = (ux, uy, d)
    settled = _settle(homes, movers, None, keep_clear, recruit=False)
    out = {}
    for i, t in settled.items():
        ux, uy, d = away[i]
        r = rnd[i][2]
        out[i] = dict(move=(t[0] - homes[i][0], t[1] - homes[i][1]),
                      face=_turn_to(rest_f[i], now_f[i], (ux, uy)) if rnd[i][3] < face_away else None,
                      mood=-1.0 if r < duck else (1.0 if r < duck + cheer else 0.0),
                      onset=d / reach, back=1.0 - d / reach)
    return out


def gen_way(crowd, polyline, reach=0.9, amount=0.35, look=0.5, seed=0, keep_clear=(), times=None, base=None):
    """Make way for: somebody walks along `polyline`. Members within `reach` of it sidestep straight away from the
    line by up to `amount`, plus whatever it takes to leave 0.45 m clear on each side; a share `look` turns to the
    walker. onset AND back are how far along the line the member's nearest point is (0..1): play the cue 0 -> 1
    over the walk and the crowd parts just ahead of the walker; play Back 0 -> 1 a second later and it closes
    behind. times: one number per vertex of the polyline when it was sampled from a walk (then "how far along"
    follows the walker's clock, not the distance)."""
    homes, now_f, rest_f = _plan_from(crowd, base)
    path = _Path(polyline, times)
    reach = max(float(reach), 1e-6)
    rnd = _rand(seed, len(homes), 4)
    movers = {}
    for i, (x, y) in enumerate(homes):
        d, qx, qy, _u, tx, ty = path.nearest(x, y)
        if d >= reach:
            continue
        nx, ny = _out_dir(rnd[i][3], x, y, d, qx, qy, tx, ty)
        step = max(amount * (1.0 - d / reach) * (0.7 + 0.3 * rnd[i][0]), LINE_CLEAR + 0.03 + 0.1 * rnd[i][1] - d)
        movers[i] = (x + nx * step, y + ny * step)

    def project(i, x, y):
        d, qx, qy, _u, tx, ty = path.nearest(x, y)
        if d >= LINE_CLEAR + 0.01:
            return x, y
        nx, ny = _out_dir(rnd[i][3], x, y, d, qx, qy, tx, ty)
        return qx + nx * (LINE_CLEAR + 0.03), qy + ny * (LINE_CLEAR + 0.03)

    def lateral(x, y):
        d, qx, qy, _u, tx, ty = path.nearest(x, y)
        return tx * (y - qy) - ty * (x - qx)

    side = {}

    def allowed(i, x, y):
        if i not in side:
            side[i] = lateral(homes[i][0], homes[i][1])
        s = side[i]
        return abs(s) < 0.05 or s * lateral(x, y) > 0.0

    settled = _settle(homes, movers, project, keep_clear, recruit=True, allowed=allowed)
    out = {}
    for i, t in settled.items():
        hx, hy = homes[i]
        u = path.nearest(hx, hy)[3]
        d, qx, qy = path.nearest(t[0], t[1])[:3]
        out[i] = dict(move=(t[0] - hx, t[1] - hy),
                      face=_turn_to(rest_f[i], now_f[i], (qx - t[0], qy - t[1])) if (rnd[i][2] < look and d > 1e-4) else None,
                      mood=0.0, onset=u, back=u)
    return out


def gen_lane(crowd, a, b, half_width=1.4, seed=0, keep_clear=(), base=None):
    """Open a lane: a clear corridor from `a` to `b`, `half_width` to each side. Members inside step out
    sideways to just beyond the edge; onset and back are their position along a -> b, so the lane opens from a
    toward b and closes the same way."""
    homes, _now_f, _rest_f = _plan_from(crowd, base)
    ax, ay, bx, by = float(a[0]), float(a[1]), float(b[0]), float(b[1])
    length = math.hypot(bx - ax, by - ay)
    if length < 1e-6:
        return {}
    tx, ty = (bx - ax) / length, (by - ay) / length
    nx, ny = -ty, tx
    half_width = float(half_width)
    rnd = _rand(seed, len(homes), 2)

    def along_across(x, y):
        return (x - ax) * tx + (y - ay) * ty, (x - ax) * nx + (y - ay) * ny

    movers, side = {}, {}
    for i, (x, y) in enumerate(homes):
        s, lat = along_across(x, y)
        if s < 0.0 or s > length or abs(lat) >= half_width:
            continue
        side[i] = (1.0 if lat > 0.0 else -1.0) if abs(lat) > 0.05 else (1.0 if rnd[i][1] < 0.5 else -1.0)
        k = side[i] * (half_width + 0.05 + 0.2 * rnd[i][0]) - lat
        movers[i] = (x + nx * k, y + ny * k)

    def project(i, x, y):
        s, lat = along_across(x, y)
        if s < 0.0 or s > length or abs(lat) >= half_width + 0.03:
            return x, y
        k = (side.get(i) or (1.0 if lat >= 0.0 else -1.0)) * (half_width + 0.05) - lat
        return x + nx * k, y + ny * k

    def allowed(i, x, y):
        s0, lat0 = along_across(homes[i][0], homes[i][1])
        s1, lat1 = along_across(x, y)
        if s1 < 0.0 or s1 > length or s0 < 0.0 or s0 > length:
            return True                         # beyond the ends of the lane there is nothing to cross
        sd = side.get(i) or ((1.0 if lat0 > 0.0 else -1.0) if abs(lat0) > 0.05 else 0.0)
        return sd == 0.0 or sd * lat1 > 0.0

    settled = _settle(homes, movers, project, keep_clear, recruit=True, allowed=allowed)
    out = {}
    for i, t in settled.items():
        u = min(1.0, max(0.0, along_across(homes[i][0], homes[i][1])[0] / length))
        out[i] = dict(move=(t[0] - homes[i][0], t[1] - homes[i][1]), face=None, mood=0.0, onset=u, back=u)
    return out


def gen_mood(crowd, point, radius, mood=1.0, share=0.6, seed=0, base=None):
    """Cheer: nobody moves; a share of the members within `radius` of `point` gets the mood (+1 excited: they
    bounce; -1 frightened: they shrink), each starting at a moment of their own."""
    homes, _now_f, _rest_f = _plan_from(crowd, base)
    px, py = float(point[0]), float(point[1])
    rnd = _rand(seed, len(homes), 3)
    out = {}
    for i, (x, y) in enumerate(homes):
        if math.hypot(px - x, py - y) <= radius and rnd[i][0] < share:
            out[i] = dict(move=(0.0, 0.0), face=None, mood=float(mood), onset=rnd[i][1], back=rnd[i][2])
    return out


def _poisson(ok, bounds, r, rng, tries=30):
    """Blue noise: points at least r apart wherever ok(x, y), as many as fit. Every island of the region is seeded."""
    x0, y0, x1, y1 = bounds
    cell = r / math.sqrt(2.0)
    grid, pts = {}, []

    def fits(x, y):
        if not ok(x, y):
            return False
        gx, gy = int((x - x0) / cell), int((y - y0) / cell)
        for ix in range(gx - 2, gx + 3):
            for iy in range(gy - 2, gy + 3):
                q = grid.get((ix, iy))
                if q is not None and (q[0] - x) ** 2 + (q[1] - y) ** 2 < r * r:
                    return False
        return True

    def put(x, y):
        pts.append((x, y))
        grid[(int((x - x0) / cell), int((y - y0) / cell))] = (x, y)

    while True:
        seed_pt = None
        for _ in range(300):
            x, y = rng.uniform(x0, x1), rng.uniform(y0, y1)
            if fits(x, y):
                seed_pt = (x, y)
                break
        if seed_pt is None:
            break
        put(*seed_pt)
        active = [seed_pt]
        while active:
            k = rng.randrange(len(active))
            ax, ay = active[k]
            for _ in range(tries):
                ang, rad = rng.uniform(0.0, 2.0 * math.pi), rng.uniform(r, 2.0 * r)
                x, y = ax + math.cos(ang) * rad, ay + math.sin(ang) * rad
                if fits(x, y):
                    put(x, y)
                    active.append((x, y))
                    break
            else:
                active.pop(k)
    return pts


def choreo_scatter(region_test, bounds, count, spacing=0.6, clump=3, seed=1, keep_clear=()):
    """Where an audience stands: about `count` spots [(x, y)] inside a region, in loose groups of 1 to `clump`
    people (people of a group 0.55–0.8 m apart, the groups further apart), nobody closer than `spacing` to anybody.
    region_test(x, y) -> bool; bounds = (x0, y0, x1, y1); keep_clear = [(x, y, radius)] left empty. Fewer than
    `count` come back when no more fit. clump = 1 is plain even noise."""
    rng = random.Random(int(seed) * 104729 + 7)
    x0, y0, x1, y1 = (float(v) for v in bounds)
    count, clump = int(count), max(1, int(clump))
    spacing = max(0.3, float(spacing))
    if count <= 0 or x1 <= x0 or y1 <= y0:
        return []
    lo = max(MIN_GAP, spacing)              # people of one group stand this far apart …
    hi = max(0.8, lo + 0.2)                 # … to this far

    def allowed(x, y):
        if not (x0 <= x <= x1 and y0 <= y <= y1) or not region_test(x, y):
            return False
        return not any((x - cx) ** 2 + (y - cy) ** 2 < cr * cr for cx, cy, cr in keep_clear)

    probes = 3000
    inside = sum(1 for _ in range(probes) if allowed(rng.uniform(x0, x1), rng.uniform(y0, y1)))
    area = (x1 - x0) * (y1 - y0) * inside / probes
    if area <= 0.0:
        return []
    sizes, total = [], 0
    while total < count:
        k = min(rng.randint(1, clump), count - total)
        sizes.append(k)
        total += k

    pts, group, grid = [], [], {}

    def near(x, y, reach, own=None):
        """Is anybody (not counting the group `own`) closer than reach?"""
        rc = int(reach / spacing) + 1
        gx, gy = math.floor(x / spacing), math.floor(y / spacing)
        for ix in range(gx - rc, gx + rc + 1):
            for iy in range(gy - rc, gy + rc + 1):
                for j in grid.get((ix, iy), ()):
                    if group[j] != own and (pts[j][0] - x) ** 2 + (pts[j][1] - y) ** 2 < reach * reach:
                        return True
        return False

    def put(x, y, g):
        grid.setdefault((math.floor(x / spacing), math.floor(y / spacing)), []).append(len(pts))
        pts.append((x, y))
        group.append(g)

    # where the groups stand: even noise, as far apart as the head count allows
    dist = max(spacing, math.sqrt(0.62 * area / len(sizes)))
    centres = []
    for _ in range(8):
        centres = _poisson(allowed, (x0, y0, x1, y1), dist, rng)
        if len(centres) >= len(sizes) or dist <= spacing * 1.001:
            break
        dist = max(spacing, dist * 0.85)
    rng.shuffle(centres)
    sep = max(spacing, min(hi + 0.3, dist - hi))        # people of different groups keep at least this apart
    for g, (cx, cy) in enumerate(centres[:len(sizes)]):
        if near(cx, cy, spacing):
            continue
        put(cx, cy, g)
        mates = [(cx, cy)]
        for _m in range(sizes[g] - 1):
            spot = None
            for limit in (sep, spacing):
                for _t in range(24):
                    ax, ay = mates[rng.randrange(len(mates))]
                    ang, r = rng.uniform(0.0, 2.0 * math.pi), rng.uniform(lo, hi)
                    x, y = ax + r * math.cos(ang), ay + r * math.sin(ang)
                    if allowed(x, y) and all(math.dist((x, y), q) >= lo for q in mates) and not near(x, y, limit, own=g):
                        spot = (x, y)
                        break
                if spot is not None:
                    break
            if spot is not None:
                put(spot[0], spot[1], g)
                mates.append(spot)
    # top up with people on their own, if groups did not fit
    tries, budget = 0, 3000 + 40 * count
    while len(pts) < count and tries < budget:
        tries += 1
        x, y = rng.uniform(x0, x1), rng.uniform(y0, y1)
        if allowed(x, y) and not near(x, y, sep if tries < budget // 2 else spacing):
            put(x, y, -1 - len(pts))
    return pts[:count]


# ------------------------------------------------------------------ operators
class BBCROWD_OT_add_zone(bpy.types.Operator):
    """Add a crowd controller: a subdivided plane at the 3D cursor, its +Y turned toward the Tower if one is picked. Shape, move or keyframe it like any mesh"""
    bl_idname = "bbcrowd.add_zone"
    bl_label = "Add Crowd Controller at Cursor"
    bl_options = {'REGISTER', 'UNDO'}

    width: bpy.props.FloatProperty(name="Width", default=20.0, min=1.0)
    depth: bpy.props.FloatProperty(name="Depth", default=12.0, min=1.0)
    cuts: bpy.props.IntProperty(name="Subdivisions", default=6, min=1, max=40)

    def execute(self, context):
        sc = context.scene
        ng = ensure_group()
        n = len(zones(sc)) + 1
        me = plane_mesh(f"BB Crowd {n:02d}", self.width, self.depth, self.cuts, max(1, round(self.cuts * self.depth / self.width)))
        ob = bpy.data.objects.new(f"BB Crowd {n:02d}", me)
        ob.location = sc.cursor.location.copy()
        ob[CTRL_KEY] = True
        crowd_coll(sc).objects.link(ob)
        m = ob.modifiers.new(MOD, 'NODES')
        m.node_group = ng
        ob.show_wire = True
        sc.bb_crowd_obj = ob
        tower = sc.bb_crowd_tower
        if tower is not None:
            set_input(m, "Tower", tower)
            d = tower.matrix_world.translation - ob.location
            ob.rotation_euler = (0.0, 0.0, math.atan2(-d.x, d.y))
        set_input(m, "Influencers", mirror_of(sc))
        peg_material_for(ob)
        sync_mirror(sc)
        context.view_layer.update()
        for o in context.selected_objects:
            o.select_set(False)
        try:
            ob.select_set(True)
            context.view_layer.objects.active = ob
        except RuntimeError:
            pass
        return {'FINISHED'}


class BBCROWD_OT_key(bpy.types.Operator):
    """Key this input of the active controller on the current frame"""
    bl_idname = "bbcrowd.key"
    bl_label = "Key"
    name: bpy.props.StringProperty()

    def execute(self, context):
        m = crowd_mod(active_zone(context))
        if m is None:
            return {'CANCELLED'}
        sock_of(m, self.name).keyframe_insert("value", frame=context.scene.frame_current)
        return {'FINISHED'}


class BBCROWD_OT_reset(bpy.types.Operator):
    """Re-seed the crowd: drop the cached simulation of the active controller and jump to the first frame (spacing, density and seed take effect at birth)"""
    bl_idname = "bbcrowd.reset"
    bl_label = "Reset Crowd"

    def execute(self, context):
        ob = active_zone(context)
        if ob is None:
            return {'CANCELLED'}
        reset_sim(context, ob)
        return {'FINISHED'}


class BBCROWD_OT_bake(bpy.types.Operator):
    """Bake the active controller's simulation over the scene range so it scrubs freely and never changes (Bake again after edits; Reset drops it)"""
    bl_idname = "bbcrowd.bake"
    bl_label = "Bake Crowd"

    def execute(self, context):
        ob = active_zone(context)
        if ob is None:
            return {'CANCELLED'}
        sc = context.scene
        for o in sc.objects:
            o.select_set(False)
        ob.select_set(True)
        context.view_layer.objects.active = ob
        try:
            if hasattr(bpy.ops.object, "simulation_nodes_cache_bake"):
                bpy.ops.object.simulation_nodes_cache_bake(selected=True)
            else:
                self.report({'ERROR'}, "This Blender has no simulation bake operator")
                return {'CANCELLED'}
        except Exception as e:
            self.report({'ERROR'}, f"Bake failed: {e}")
            return {'CANCELLED'}
        return {'FINISHED'}


class BBCROWD_OT_influence(bpy.types.Operator):
    """Add the selected objects as influencers (or pull every character and prop of this BB Stage staging)"""
    bl_idname = "bbcrowd.influence"
    bl_label = "Add Influencers"
    bl_options = {'REGISTER', 'UNDO'}

    source: bpy.props.EnumProperty(items=[('SELECTED', "Selected", ""), ('STAGE', "From BB Stage", "")], default='SELECTED')

    def execute(self, context):
        sc = context.scene
        if self.source == 'STAGE':
            st = bbstage()
            if st is None:
                self.report({'ERROR'}, "BB Stage is not enabled")
                return {'CANCELLED'}
            if not st.is_staging(sc):
                self.report({'ERROR'}, "Open a BB Stage staging first (its characters live there)")
                return {'CANCELLED'}
            obs = [o for o in st.stage_objects(sc, roles=("char", "prop")) if o.name in sc.objects]
        else:
            obs = [o for o in context.selected_objects if crowd_mod(o) is None and not o.get(MIRROR_KEY)
                   and not o.get(CH_TAG) and not o.get(CUE_TAG)]
        for o in obs:
            o.bb_crowd.on = True
        sync_mirror(sc)
        return {'FINISHED'}


class BBCROWD_OT_uninfluence(bpy.types.Operator):
    """Drop this object from the influencers"""
    bl_idname = "bbcrowd.uninfluence"
    bl_label = "Remove"
    name: bpy.props.StringProperty()

    def execute(self, context):
        ob = bpy.data.objects.get(self.name)
        if ob is not None:
            ob.bb_crowd.on = False
        sync_mirror(context.scene)
        return {'FINISHED'}


class BBCROWD_OT_sync(bpy.types.Operator):
    """Rebuild the influencer mirror, point every controller at it, upgrade controllers from older versions and drop stale mirrors"""
    bl_idname = "bbcrowd.sync"
    bl_label = "Sync Influencers"

    def execute(self, context):
        sc = context.scene
        for z in zones(sc):
            upgrade_zone(sc, z)
        for c in choreo_crowds(sc):             # choreographed crowds: sliders and nodes in line with their cue lists
            choreo_sync(c)
        sync_mirror(sc)
        for ob in list(bpy.data.objects):
            if ob.get(MIRROR_KEY) and not any(ob.name in s.objects for s in bpy.data.scenes):
                _remove_object(ob)
        context.view_layer.update()
        return {'FINISHED'}


class BBCROWD_OT_clear_keys(bpy.types.Operator):
    """Remove the test keys from the controllers' inputs and from the test driver objects"""
    bl_idname = "bbcrowd.clear_keys"
    bl_label = "Clear Test Keys"
    bl_options = {'REGISTER', 'UNDO'}

    def execute(self, context):
        sc = context.scene
        for z in zones(sc):
            m = crowd_mod(z)
            vals = {}
            for nm in ZONE_INPUTS:
                try:
                    vals[nm] = sock_of(m, nm).value
                except Exception:
                    pass
            if z.animation_data:
                z.animation_data_clear()
            vals["Panic"] = 0.0
            for nm, v in vals.items():
                set_input(m, nm, v)
        for d in sc.objects:
            if d.get("bb_crowd_test_driver") and d.animation_data:
                loc, rot = d.location.copy(), d.rotation_euler.copy()
                d.animation_data_clear()
                d.location, d.rotation_euler = loc, rot
        context.view_layer.update()
        return {'FINISHED'}


def _key_driver(d, zone, fx, fy, z, frame):
    d.location = zone.matrix_world @ Vector((fx, fy, z))
    d.rotation_euler = (0.0, 0.0, zone.rotation_euler.z)
    d.keyframe_insert("location", frame=frame)
    d.keyframe_insert("rotation_euler", frame=frame)


class BBCROWD_OT_test(bpy.types.Operator):
    """Key a scripted test on the active controller and two test drivers, re-seed the crowd and play from the first frame"""
    bl_idname = "bbcrowd.test"
    bl_label = "Run Test"
    bl_options = {'REGISTER', 'UNDO'}

    kind: bpy.props.EnumProperty(items=[
        ('SWIVEL', "Swivel", "A gaze attractor (the cone holder) steps out front; non-veterans turn to it"),
        ('WALK', "Walk through", "A walker with Move −1 crosses the crowd; members step aside just enough and close behind"),
        ('PANIC', "Panic", "The collapse: non-veterans run from the tower, veterans stand"),
        ('ALL', "All", "Swivel, the walk, then the panic, then everything settles")])
    play: bpy.props.BoolProperty(default=True)

    def execute(self, context):
        sc = context.scene
        zone = active_zone(context)
        m = crowd_mod(zone)
        if m is None:
            self.report({'ERROR'}, "Add a crowd controller first")
            return {'CANCELLED'}
        bpy.ops.bbcrowd.clear_keys()
        coll = crowd_coll(sc)

        def driver(name, kind, size, gaze, move, radius):
            d = sc.objects.get(name)
            if d is None:
                d = bpy.data.objects.new(name, None)
                d.empty_display_type, d.empty_display_size = kind, size
                coll.objects.link(d)
            d["bb_crowd_test_driver"] = True
            d.bb_crowd.on = True
            d.bb_crowd.gaze, d.bb_crowd.move, d.bb_crowd.radius = gaze, move, radius
            return d

        att = driver("Test · cone holder", 'CONE', 1.2, 1.0, 0.0, 2.5)
        walker = driver("Test · walker", 'SPHERE', 0.6, 0.0, -1.0, 2.5)
        k = self.kind
        if k in ('SWIVEL', 'ALL'):
            att.bb_crowd.gaze = 1.0
            _key_driver(att, zone, 0.0, -2.0, 0.0, 1)
            _key_driver(att, zone, 0.0, -2.0, 0.0, 30)
            _key_driver(att, zone, 0.0, 4.0, 0.0, 60)
            _key_driver(att, zone, 0.0, 4.0, 0.0, 240)
        else:
            att.bb_crowd.gaze = 0.0
            _key_driver(att, zone, 0.0, -30.0, 0.0, 1)
        if k in ('WALK', 'ALL'):
            f0 = 1 if k == 'WALK' else 80
            _key_driver(walker, zone, -3.0, -12.0, 0.0, f0)
            _key_driver(walker, zone, -3.0, 10.0, 0.0, f0 + 110)
            _key_driver(walker, zone, -3.0, 10.0, 0.0, 240)
        else:
            _key_driver(walker, zone, 0.0, -30.0, 0.0, 1)
        if k in ('PANIC', 'ALL'):
            key_input(m, "Panic", 0.0, 1 if k == 'PANIC' else 190)
            key_input(m, "Panic", 1.0, 30 if k == 'PANIC' else 215)
            key_input(m, "Panic", 1.0, 100 if k == 'PANIC' else 225)
            key_input(m, "Panic", 0.0, 140 if k == 'PANIC' else 240)
        else:
            key_input(m, "Panic", 0.0, 1)
        sync_mirror(sc)
        sc.frame_start, sc.frame_end = 1, 240
        reset_sim(context, zone)
        context.view_layer.update()
        if self.play and context.screen is not None and not context.screen.is_animation_playing:
            try:
                bpy.ops.screen.animation_play()
            except Exception:
                pass
        return {'FINISHED'}


class BBCROWD_OT_pick(bpy.types.Operator):
    """Make this the active controller for the panel"""
    bl_idname = "bbcrowd.pick"
    bl_label = "Pick Controller"
    name: bpy.props.StringProperty()

    def execute(self, context):
        ob = bpy.data.objects.get(self.name)
        if crowd_mod(ob) is not None:
            context.scene.bb_crowd_obj = ob
        return {'FINISHED'}


# ------------------------------------------------------------------ choreographed crowds: operators
class CueError(Exception):
    """Something a cue operator cannot do, said in words for the director (shown as the operator's error)."""


def _choreo_poll(self, ob):
    return ob.type == 'MESH' and bool(ob.get(CH_TAG))


_FIRST_CROWD = {"scene": "", "at": 0.0, "name": ""}


def active_choreo(context):
    """The choreographed crowd the panel works on: the one picked, else the scene's first."""
    sc = context.scene
    ob = getattr(sc, "bb_crowd_choreo", None)
    if ob is not None and ob.get(CH_TAG) and sc.objects.get(ob.name) == ob:
        return ob
    # nothing picked: the scene's first crowd, looked for at most twice a second (a set scene holds thousands
    # of objects, and every button of the panel asks on every redraw)
    now = time.monotonic()
    if _FIRST_CROWD["scene"] != sc.name or now - _FIRST_CROWD["at"] > 0.5:
        cs = choreo_crowds(sc)
        _FIRST_CROWD.update(scene=sc.name, at=now, name=cs[0].name if cs else "")
    ob = sc.objects.get(_FIRST_CROWD["name"]) if _FIRST_CROWD["name"] else None
    return ob if (ob is not None and ob.type == 'MESH' and ob.get(CH_TAG)) else None


def working_choreo(context):
    """The crowd an operator is about to change, brought in line first (choreo_sync: cheap when nothing is off).
    This is where a crowd made by crowd_choreo.py gets its cue list and a duplicated crowd its own cues."""
    crowd = active_choreo(context)
    choreo_sync(crowd)
    return crowd


def _active_cue(crowd):
    cues = crowd.bb_crowd_cues
    i = crowd.bb_crowd_cue_index
    return cues[i] if 0 <= i < len(cues) else None


def _fps(scene):
    return scene.render.fps / scene.render.fps_base


def _depsgraph(scene):
    ctx = bpy.context
    if ctx.scene == scene:
        return ctx.evaluated_depsgraph_get()
    dg = scene.view_layers[0].depsgraph
    dg.update()
    return dg


def _in_scene(scene, ob):
    return ob is not None and scene.objects.get(ob.name) == ob


class _FrameGuard:
    """Visit other frames and come back as if nothing happened: the playhead returns, and so does anything that
    was moved but not keyed yet (a frame change re-reads the keys and would wipe it)."""

    def __init__(self, scene):
        self.scene = scene
        self.moved = False
        self.poses = []

    def __enter__(self):
        self.frame, self.sub = self.scene.frame_current, self.scene.frame_subframe
        return self

    def go(self, frame, force=False):
        """Put the scene on a frame. Staying on the current frame keeps what is on screen (unkeyed moves and
        all) unless force: then the frame is read again from its keys, like every other frame visited."""
        sc = self.scene
        if not force and sc.frame_current == frame and (self.moved or abs(sc.frame_subframe) < 1e-6):
            return
        if not self.moved:
            self.poses = [(o, o.matrix_basis.copy()) for o in sc.objects
                          if o.animation_data is not None and o.animation_data.action is not None]
            self.moved = True
        sc.frame_set(frame)

    def __exit__(self, *exc):
        if self.moved:
            sc = self.scene
            sc.frame_set(self.frame, subframe=self.sub)
            for o, mb in self.poses:
                if any(abs(o.matrix_basis[r][c] - mb[r][c]) > 1e-6 for r in range(4) for c in range(4)):
                    o.matrix_basis = mb
        return False


def choreo_keep_clear(scene, space, depsgraph=None, radius=0.6, skip=()):
    """Spots nobody may end on, for the generators: the staging's characters and props and the BB Crowd
    influencers where they are now, as [(x, y, radius)] in `space` (a crowd object or its world matrix)."""
    mw = space.matrix_world if hasattr(space, "matrix_world") else space
    inv = mw.inverted()
    obs = list(influencers(scene))
    st = bbstage()
    if st is not None and st.is_staging(scene):
        obs += [o for o in st.stage_objects(scene, roles=("char", "prop")) if _in_scene(scene, o)]
    out, seen = [], set()
    for o in obs:
        if o.name in seen or o in skip:
            continue
        seen.add(o.name)
        ev = o.evaluated_get(depsgraph) if depsgraph is not None else o
        p = inv @ ev.matrix_world.translation
        out.append((p.x, p.y, min(2.5, max(radius, 0.5 * max(o.dimensions.x, o.dimensions.y)))))
    return out


def _walk_window(scene, frame, seconds):
    """The frames of the walk the playhead is in. In a BB Stage staging: the move into the beat the playhead is
    on or heading for, from the frame the beat before it is left to the frame it is reached (the same move BB
    Stage draws a path for). Anywhere else: `seconds` from the playhead."""
    st = bbstage()
    if st is not None and st.is_staging(scene):
        beats = list(scene.bb_st.beats)
        if len(beats) >= 2:
            i = next((k for k in range(1, len(beats)) if frame <= st.beat_out(beats[k])), len(beats) - 1)
            a, b = st.beat_out(beats[i - 1]), beats[i].frame
            if b > a:
                return int(a), int(b)
    return int(frame), int(frame + max(2, round(seconds * _fps(scene))))


def choreo_update_cue(scene, crowd, cue, frame=None):
    """Run the cue's generator again from what the cue remembers (kind, numbers, source), reading the source on
    the frame the cue was made on (or `frame`) and planning from where the crowd is on that frame: the other cues
    as far as they are played there, this cue not at all (base=choreo_state). Returns how many members take
    part. Hand edits are replaced; the timing is not touched. Raises CueError with a message for the director."""
    kind = cue.kind
    if kind == 'HAND':
        raise CueError("This reaction was placed by hand: there is nothing to update it from")
    ob = cue.obj
    if ob is None:
        raise CueError("This reaction has lost its object: delete it and make it again")
    if ob.mode == 'EDIT':
        raise CueError("Press Done first")
    if frame is not None:
        cue.frame = int(frame)
    inv = crowd.matrix_world.inverted()
    src, src_b = cue.source, cue.source_b
    if kind == 'WAY' and not _in_scene(scene, src):
        raise CueError("The walker of this reaction is no longer in the scene")
    if kind == 'WAY' and cue.win_b <= cue.win_a:
        raise CueError("The walk must end on a later frame than it starts on")

    def where(o, stored, dg):
        if _in_scene(scene, o):
            return inv @ o.evaluated_get(dg).matrix_world.translation
        return Vector(stored)

    with _FrameGuard(scene) as guard:
        pts, times = [], []
        if kind == 'WAY':
            a, b = cue.win_a, cue.win_b
            for f in list(range(a, b, 2)) + [b]:
                guard.go(f, force=True)         # the walk as it is keyed, on every frame alike
                p = inv @ src.evaluated_get(_depsgraph(scene)).matrix_world.translation
                pts.append((p.x, p.y))
                times.append(f)
        guard.go(cue.frame)
        dg = _depsgraph(scene)
        keep = choreo_keep_clear(scene, crowd, dg, skip=(src,) if kind == 'WAY' else ())
        p0, p1 = where(src, cue.point, dg), where(src_b, cue.point_b, dg)
    cue.point, cue.point_b = p0, p1
    # where the crowd is at that moment: every other cue as far as it is played on that frame, this one not at all
    weights = choreo_weights(crowd, cue.frame)
    weights[cue.name] = (0.0, 0.0)
    base = choreo_state(crowd, weights)
    if kind == 'LOOK':
        members = gen_look(crowd, p0, cue.radius, cue.share, cue.near_bias, cue.seed, base=base)
    elif kind == 'ROOM':
        members = gen_room(crowd, p0, cue.radius, cue.seed, keep, base=base)
    elif kind == 'BACK':
        members = gen_back(crowd, p0, cue.reach, cue.amount, cue.share, cue.duck, cue.cheer, cue.face_away, cue.seed, keep,
                           base=base)
    elif kind == 'WAY':
        if _Path(pts).length < 0.3:
            raise CueError(f"{src.name} does not move between frames {cue.win_a} and {cue.win_b}: "
                           "put the playhead on the beat it walks to")
        members = gen_way(crowd, pts, cue.reach, cue.amount, cue.look, cue.seed, keep, times=times, base=base)
    elif kind == 'LANE':
        members = gen_lane(crowd, p0, p1, cue.half_width, cue.seed, keep, base=base)
    else:
        members = gen_mood(crowd, p0, cue.radius, cue.mood, cue.share, cue.seed, base=base)
    _cue_write(crowd, cue, members)
    return len(members)


def _cue_sources(context, crowd, kind):
    """(source, second source) for a new cue: the active object, and for a lane the two selected objects."""
    scene = context.scene

    def usable(o):
        return (_in_scene(scene, o) and o != crowd and not o.get(CUE_TAG) and not o.get(MIRROR_KEY)
                and not o.get(CH_TAG))

    act = context.view_layer.objects.active
    if kind == 'HAND':
        return None, None
    if kind == 'LANE':
        sel = [o for o in context.selected_objects if usable(o)]
        if usable(act) and any(o != act for o in sel):
            return next(o for o in sel if o != act), act
        if len(sel) >= 2:
            return sel[0], sel[1]
        raise CueError("Select the two things the lane runs between: where it starts, then where it ends")
    if not usable(act):
        raise CueError({'LOOK': "Select what the crowd should look at first",
                        'ROOM': "Select what the crowd should make room around first",
                        'BACK': "Select what the crowd should step back from first",
                        'WAY': "Select who walks through the crowd first",
                        'MOOD': "Select what the crowd cheers around first"}[kind])
    return act, None


def _cue_title(kind, src, src_b, mood=1.0):
    if kind == 'HAND':
        return "By hand"
    if kind == 'LANE':
        return f"Lane {src.name} to {src_b.name}"
    if kind == 'MOOD':
        return f"{'Cheer' if mood >= 0.0 else 'Fright'} near {src.name}"
    return f"{CUE_LABEL[kind]} {src.name}"


def _cue_ease(cue):
    """Make way and lanes follow a walker: straight ramps. Everything else: soft shoulders."""
    return 0.0 if cue.kind in ('WAY', 'LANE') else 0.33


def _way_timing(scene, crowd, cue):
    """Make way for: each person starts to step aside about a second before the walker is level with them (the
    sidestep lasts 0.8 s and is over a quarter of a second early) and the crowd closes 30 frames behind, all
    along the walk. The 0.8 s holds whatever the length of the walk, which fixes Wave <-> Together."""
    a, b = cue.win_a, cue.win_b
    own = max(2, round(0.8 * _fps(scene)))
    _CH_QUIET["on"] = True
    try:
        cue.width = min(1.0, max(0.02, own / float((b - a) + own)))
    finally:
        _CH_QUIET["on"] = False
    _cue_shape_update(cue, None)
    name = cue.name
    choreo_clear_keys(crowd, name)
    lead = own + max(1, round(0.25 * _fps(scene)))    # the sidestep is over a quarter of a second before the walker is level
    choreo_key(crowd, name, rise=[(a - lead, 0.0), (b - lead + own, 1.0)], back=[(a + 30, 0.0), (b + 30 + own, 1.0)], ease=0.0)
    cue.key_a, cue.key_b = a, b


def choreo_new_cue(context, crowd, kind, seconds=1.5, width=0.4, snap=2.0, **params):
    """What the New Cue buttons do: a cue of `kind` from the active object (for a lane: the two selected
    objects) on the current frame, with Play keyed 0 -> 1 from here. Returns (cue, how many take part)."""
    scene = context.scene
    if choreo_editing(crowd) is not None:
        raise CueError("Press Done on the reaction you are editing first")
    src, src_b = _cue_sources(context, crowd, kind)
    f = scene.frame_current
    name = _cue_title(kind, src, src_b, params.get("mood", 1.0))
    cue = choreo_add_cue(crowd, name, {}, width=width, snap=snap, kind=kind, sync=False,
                         source=src, source_b=src_b, frame=f, seconds=seconds, **params)
    name = cue.name
    n = 0
    try:
        if kind == 'WAY':
            cue.win_a, cue.win_b = _walk_window(scene, f, seconds)
        if kind != 'HAND':
            n = choreo_update_cue(scene, crowd, cue)
            if n == 0:
                raise CueError("Nobody in the crowd is close enough to react")
    except Exception:
        choreo_remove_cue(crowd, name)      # nothing half-made stays behind
        raise
    choreo_sync(crowd)
    cue = choreo_cue(crowd, name)
    if kind == 'WAY':
        _way_timing(scene, crowd, cue)
    else:
        choreo_key(crowd, name, rise=[(f, 0.0), (f + max(1, round(seconds * _fps(scene))), 1.0)], ease=_cue_ease(cue))
    return cue, n


def _cue_take_part(crowd, cue):
    """After Edit Positions: whoever was moved, turned or given a mood by hand takes part in the cue."""
    me = cue.obj.data
    n = choreo_members(crowd)
    if len(me.vertices) != 2 * n:
        return -1
    a, b = [0.0] * (6 * n), [0.0] * (6 * n)
    crowd.data.vertices.foreach_get("co", a)
    me.vertices.foreach_get("co", b)
    for an in ("part", "onset", "back"):
        if an not in me.attributes:
            me.attributes.new(an, 'FLOAT', 'POINT')
    part = [0.0] * (2 * n)
    me.attributes["part"].data.foreach_get("value", part)
    joined = 0
    for i in range(n):
        k = 6 * i
        moved = abs(b[k] - a[k]) + abs(b[k + 1] - a[k + 1])
        turned = abs((b[k + 3] - b[k]) - (a[k + 3] - a[k])) + abs((b[k + 4] - b[k + 1]) - (a[k + 4] - a[k + 1]))
        mood = abs((b[k + 5] - b[k + 2]) - (a[k + 5] - a[k + 2]))
        if part[2 * i] < 0.5 and moved + turned + mood > 1e-4:
            part[2 * i] = 1.0
            joined += 1
    if joined:
        me.attributes["part"].data.foreach_set("value", part)
        me.update()
    return joined


def choreo_edit_begin(context, crowd, cue):
    """Edit Positions: show the cue's object, make it the only selected and active object and enter Edit Mode.
    The crowd shows this cue fully played meanwhile, so the people follow the lines as they are moved."""
    ob = cue.obj
    if ob is None or len(ob.data.vertices) != len(crowd.data.vertices):
        raise CueError("This reaction no longer matches the crowd: delete it and make it again")
    if context.mode != 'OBJECT':
        try:
            bpy.ops.object.mode_set(mode='OBJECT')
        except RuntimeError:
            pass
    vl = context.view_layer
    ts = context.tool_settings
    _EDIT_PREV[crowd.name] = dict(selected=[o.name for o in context.selected_objects],
                                  active=vl.objects.active.name if vl.objects.active is not None else "",
                                  select_mode=tuple(ts.mesh_select_mode))
    ob.hide_viewport = False
    try:
        ob.hide_set(False)
    except RuntimeError:
        pass
    vl.update()
    for o in list(context.selected_objects):
        o.select_set(False)
    ob.select_set(True)
    vl.objects.active = ob
    st = bbstage()
    if st is not None and hasattr(st, "request_sync"):
        st.request_sync(0.0)                # BB Stage's panes show only what it has put in their local view
    prev = ch_sock(crowd, "Preview")
    if prev is not None:
        prev.value = cue.uid
    crowd.update_tag()
    try:
        bpy.ops.object.mode_set(mode='EDIT')
    except RuntimeError:
        choreo_edit_end(context, crowd, cue)        # back to how it was
        raise CueError("This reaction cannot be opened for editing here: its object cannot be shown in this view")
    ts.mesh_select_mode = (False, True, False)     # a person is a short line: pick the line, not one of its ends


def choreo_edit_end(context, crowd, cue):
    """Done: leave Edit Mode, hide the cue's object again and go back to what was selected before."""
    ob = cue.obj if cue is not None else None
    vl = context.view_layer
    joined = 0
    if ob is not None:
        if ob.mode == 'EDIT':
            try:
                vl.objects.active = ob
                bpy.ops.object.mode_set(mode='OBJECT')
            except RuntimeError:
                pass
        joined = _cue_take_part(crowd, cue)
        try:
            ob.select_set(False)
        except RuntimeError:
            pass
        ob.hide_viewport = True
    prev = ch_sock(crowd, "Preview")
    if prev is not None:
        prev.value = 0
    was = _EDIT_PREV.pop(crowd.name, None)
    if was is not None:
        for nm in was["selected"]:
            o = context.scene.objects.get(nm)
            if o is not None:
                try:
                    o.select_set(True)
                except RuntimeError:
                    pass
        act = context.scene.objects.get(was["active"])
        if act is not None:
            vl.objects.active = act
        context.tool_settings.mesh_select_mode = was["select_mode"]
    crowd.update_tag()
    return joined


class BBCROWD_OT_choreo_convert(bpy.types.Operator):
    """Turn the simulated crowd into a choreographed one. Everybody stays where they stand on this frame and watches what the simulated crowd watched. The simulated crowd is hidden, not deleted"""
    bl_idname = "bbcrowd.choreo_convert"
    bl_label = "Convert Simulated Crowd"
    bl_options = {'REGISTER', 'UNDO'}

    @classmethod
    def poll(cls, context):
        return active_zone(context) is not None

    def execute(self, context):
        sc = context.scene
        zone = active_zone(context)
        m = crowd_mod(zone)
        hidden = zone.hide_viewport
        try:
            hidden = hidden or zone.hide_get()
        except RuntimeError:
            pass
        if hidden:
            self.report({'ERROR'}, f"{zone.name} is hidden: show it first (its people must be standing somewhere)")
            return {'CANCELLED'}
        # where people really stand: without the step aside for the lens, which is only drawn
        lens = None
        try:
            lens = sock_of(m, "Lens clearance")
        except Exception:
            pass
        lens_was = lens.value if lens is not None else 0.0
        if lens_was:
            set_input(m, "Lens clearance", 0.0)
            context.view_layer.update()
        dg = context.evaluated_depsgraph_get()
        mats = [i.matrix_world.copy() for i in dg.object_instances
                if i.is_instance and i.parent is not None and i.parent.original == zone]
        if lens_was:
            set_input(m, "Lens clearance", lens_was)
        if not mats:
            self.report({'ERROR'}, f"{zone.name} has nobody on this frame: go to a frame where its people stand")
            return {'CANCELLED'}
        loc, rot, _scale = zone.matrix_world.decompose()
        world = Matrix.LocRotScale(loc, rot, None)
        inv = world.inverted()
        homes = [tuple(inv @ mw.translation) for mw in mats]
        tower = None
        try:
            tower = sock_of(m, "Tower").value
        except Exception:
            pass
        look, facings = None, None
        if tower is not None:
            t = inv @ tower.matrix_world.translation
            look = (t.x, t.y)
        else:
            r3 = inv.to_3x3()
            facings = [tuple((r3 @ (mw.to_3x3() @ Vector((0.0, 1.0, 0.0)))).xy) for mw in mats]
        coll = zone.users_collection[0] if zone.users_collection else None
        crowd = choreo_make(sc, f"{zone.name} · choreographed", homes, look, collection=coll, world=world,
                            material=peg_material_for(zone), facings=facings)
        try:
            ch_sock(crowd, "Peg height").value = min(2.3, max(0.5, sock_of(m, "Peg height").value * 1.75 / 1.7))
            # the lens clearance is not carried over: a simulated crowd steps aside, a choreographed one would vanish
            ch_sock(crowd, "Lens reach").value = sock_of(m, "Lens reach").value
        except Exception:
            pass
        zone.hide_viewport = True
        zone.hide_render = True
        sc.bb_crowd_choreo = crowd
        crowd.update_tag()
        self.report({'INFO'}, f"{crowd.name}: {len(homes)} people. {zone.name} is hidden, not deleted")
        return {'FINISHED'}


class BBCROWD_OT_choreo_scatter(bpy.types.Operator):
    """Make a choreographed crowd standing on the active object (a plane you shaped): people in small loose groups, facing the Tower if one is picked, else the plane's +Y"""
    bl_idname = "bbcrowd.choreo_scatter"
    bl_label = "Scatter Crowd on Plane"
    bl_options = {'REGISTER', 'UNDO'}

    count: bpy.props.IntProperty(name="People", default=150, min=1, soft_max=3000,
                                 description="About how many people (fewer if no more fit)")
    spacing: bpy.props.FloatProperty(name="Spacing (m)", default=0.6, min=0.4, soft_max=3.0,
                                     description="Nobody stands closer than this to anybody else")
    clump: bpy.props.IntProperty(name="Group size", default=3, min=1, max=8,
                                 description="People stand in loose groups of 1 to this many. 1 = everybody on their own")
    seed: bpy.props.IntProperty(name="Shuffle", default=1, min=0, description="Another number, another arrangement")
    keep_off: bpy.props.BoolProperty(name="Keep off the characters", default=True,
                                     description="Leave the spots free where the staging's characters and props stand on this frame")

    @classmethod
    def poll(cls, context):
        ob = context.active_object
        return (ob is not None and ob.type == 'MESH' and context.mode == 'OBJECT'
                and not ob.get(CH_TAG) and not ob.get(CUE_TAG) and not ob.get(MIRROR_KEY))

    def execute(self, context):
        from mathutils.bvhtree import BVHTree
        sc = context.scene
        plane = context.active_object
        me = plane.data
        if not len(me.polygons):
            self.report({'ERROR'}, f"{plane.name} has no surface to stand on: pick a plane")
            return {'CANCELLED'}
        loc, rot, _scale = plane.matrix_world.decompose()
        world = Matrix.LocRotScale(loc, rot, None)          # the crowd takes the plane's place, never its scale
        to_crowd = world.inverted() @ plane.matrix_world
        verts = [to_crowd @ v.co for v in me.vertices]
        tree = BVHTree.FromPolygons(verts, [tuple(p.vertices) for p in me.polygons])
        top = max(v.z for v in verts) + 1.0
        down = Vector((0.0, 0.0, -1.0))

        def height(x, y):
            hit = tree.ray_cast(Vector((x, y, top)), down)
            return hit[0].z if hit[0] is not None else None

        keep = choreo_keep_clear(sc, world) if self.keep_off else []
        bounds = (min(v.x for v in verts), min(v.y for v in verts), max(v.x for v in verts), max(v.y for v in verts))
        spots = choreo_scatter(lambda x, y: height(x, y) is not None, bounds, self.count, self.spacing, self.clump, self.seed, keep)
        if not spots:
            self.report({'ERROR'}, f"Nobody fits on {plane.name}")
            return {'CANCELLED'}
        homes = [(x, y, height(x, y) or 0.0) for x, y in spots]
        tower = sc.bb_crowd_tower
        look = None
        if tower is not None:
            t = world.inverted() @ tower.matrix_world.translation
            look = (t.x, t.y)
        k = len(choreo_crowds(sc)) + 1
        while bpy.data.objects.get(f"Crowd {k:02d}") is not None:
            k += 1
        crowd = choreo_make(sc, f"Crowd {k:02d}", homes, look, world=world)
        sc.bb_crowd_choreo = crowd
        note = "" if len(homes) >= self.count else f" (only {len(homes)} of {self.count} fit)"
        self.report({'INFO'}, f"{crowd.name}: {len(homes)} people on {plane.name}{note}")
        return {'FINISHED'}


def _p_seconds(default, name="Takes (seconds)"):
    return bpy.props.FloatProperty(name=name, default=default, min=0.04, soft_max=20.0, step=10, precision=1,
                                   description="How long the reaction takes to go through the crowd, starting on the current frame")


def _p_width(default):
    return bpy.props.FloatProperty(name="Wave ↔ Together", default=default, min=0.02, max=1.0, subtype='FACTOR',
                                   description="Low: the reaction travels through the crowd like a wave. High: everybody moves together")


def _p_snap(default):
    return bpy.props.FloatProperty(name="Snap", default=default, min=1.0, max=5.0,
                                   description="How sudden each person's move is. 1 = even, 2 = quick start and soft settle, 3 and up = a startle")


def _p_seed():
    return bpy.props.IntProperty(name="Shuffle", default=0, min=0, description="Another number, another pick of who does what")


class _NewCue:
    """Shared by the New Cue operators: the active object, where it is on this frame, is what the crowd reacts to."""
    bl_options = {'REGISTER', 'UNDO'}
    kind = 'HAND'

    @classmethod
    def poll(cls, context):
        return active_choreo(context) is not None

    def numbers(self):
        return {}

    def execute(self, context):
        crowd = working_choreo(context)
        try:
            cue, n = choreo_new_cue(context, crowd, self.kind, seconds=self.seconds, width=getattr(self, "width", 0.4),
                                    snap=self.snap, **self.numbers())
        except CueError as e:
            self.report({'ERROR'}, str(e))
            return {'CANCELLED'}
        if self.kind == 'HAND':
            self.report({'INFO'}, f"'{cue.name}' is empty: press Edit Positions to place people")
        elif self.kind == 'WAY':
            self.report({'INFO'}, f"'{cue.name}': {n} people make way, frames {cue.win_a}–{cue.win_b}")
        else:
            self.report({'INFO'}, f"'{cue.name}': {n} people react from frame {context.scene.frame_current}")
        return {'FINISHED'}


class BBCROWD_OT_cue_look(_NewCue, bpy.types.Operator):
    """The crowd turns to look at the active object, where it is on this frame. The nearest turn first"""
    bl_idname = "bbcrowd.cue_look"
    bl_label = "Look at"
    kind = 'LOOK'
    radius: bpy.props.FloatProperty(name="Within (m)", default=12.0, min=0.5, soft_max=80.0, description="People this close turn to look")
    share: bpy.props.FloatProperty(name="How many", default=0.7, min=0.0, max=1.0, subtype='FACTOR', description="The share of those people that looks")
    near_bias: bpy.props.BoolProperty(name="Nearly everybody close by", default=True,
                                      description="Close to it nearly everybody looks; far away only the share above")
    seed: _p_seed()
    seconds: _p_seconds(1.5)
    width: _p_width(0.4)
    snap: _p_snap(2.0)

    def numbers(self):
        return dict(radius=self.radius, share=self.share, near_bias=self.near_bias, seed=self.seed)


class BBCROWD_OT_cue_room(_NewCue, bpy.types.Operator):
    """The crowd steps back to leave a clear space around the active object, where it is on this frame. Nobody turns their back; the nearest step first"""
    bl_idname = "bbcrowd.cue_room"
    bl_label = "Make room around"
    kind = 'ROOM'
    radius: bpy.props.FloatProperty(name="Clear space (m)", default=2.0, min=0.3, soft_max=20.0, description="Nobody stays closer than this")
    seed: _p_seed()
    seconds: _p_seconds(1.2)
    width: _p_width(0.5)
    snap: _p_snap(2.0)

    def numbers(self):
        return dict(radius=self.radius, seed=self.seed)


class BBCROWD_OT_cue_back(_NewCue, bpy.types.Operator):
    """The crowd recoils from the active object, where it is on this frame: the closer, the bigger the step. Some duck, some cheer"""
    bl_idname = "bbcrowd.cue_back"
    bl_label = "Step back from"
    kind = 'BACK'
    reach: bpy.props.FloatProperty(name="Within (m)", default=6.0, min=0.5, soft_max=60.0, description="People this close react")
    amount: bpy.props.FloatProperty(name="Step (m)", default=1.0, min=0.0, soft_max=5.0, description="How far the nearest people step back; less further away")
    share: bpy.props.FloatProperty(name="How many", default=1.0, min=0.0, max=1.0, subtype='FACTOR', description="The share of those people that reacts; the rest stand firm")
    duck: bpy.props.FloatProperty(name="Frightened", default=0.25, min=0.0, max=1.0, subtype='FACTOR', description="The share that shrinks")
    cheer: bpy.props.FloatProperty(name="Excited", default=0.2, min=0.0, max=1.0, subtype='FACTOR', description="The share that bounces")
    face_away: bpy.props.FloatProperty(name="Turn away", default=0.0, min=0.0, max=1.0, subtype='FACTOR', description="The share that also turns their back")
    seed: _p_seed()
    seconds: _p_seconds(1.0)
    width: _p_width(0.3)
    snap: _p_snap(3.0)

    def numbers(self):
        return dict(reach=self.reach, amount=self.amount, share=self.share, duck=self.duck, cheer=self.cheer,
                    face_away=self.face_away, seed=self.seed)


class BBCROWD_OT_cue_way(_NewCue, bpy.types.Operator):
    """The crowd makes way for the active object's walk: people step aside just ahead of it and close in behind. In a staging: the walk into the beat the playhead is on; elsewhere: the seconds after the playhead"""
    bl_idname = "bbcrowd.cue_way"
    bl_label = "Make way for"
    kind = 'WAY'
    reach: bpy.props.FloatProperty(name="Within (m)", default=0.9, min=0.3, soft_max=5.0, description="People this close to the walker's line step aside")
    amount: bpy.props.FloatProperty(name="Sidestep (m)", default=0.35, min=0.0, soft_max=2.0, description="How far they step aside (more when needed to let the walker through)")
    look: bpy.props.FloatProperty(name="Watch the walker", default=0.5, min=0.0, max=1.0, subtype='FACTOR', description="The share that turns to the walker")
    seed: _p_seed()
    seconds: _p_seconds(4.0, "Walk lasts (seconds)")
    snap: _p_snap(2.0)

    def numbers(self):
        return dict(reach=self.reach, amount=self.amount, look=self.look, seed=self.seed)


class BBCROWD_OT_cue_lane(_NewCue, bpy.types.Operator):
    """The crowd clears a straight lane between the two selected objects, opening from the first toward the second (the active one)"""
    bl_idname = "bbcrowd.cue_lane"
    bl_label = "Open a lane"
    kind = 'LANE'
    half_width: bpy.props.FloatProperty(name="Half width (m)", default=1.4, min=0.3, soft_max=10.0, description="Clear space on each side of the line")
    seed: _p_seed()
    seconds: _p_seconds(3.0)
    width: _p_width(0.3)
    snap: _p_snap(2.0)

    def numbers(self):
        return dict(half_width=self.half_width, seed=self.seed)


class BBCROWD_OT_cue_mood(_NewCue, bpy.types.Operator):
    """People around the active object get excited and bounce on the spot (or, with a mood below 0, get frightened and shrink). Nobody moves"""
    bl_idname = "bbcrowd.cue_mood"
    bl_label = "Cheer"
    kind = 'MOOD'
    radius: bpy.props.FloatProperty(name="Within (m)", default=8.0, min=0.5, soft_max=80.0, description="People this close can react")
    mood: bpy.props.FloatProperty(name="Mood", default=1.0, min=-1.0, max=1.0, description="+1 excited: they bounce. -1 frightened: they shrink")
    share: bpy.props.FloatProperty(name="How many", default=0.6, min=0.0, max=1.0, subtype='FACTOR', description="The share of those people that reacts")
    seed: _p_seed()
    seconds: _p_seconds(2.0)
    width: _p_width(0.5)
    snap: _p_snap(2.0)

    def numbers(self):
        return dict(radius=self.radius, mood=self.mood, share=self.share, seed=self.seed)


class BBCROWD_OT_cue_hand(_NewCue, bpy.types.Operator):
    """An empty reaction: press Edit Positions and move the people yourself"""
    bl_idname = "bbcrowd.cue_hand"
    bl_label = "By hand"
    kind = 'HAND'
    seconds: _p_seconds(1.0)
    width: _p_width(0.4)
    snap: _p_snap(2.0)


class _ActiveCue:
    """Shared by the operators that work on the reaction picked in the list."""
    bl_options = {'REGISTER', 'UNDO'}

    @classmethod
    def poll(cls, context):
        crowd = active_choreo(context)
        return crowd is not None and _active_cue(crowd) is not None


def _cue_ramp(scene, crowd, cue, which, seconds):
    """Play From Here / Back From Here: the slider goes 0 -> 1 from the current frame; its old keys go."""
    f = scene.frame_current
    n = max(1, round(seconds * _fps(scene)))
    name = cue.name
    choreo_clear_keys(crowd, name, which=(which,))
    keys = [(f, 0.0), (f + n, 1.0)]
    cue = choreo_cue(crowd, name)
    choreo_key(crowd, name, rise=keys if which == 'PLAY' else (), back=keys if which == 'BACK' else (), ease=_cue_ease(cue))
    return f, f + n


class BBCROWD_OT_cue_play_here(_ActiveCue, bpy.types.Operator):
    """This reaction starts on the current frame: Play goes from 0 to 1 over the seconds beside the button. The timing it had is replaced"""
    bl_idname = "bbcrowd.cue_play_here"
    bl_label = "Play From Here"
    seconds: bpy.props.FloatProperty(name="Seconds", default=0.0, min=0.0, soft_max=20.0, description="0 = the seconds set on the reaction")

    def execute(self, context):
        crowd = working_choreo(context)
        cue = _active_cue(crowd)
        a, b = _cue_ramp(context.scene, crowd, cue, 'PLAY', self.seconds or cue.seconds)
        self.report({'INFO'}, f"'{cue.name}' plays over frames {a}–{b}")
        return {'FINISHED'}


class BBCROWD_OT_cue_back_here(_ActiveCue, bpy.types.Operator):
    """The people of this reaction go back to where they stood, starting on the current frame, over the seconds beside the button. The return it had is replaced"""
    bl_idname = "bbcrowd.cue_back_here"
    bl_label = "Back From Here"
    seconds: bpy.props.FloatProperty(name="Seconds", default=0.0, min=0.0, soft_max=20.0, description="0 = the seconds set on the reaction")

    def execute(self, context):
        crowd = working_choreo(context)
        cue = _active_cue(crowd)
        a, b = _cue_ramp(context.scene, crowd, cue, 'BACK', self.seconds or cue.seconds)
        self.report({'INFO'}, f"'{cue.name}' goes back over frames {a}–{b}")
        return {'FINISHED'}


class BBCROWD_OT_cue_clear_timing(_ActiveCue, bpy.types.Operator):
    """Remove when this reaction plays and goes back: it stays in the list, at rest, until you time it again"""
    bl_idname = "bbcrowd.cue_clear_timing"
    bl_label = "Clear Timing"

    def execute(self, context):
        crowd = working_choreo(context)
        choreo_clear_keys(crowd, _active_cue(crowd).name)
        return {'FINISHED'}


class BBCROWD_OT_cue_update(_ActiveCue, bpy.types.Operator):
    """Work this reaction out again from what it reacts to and the numbers above (after a number was changed or the character was moved). Anything placed by hand in it is replaced; its timing stays (Make way for: the timing follows the walk)"""
    bl_idname = "bbcrowd.cue_update"
    bl_label = "Update From Source"
    here: bpy.props.BoolProperty(name="Where it is on this frame", default=False,
                                 description="Read the source on the current frame instead of the frame the reaction was made on "
                                             "(Make way for: the walk the playhead is in now, and its timing follows)")

    def execute(self, context):
        sc = context.scene
        crowd = working_choreo(context)
        cue = _active_cue(crowd)
        name = cue.name
        try:
            if self.here and cue.kind == 'WAY':
                cue.win_a, cue.win_b = _walk_window(sc, sc.frame_current, cue.seconds)
            n = choreo_update_cue(sc, crowd, cue, frame=sc.frame_current if self.here else None)
        except CueError as e:
            self.report({'ERROR'}, str(e))
            return {'CANCELLED'}
        cue = choreo_cue(crowd, name)
        if cue.kind == 'WAY' and (cue.win_a, cue.win_b) != (cue.key_a, cue.key_b):
            _way_timing(sc, crowd, cue)         # another walk: the parting follows it
            self.report({'INFO'}, f"'{name}': {n} people make way, frames {cue.win_a}–{cue.win_b}")
        else:
            self.report({'INFO'}, f"'{name}': {n} people react")
        return {'FINISHED'}


class BBCROWD_OT_cue_edit(_ActiveCue, bpy.types.Operator):
    """Place people by hand in this reaction. Everybody is shown where they stand when it is fully played, as a short line each: move it (G) to move the person, turn it (R) to turn them. Press Done when finished"""
    bl_idname = "bbcrowd.cue_edit"
    bl_label = "Edit Positions"

    @classmethod
    def poll(cls, context):
        crowd = active_choreo(context)
        return crowd is not None and (_active_cue(crowd) is not None or choreo_editing(crowd) is not None)

    def execute(self, context):
        crowd = working_choreo(context)
        editing = choreo_editing(crowd)
        try:
            if editing is not None:
                joined = choreo_edit_end(context, crowd, editing)
                if joined < 0:
                    self.report({'WARNING'}, f"'{editing.name}' no longer matches the crowd (people were added or deleted in it)")
                elif joined:
                    self.report({'INFO'}, f"{joined} more people take part in '{editing.name}'")
            else:
                choreo_edit_begin(context, crowd, _active_cue(crowd))
        except CueError as e:
            self.report({'ERROR'}, str(e))
            return {'CANCELLED'}
        return {'FINISHED'}


class BBCROWD_OT_cue_remove(_ActiveCue, bpy.types.Operator):
    """Delete this reaction and its timing. The other reactions play exactly as before"""
    bl_idname = "bbcrowd.cue_remove"
    bl_label = "Delete Reaction"

    def execute(self, context):
        crowd = working_choreo(context)
        cue = _active_cue(crowd)
        editing = choreo_editing(crowd)
        if editing is not None and editing.uid == cue.uid:
            choreo_edit_end(context, crowd, editing)
            cue = _active_cue(crowd)
        choreo_remove_cue(crowd, cue.name)
        return {'FINISHED'}


class BBCROWD_OT_cue_move(_ActiveCue, bpy.types.Operator):
    """Move this reaction up or down the list (the order is only for you: reactions add up whatever their order)"""
    bl_idname = "bbcrowd.cue_move"
    bl_label = "Move Reaction"
    direction: bpy.props.EnumProperty(items=[('UP', "Up", ""), ('DOWN', "Down", "")], default='UP')

    def execute(self, context):
        crowd = working_choreo(context)
        cues = crowd.bb_crowd_cues
        i = crowd.bb_crowd_cue_index
        j = i - 1 if self.direction == 'UP' else i + 1
        if not (0 <= i < len(cues)) or not (0 <= j < len(cues)):
            return {'CANCELLED'}
        cues.move(i, j)
        crowd.bb_crowd_cue_index = j
        choreo_sync(crowd)
        return {'FINISHED'}


# ------------------------------------------------------------------ panels (one tab, four panels)
class _CrowdPanel:
    bl_space_type = 'VIEW_3D'
    bl_region_type = 'UI'
    bl_category = "BB Crowd"


class BBSTCROWD_PT_controllers(_CrowdPanel, bpy.types.Panel):
    """Named BBST… so BB Stage keeps this tab in Stage Mode (it hides every other sidebar tab there)."""
    bl_label = "Controllers"
    bl_order = 1

    def draw(self, context):
        lay = self.layout
        sc = context.scene
        zone = active_zone(context)
        m = crowd_mod(zone)
        col = lay.column(align=True)
        col.prop(sc, "bb_crowd_tower", text="Tower")
        col.operator("bbcrowd.add_zone", icon='ADD')
        zs = zones(sc)
        if len(zs) > 1:
            for z in zs:
                col.operator("bbcrowd.pick", text=z.name, icon='RADIOBUT_ON' if z == zone else 'RADIOBUT_OFF', depress=(z == zone)).name = z.name
        if m is None:
            lay.label(text="Add a controller to start", icon='INFO')
            return
        if GROUP_MARK not in m.node_group.interface.items_tree:
            lay.label(text="Older controller: press Sync Influencers", icon='ERROR')
            return
        try:
            n = member_count(context, zone)
        except Exception:
            n = -1
        lay.separator()
        lay.label(text=f"{zone.name}: {n} members" if n >= 0 else zone.name, icon='COMMUNITY')
        r = lay.row(align=True)
        r.operator("bbcrowd.reset", icon='LOOP_BACK')
        r.operator("bbcrowd.bake", icon='FREEZE')
        box = lay.box()
        box.label(text="Birth (needs Reset)", icon='STICKY_UVS_DISABLE')
        for nm in ("Spacing", "Density", "Seed"):
            box.prop(sock_of(m, nm), "value", text=nm)
        box = lay.box()
        box.label(text="Walking", icon='MOD_DYNAMICPAINT')
        for nm in ("Walk speed", "Run speed", "Reaction", "Personal space"):
            box.prop(sock_of(m, nm), "value", text=nm)
        box = lay.box()
        box.label(text="Idle", icon='FORCE_TURBULENCE')
        for nm in ("Idle amount", "Idle speed", "Idle turn"):
            box.prop(sock_of(m, nm), "value", text=nm)
        box = lay.box()
        box.label(text="Tower and panic (key per beat)", icon='ACTION')
        box.prop(sock_of(m, "Tower"), "value", text="Tower")
        for nm in ("Panic", "Flee distance", "Veterans"):
            r = box.row(align=True)
            r.prop(sock_of(m, nm), "value", text=nm)
            r.operator("bbcrowd.key", text="", icon='KEYFRAME').name = nm
        box = lay.box()
        box.label(text="Look", icon='MATERIAL')
        mat = peg_material_for(zone)
        r = box.row(align=True)
        r.prop(mat, "diffuse_color", text="Member colour")
        box.prop(sock_of(m, "Peg height"), "value", text="Peg height")
        box.prop(sock_of(m, "Show controller"), "value", text="Show controller plane")
        box = lay.box()
        box.label(text="Camera (the cut camera's foreground)", icon='VIEW_CAMERA')
        for nm in ("Lens clearance", "Lens reach"):
            r = box.row(align=True)
            r.prop(sock_of(m, nm), "value", text=nm)
            r.operator("bbcrowd.key", text="", icon='KEYFRAME').name = nm


class BBSTCROWD_PT_influencers(_CrowdPanel, bpy.types.Panel):
    bl_label = "Influencers"
    bl_order = 2

    def draw(self, context):
        lay = self.layout
        sc = context.scene
        lay.label(text="Fields carried by the characters", icon='FORCE_MAGNETIC')
        r = lay.row(align=True)
        r.operator("bbcrowd.influence", text="Add Selected", icon='RESTRICT_SELECT_OFF').source = 'SELECTED'
        r.operator("bbcrowd.influence", text="From BB Stage", icon='ARMATURE_DATA').source = 'STAGE'
        lay.operator("bbcrowd.sync", icon='FILE_REFRESH')
        infl = influencers(sc)
        if not infl:
            lay.label(text="None yet.", icon='INFO')
            lay.label(text="Gaze: + look at it, − look away.")
            lay.label(text="Move: − step aside for it, + drift toward it.")
            return
        for ob in infl:
            s = ob.bb_crowd
            box = lay.box()
            r = box.row(align=True)
            r.label(text=ob.name, icon='OUTLINER_OB_EMPTY' if ob.type == 'EMPTY' else 'OUTLINER_OB_MESH')
            r.operator("bbcrowd.uninfluence", text="", icon='X').name = ob.name
            col = box.column(align=True)
            r = col.row(align=True)
            r.prop(s, "gaze", text="Gaze")
            r.prop(s, "gaze_radius", text="reach")
            r = col.row(align=True)
            r.prop(s, "move", text="Move")
            r.prop(s, "radius", text="radius")


class BBSTCROWD_PT_tests(_CrowdPanel, bpy.types.Panel):
    bl_label = "Tests"
    bl_order = 3
    bl_options = {'DEFAULT_CLOSED'}

    def draw(self, context):
        lay = self.layout
        lay.label(text="240 frames, keys the inputs and two test drivers", icon='PLAY')
        r = lay.row(align=True)
        for k, t in (('SWIVEL', "Swivel"), ('WALK', "Walk"), ('PANIC', "Panic"), ('ALL', "All")):
            r.operator("bbcrowd.test", text=t).kind = k
        lay.operator("bbcrowd.clear_keys", icon='X')


class BBSTCROWD_UL_cues(bpy.types.UIList):
    """The reactions of the crowd: the name (double-click to rename), then Play and Back, which key like any field"""

    def draw_item(self, context, layout, data, item, icon, active_data, active_propname, index):
        play, back = cue_sliders(data, item)
        split = layout.split(factor=0.4, align=True)
        split.prop(item, "name", text="", emboss=False, icon=CUE_ICON.get(item.kind, 'DOT'))
        row = split.row(align=True)
        if play is None or back is None:
            row.label(text="not ready", icon='ERROR')
            return
        row.prop(play, "value", text="Play", slider=True)
        row.prop(back, "value", text="Back", slider=True)


class BBSTCROWD_MT_new_cue(bpy.types.Menu):
    """A new reaction to what is selected, starting on the current frame"""
    bl_label = "New Cue"

    def draw(self, context):
        lay = self.layout
        for kind, idname in (('LOOK', "bbcrowd.cue_look"), ('ROOM', "bbcrowd.cue_room"), ('BACK', "bbcrowd.cue_back"),
                             ('WAY', "bbcrowd.cue_way"), ('LANE', "bbcrowd.cue_lane"), ('MOOD', "bbcrowd.cue_mood")):
            lay.operator(idname, text=CUE_LABEL[kind], icon=CUE_ICON[kind])
        lay.separator()
        lay.operator("bbcrowd.cue_hand", text=CUE_LABEL['HAND'], icon=CUE_ICON['HAND'])


class BBSTCROWD_PT_choreo(_CrowdPanel, bpy.types.Panel):
    """Named BBST… so BB Stage keeps this tab in Stage Mode. Choreographed crowds: every reaction is a cue."""
    bl_label = "Crowd choreography"
    bl_order = 0

    def draw(self, context):
        lay = self.layout
        sc = context.scene
        crowd = active_choreo(context)
        col = lay.column(align=True)
        if crowd is not None:
            col.prop(sc, "bb_crowd_choreo", text="Crowd")
        col.operator("bbcrowd.choreo_convert", icon='MOD_PARTICLE_INSTANCE')
        col.operator("bbcrowd.choreo_scatter", icon='OUTLINER_OB_POINTCLOUD')
        m = choreo_mod(crowd)
        if m is None or m.node_group is None:
            lay.label(text="Make a crowd to start", icon='INFO')
            return
        lay.label(text=f"{crowd.name}: {choreo_members(crowd)} people", icon='COMMUNITY')
        if not len(crowd.bb_crowd_cues) and any(ch.get(CUE_TAG) for ch in crowd.children):
            # built by the crowd_choreo.py script: its reactions are listed (keys and all) by the first sync
            lay.operator("bbcrowd.sync", text="List This Crowd's Reactions", icon='FILE_REFRESH')
        editing = choreo_editing(crowd)
        lay.menu("BBSTCROWD_MT_new_cue", text="New Cue", icon='ADD')
        row = lay.row()
        row.template_list("BBSTCROWD_UL_cues", "", crowd, "bb_crowd_cues", crowd, "bb_crowd_cue_index", rows=4)
        side = row.column(align=True)
        side.operator("bbcrowd.cue_remove", text="", icon='REMOVE')
        side.separator()
        side.operator("bbcrowd.cue_move", text="", icon='TRIA_UP').direction = 'UP'
        side.operator("bbcrowd.cue_move", text="", icon='TRIA_DOWN').direction = 'DOWN'
        cue = _active_cue(crowd)
        if cue is not None:
            box = lay.box()
            box.label(text=f"{cue.name} · {CUE_LABEL.get(cue.kind, '')}", icon=CUE_ICON.get(cue.kind, 'DOT'))
            if cue.obj is None or len(cue.obj.data.vertices) != len(crowd.data.vertices):
                box.label(text="No longer matches the crowd: delete it", icon='ERROR')
            box.prop(cue, "seconds", text="Seconds")
            r = box.row(align=True)
            r.operator("bbcrowd.cue_play_here", icon='PLAY')
            r.operator("bbcrowd.cue_back_here", icon='LOOP_BACK')
            box.operator("bbcrowd.cue_clear_timing", icon='X')
            c2 = box.column(align=True)
            c2.prop(cue, "width", slider=True)
            c2.prop(cue, "snap", slider=True)
            r = box.row(align=True)
            if editing is not None:
                r.alert = True
                r.operator("bbcrowd.cue_edit", text=f"Done ({editing.name})", icon='CHECKMARK', depress=True)
            else:
                r.operator("bbcrowd.cue_edit", text="Edit Positions", icon='EDITMODE_HLT')
            if cue.kind in CUE_NUMBERS:
                # what the reaction was made from: change a number or the source, then Update From Source
                # (the same numbers as in the box Blender shows after New Cue, which BB Stage hides in Stage Mode)
                sub = box.box()
                sub.enabled = editing is None
                c3 = sub.column(align=True)
                c3.prop(cue, "source", text="Lane starts at" if cue.kind == 'LANE' else "Reacts to")
                if cue.kind == 'LANE':
                    c3.prop(cue, "source_b", text="Lane ends at")
                if cue.kind == 'WAY':
                    r = c3.row(align=True)
                    r.prop(cue, "win_a", text="Walk from")
                    r.prop(cue, "win_b", text="to")
                else:
                    c3.prop(cue, "frame", text="On frame")
                c3 = sub.column(align=True)
                for prop, text in CUE_NUMBERS[cue.kind]:
                    c3.prop(cue, prop, text=text)
                sub.operator("bbcrowd.cue_update", icon='FILE_REFRESH')
        elif editing is not None:
            r = lay.row()
            r.alert = True
            r.operator("bbcrowd.cue_edit", text=f"Done ({editing.name})", icon='CHECKMARK', depress=True)
        box = lay.box()
        box.label(text="Members", icon='OUTLINER_OB_ARMATURE')
        for nm, text in (("Peg height", "Height"), ("Height variation", "Height variation"), ("Idle turn", "Head wander"),
                         ("Bob height", "Bounce height"), ("Bob rate", "Bounce rate")):
            s = ch_sock(crowd, nm)
            if s is not None:
                box.prop(s, "value", text=text)
        mat = ch_sock(crowd, "Peg material")
        if mat is not None and mat.value is not None:
            box.prop(mat.value, "diffuse_color", text="Colour")
        box = lay.box()
        box.label(text="Cameras", icon='VIEW_CAMERA')
        for nm in ("Lens clearance", "Lens reach", "Keep off"):
            s = ch_sock(crowd, nm)
            if s is not None:
                box.prop(s, "value", text=nm)


CLASSES = (BBCrowdInfluencer, BBCrowdCue, BBCROWD_OT_add_zone, BBCROWD_OT_key, BBCROWD_OT_reset, BBCROWD_OT_bake,
           BBCROWD_OT_influence, BBCROWD_OT_uninfluence, BBCROWD_OT_sync, BBCROWD_OT_clear_keys, BBCROWD_OT_test,
           BBCROWD_OT_pick,
           BBCROWD_OT_choreo_convert, BBCROWD_OT_choreo_scatter, BBCROWD_OT_cue_look, BBCROWD_OT_cue_room,
           BBCROWD_OT_cue_back, BBCROWD_OT_cue_way, BBCROWD_OT_cue_lane, BBCROWD_OT_cue_mood, BBCROWD_OT_cue_hand,
           BBCROWD_OT_cue_play_here, BBCROWD_OT_cue_back_here, BBCROWD_OT_cue_clear_timing, BBCROWD_OT_cue_update,
           BBCROWD_OT_cue_edit, BBCROWD_OT_cue_remove, BBCROWD_OT_cue_move,
           BBSTCROWD_UL_cues, BBSTCROWD_MT_new_cue,
           BBSTCROWD_PT_choreo, BBSTCROWD_PT_controllers, BBSTCROWD_PT_influencers, BBSTCROWD_PT_tests)
# (owner, name) of everything register() adds to Blender's own types
PROPS = ((bpy.types.Object, "bb_crowd"), (bpy.types.Scene, "bb_crowd_obj"), (bpy.types.Scene, "bb_crowd_tower"),
         (bpy.types.Object, "bb_crowd_cues"), (bpy.types.Object, "bb_crowd_cue_index"), (bpy.types.Scene, "bb_crowd_choreo"))


def register():
    unregister()                                   # registering twice (a reload) starts clean instead of raising
    for stale in ("BBSTCROWD_PT_panel",):          # panels of older versions
        prev = getattr(bpy.types, stale, None)
        if prev is not None:
            try:
                bpy.utils.unregister_class(prev)
            except (RuntimeError, ValueError):
                pass
    for c in CLASSES:
        prev = getattr(bpy.types, c.__name__, None)     # the same class from another copy of this add-on
        if prev is not None:
            try:
                bpy.utils.unregister_class(prev)
            except (RuntimeError, ValueError):
                pass
        bpy.utils.register_class(c)
    bpy.types.Object.bb_crowd = bpy.props.PointerProperty(type=BBCrowdInfluencer)
    bpy.types.Scene.bb_crowd_obj = bpy.props.PointerProperty(type=bpy.types.Object, name="Crowd controller", poll=_zone_poll)
    bpy.types.Scene.bb_crowd_tower = bpy.props.PointerProperty(type=bpy.types.Object, name="Tower",
                                                               description="What the crowd watches: Add Crowd Controller turns the plane toward it, "
                                                                           "Scatter Crowd on Plane makes everybody face it")
    bpy.types.Object.bb_crowd_cues = bpy.props.CollectionProperty(type=BBCrowdCue, name="Reactions")
    bpy.types.Object.bb_crowd_cue_index = bpy.props.IntProperty(name="Reaction", default=0, min=0,
                                                                description="The reaction the buttons below work on")
    bpy.types.Scene.bb_crowd_choreo = bpy.props.PointerProperty(type=bpy.types.Object, name="Crowd", poll=_choreo_poll,
                                                                description="The choreographed crowd this panel works on")


def unregister():
    for owner, p in PROPS:                         # first: nothing may still point at the classes below
        if hasattr(owner, p):
            delattr(owner, p)
    for c in reversed(CLASSES):
        if getattr(c, "is_registered", False):
            try:
                bpy.utils.unregister_class(c)
            except (RuntimeError, ValueError):
                pass


if __name__ == "__main__":
    register()
