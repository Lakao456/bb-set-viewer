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
"""
import math

import bpy
import bmesh
from mathutils import Matrix, Vector

bl_info = {
    "name": "BB Crowd",
    "author": "Beta Builder",
    "version": (0, 4, 1),
    "blender": (5, 0, 0),
    "location": "View3D > Sidebar > BB Crowd",
    "description": "Procedural crowds for blocking: controllers and character fields",
    "category": "3D View",
}

GROUP = "BB Crowd"
MOD = "BB Crowd"
MIRROR_KEY = "bb_crowd_mirror"        # on the mirror object: the scene it serves
CTRL_KEY = "bb_crowd_controller"      # on controllers
GROUP_MARK = "Peg material"           # an input only this version has: older groups get retired
BUILD_TAG = "bb_crowd_build"          # on the node group: the add-on version that built it (any other → rebuilt)
ZONE_INPUTS = ["Spacing", "Density", "Seed", "Peg height", "Personal space", "Walk speed", "Run speed", "Reaction",
               "Idle amount", "Idle speed", "Idle turn", "Tower", "Panic", "Flee distance", "Veterans", "Influencers",
               "Show controller", "Peg material"]
CROWD_GREY = (0.30, 0.31, 0.34, 1.0)  # default member colour: a mid grey that stays grey under the studio light


def bbstage():
    import sys
    for name, mod in sys.modules.items():
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
    nose.inputs["Depth"].default_value = head_r * 1.1
    nose_t = N("GeometryNodeTransform", "Nose fwd")
    # the cone is centred on its origin: put its base inside the head so the nose stays attached
    nose_t.inputs["Translation"].default_value = (0.0, head_r * 0.85 + head_r * 0.55, body_h + head_r * 1.1)
    nose_t.inputs["Rotation"].default_value = (-math.pi / 2, 0.0, 0.0)
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
    inst = N("GeometryNodeInstanceOnPoints", "Members")
    L(simmed[0], simmed[1], inst, "Points")
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
    ng[BUILD_TAG] = ".".join(str(v) for v in bl_info["version"])
    return ng


def ensure_group():
    ng = bpy.data.node_groups.get(GROUP)
    current = ".".join(str(v) for v in bl_info["version"])
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
            obs = [o for o in context.selected_objects if crowd_mod(o) is None and not o.get(MIRROR_KEY)]
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


# ------------------------------------------------------------------ panels (one tab, three panels)
class _CrowdPanel:
    bl_space_type = 'VIEW_3D'
    bl_region_type = 'UI'
    bl_category = "BB Crowd"


class BBSTCROWD_PT_controllers(_CrowdPanel, bpy.types.Panel):
    """Named BBST… so BB Stage keeps this tab in Stage Mode (it hides every other sidebar tab there)."""
    bl_label = "Controllers"
    bl_order = 0

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


class BBSTCROWD_PT_influencers(_CrowdPanel, bpy.types.Panel):
    bl_label = "Influencers"
    bl_order = 1

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
    bl_order = 2
    bl_options = {'DEFAULT_CLOSED'}

    def draw(self, context):
        lay = self.layout
        lay.label(text="240 frames, keys the inputs and two test drivers", icon='PLAY')
        r = lay.row(align=True)
        for k, t in (('SWIVEL', "Swivel"), ('WALK', "Walk"), ('PANIC', "Panic"), ('ALL', "All")):
            r.operator("bbcrowd.test", text=t).kind = k
        lay.operator("bbcrowd.clear_keys", icon='X')


CLASSES = (BBCrowdInfluencer, BBCROWD_OT_add_zone, BBCROWD_OT_key, BBCROWD_OT_reset, BBCROWD_OT_bake, BBCROWD_OT_influence,
           BBCROWD_OT_uninfluence, BBCROWD_OT_sync, BBCROWD_OT_clear_keys, BBCROWD_OT_test, BBCROWD_OT_pick,
           BBSTCROWD_PT_controllers, BBSTCROWD_PT_influencers, BBSTCROWD_PT_tests)


def register():
    for stale in ("BBSTCROWD_PT_panel",):          # panels of older versions
        prev = getattr(bpy.types, stale, None)
        if prev is not None:
            try:
                bpy.utils.unregister_class(prev)
            except RuntimeError:
                pass
    for c in CLASSES:
        prev = getattr(bpy.types, c.__name__, None)
        if prev is not None:
            try:
                bpy.utils.unregister_class(prev)
            except RuntimeError:
                pass
        bpy.utils.register_class(c)
    bpy.types.Object.bb_crowd = bpy.props.PointerProperty(type=BBCrowdInfluencer)
    bpy.types.Scene.bb_crowd_obj = bpy.props.PointerProperty(type=bpy.types.Object, name="Crowd controller", poll=_zone_poll)
    bpy.types.Scene.bb_crowd_tower = bpy.props.PointerProperty(type=bpy.types.Object, name="Tower",
                                                               description="Used by Add Crowd Controller to turn the plane toward the tower")


def unregister():
    for c in reversed(CLASSES):
        try:
            bpy.utils.unregister_class(c)
        except RuntimeError:
            pass
    for owner, p in ((bpy.types.Object, "bb_crowd"), (bpy.types.Scene, "bb_crowd_obj"), (bpy.types.Scene, "bb_crowd_tower")):
        if hasattr(owner, p):
            delattr(owner, p)


if __name__ == "__main__":
    register()
