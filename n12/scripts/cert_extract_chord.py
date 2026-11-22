#!/usr/bin/env python3
"""Extract the historical chord stages (Compact/Preservation/Chords/C*StepNN.lean),
the 192 chord radii (Preservation/Chords/Radii.lean) and the 108 C713 height
records (Cases/C713/HeightData/Batch*.lean) into n12/data/cert/.  Untrusted: every
item is re-checked in HOL (n12/cert/CH_*.ml).

Outputs (n12/data/cert/):
  chord_radii.txt    k Bnum Bden rnum rden            (Lean radiusK = <sumUpper, radius>,
                                                      radiusK_checked : radiusK.Check angle K)
  chord_stages.txt   case step hz lonum loden hinum hiden srcDom tgtDom n1Dom n2Dom n3Dom m0,m1,m2,m3 nplans nnbrs
  chord_plans/C<case>_S<step>.txt  one record per line:
     N <coll> <src> <k> <lowRow> <highRow> | <hint>;<hint>;...
         neighbour of collection coll (0,1,2), radius index k; lowRow/highRow are
         Neighbor.bounds = [lower(hi-r) false, upper(lo+r) false] (rows x,y,c,s)
     P <src> <k> <lowCut> <highCut> | <branch> | <branch>
         lowCut = AxisSection.upper(lo-r) true, highCut = AxisSection.lower(hi+r) true
         branch: K <tgt> : <hint>;...     (chord_keep)
                 C <i>,<j>,... : <w>@<i>,...  (chord_close, EmptyContext.Witness)
  c713_height.txt    i src cutx,cuty,cutc,cuts tgt|- Bnum Bden rnum rden k
         (k = radius index whose radius equals the record's radius, or -1)
Rows are computed with Lean's CoordinateBound on reduced rationals (Fraction = Lean ℚ).
hint: k (constant) | c<i> (copy) | s<i> (single) | p<i>.<j> (pair)
"""
import os, re, glob
from fractions import Fraction as Q

ROOT = "n12/ext/jatloe/Lean/Proofs/N12-jatloe/Compact"
OUT = "n12/data/cert"


def enc_rh(t):
    t = t.strip()
    if t == ".constant":
        return "k"
    m = re.match(r"^\.copy (\d+)$", t)
    if m:
        return "c" + m.group(1)
    m = re.match(r"^\.single (\d+)$", t)
    if m:
        return "s" + m.group(1)
    m = re.match(r"^\.pair (\d+) (\d+)$", t)
    if m:
        return "p%s.%s" % m.groups()
    raise ValueError(t)


def enc_hint_list(s):
    s = s.strip()
    assert s.startswith("[") and s.endswith("]"), s
    inner = s[1:-1].strip()
    if not inner:
        return ""
    return ";".join(enc_rh(x) for x in inner.split(","))


def qparse(s):
    s = s.strip().strip("()")
    if "/" in s:
        a, b = s.split("/")
        return Q(int(a), int(b))
    return Q(int(s))


# Lean CoordinateBound.lower / upper and AxisSection.orient
def lower(hz, b, strict):
    r = (b.denominator, 0, -b.numerator, strict)
    return (r[1], r[0], r[2], r[3]) if hz else r


def upper(hz, b, strict):
    r = (-b.denominator, 0, b.numerator, strict)
    return (r[1], r[0], r[2], r[3]) if hz else r


def enc_row(r):
    return "%d,%d,%d,%d" % (r[0], r[1], r[2], 1 if r[3] else 0)


def split_top(s, sep=","):
    out, depth, cur = [], 0, ""
    for ch in s:
        if ch in "([⟨":
            depth += 1
        elif ch in ")]⟩":
            depth -= 1
        if ch == sep and depth == 0:
            out.append(cur.strip())
            cur = ""
        else:
            cur += ch
    if cur.strip():
        out.append(cur.strip())
    return out


def read_radii():
    t = open(ROOT + "/Preservation/Chords/Radii.lean").read()
    rad = {}
    for m in re.finditer(r"def radius(\d+) : Radius := ⟨\(([-\d/]+)\),\(([-\d/]+)\)⟩", t):
        rad[int(m.group(1))] = (qparse(m.group(2)), qparse(m.group(3)))
    for m in re.finditer(r"theorem radius(\d+)_checked : radius\d+\.Check angle(64|128)_(\d+)", t):
        k = int(m.group(1))
        a = int(m.group(3)) + (0 if m.group(2) == "64" else 64)
        assert a == k, (k, a)
    assert sorted(rad) == list(range(192))
    return rad


def read_domains():
    doms = {}
    for l in open(OUT + "/hist_domains.txt"):
        p = l.split()
        doms[(p[0], p[1])] = [int(x) for x in p[2].split(",")] if len(p) > 2 else []
    return doms


def read_pose_angles():
    ang = {}
    for l in open(OUT + "/hist_poses.txt"):
        p = l.split()
        ang[int(p[0])] = int(p[1])
    return ang


def branch(text, src, ang, tgts):
    text = text.strip()
    m = re.match(r"^chord_close%\(⟨\[([\d,\s]*)\],\[(.*)\]⟩\)$", text)
    if m:
        ins = [int(x) for x in m.group(1).split(",") if x.strip()]
        terms = re.findall(r"\((-?\d+),(\d+)\)", m.group(2))
        return "C %s : %s" % (",".join(map(str, ins)), ",".join("%s@%s" % t for t in terms))
    m = re.match(r"^chord_keep%\((\d+),(\[.*\])\)$", text)
    if m:
        tgt = int(m.group(1))
        assert ang.get(tgt, 0) == ang.get(src, 0)
        tgts.append(tgt)
        return "K %d : %s" % (tgt, enc_hint_list(m.group(2)))
    raise ValueError(text)


def main():
    rad = read_radii()
    doms = read_domains()
    ang = read_pose_angles()
    with open(OUT + "/chord_radii.txt", "w") as f:
        for k in range(192):
            B, r = rad[k]
            f.write("%d %d %d %d %d\n" % (k, B.numerator, B.denominator, r.numerator, r.denominator))
    os.makedirs(OUT + "/chord_plans", exist_ok=True)
    stages = []
    tot_plans = tot_nbrs = tot_close2 = 0
    for fn in sorted(glob.glob(ROOT + "/Preservation/Chords/C*Step*.lean")):
        mm = re.search(r"C(\d+)Step(\d+)\.lean$", fn)
        case, step = mm.groups()
        t = open(fn).read()
        hz = re.search(r"def horizontal : Bool := (true|false)", t).group(1) == "true"
        lo = qparse(re.search(r"def lo : ℚ := (\([-\d/]+\))", t).group(1))
        hi = qparse(re.search(r"def hi : ℚ := (\([-\d/]+\))", t).group(1))
        assert lo <= hi
        recs = []
        coll_ids = {}
        nb = {}
        for m in re.finditer(r"checked_chord_neighbor neighbor(\d+)_(\d+) \(dictionary,horizontal,lo,hi\) := "
                             r"\((\d+),radius(\d+),radius\d+_checked,(\[[^\]]*\])\)", t):
            c, j, src, k, hs = int(m.group(1)), int(m.group(2)), int(m.group(3)), int(m.group(4)), m.group(5)
            assert ang.get(src, 0) == k, (fn, src, k)
            r = rad[k][1]
            nb[(c, j)] = (src, k, lower(hz, hi - r, False), upper(hz, lo + r, False), enc_hint_list(hs))
        for m in re.finditer(r"checked_chord_collection neighbors(\d+) : .*?:= \[(.*?)\]", t, re.S):
            c = int(m.group(1))
            names = [x.strip() for x in m.group(2).split(",") if x.strip()]
            js = []
            for nm in names:
                mm2 = re.match(r"neighbor(\d+)_(\d+)$", nm)
                assert int(mm2.group(1)) == c
                js.append(int(mm2.group(2)))
            coll_ids[c] = js
        assert sorted(coll_ids) == [0, 1, 2]
        ndoms = []
        for c in range(3):
            dm = re.search(r"theorem neighbors%d_sources : neighbors%d\.map Neighbor\.source =\s*"
                           r"continuousScout%sDomain(\d+_\d+)Ids := by rfl" % (c, c, case), t)
            dname = dm.group(1)
            ndoms.append(dname)
            srcs = []
            for j in coll_ids[c]:
                src, k, rl, rh, hs = nb[(c, j)]
                srcs.append(src)
                recs.append("N %d %d %d %s %s | %s" % (c, src, k, enc_row(rl), enc_row(rh), hs))
            assert srcs == doms[(case, dname)], (fn, c)
            tot_nbrs += len(srcs)
        plan = {}
        for line in t.splitlines():
            m = re.match(r"^checked_chord_plan plan(\d+) \(dictionary,horizontal,lo,hi\) := \((.*)\)$", line)
            if not m:
                continue
            parts = split_top(m.group(2))
            assert len(parts) == 5, line
            src, k = int(parts[0]), int(re.match(r"radius(\d+)$", parts[1]).group(1))
            assert ang.get(src, 0) == k
            r = rad[k][1]
            tg = []
            bl = branch(parts[3], src, ang, tg)
            bh = branch(parts[4], src, ang, tg)
            if bl.startswith("C") and bh.startswith("C"):
                tot_close2 += 1
            plan[int(m.group(1))] = (src, tg, "P %d %d %s %s | %s | %s" % (
                src, k, enc_row(upper(hz, lo - r, True)), enc_row(lower(hz, hi + r, True)), bl, bh))
        pm = re.search(r"checked_chord_collection plans : .*?:= \[(.*?)\]", t, re.S)
        order = [int(re.match(r"plan(\d+)$", x.strip()).group(1)) for x in pm.group(1).split(",") if x.strip()]
        sm = re.search(r"theorem plans_sources : plans\.map IndexedChord\.Plan\.source = "
                       r"continuousScout%sDomain(\d+_\d+)Ids := by rfl" % case, t)
        sdom = sm.group(1)
        tm = re.search(r"theorem outputs_included : .*? target ∈ continuousScout%sDomain(\d+_\d+)Ids" % case, t)
        tdom = tm.group(1)
        srcs = [plan[i][0] for i in order]
        assert srcs == doms[(case, sdom)], fn
        outs = re.search(r"def outputIds : List \(Fin poseCount\) := \[([\d,\s]*)\]", t).group(1)
        outs = [int(x) for x in outs.split(",") if x.strip()]
        assert outs == [x for i in order for x in plan[i][1]], fn
        assert all(o in doms[(case, tdom)] for o in outs)
        for i in order:
            recs.append(plan[i][2])
        # sound: incoming / h0 h1 h2 domains
        snd = t.split("theorem sound")[1].split("def masks")[0]
        dd = re.findall(r"OrientedPoseCovered continuousScout%sDomain(\d+_\d+) \(q (\d)\)" % case, snd)
        assert dd == [(sdom, "0"), (ndoms[0], "1"), (ndoms[1], "2"), (ndoms[2], "3"), (tdom, "0")], (fn, dd)
        masks = re.search(r"def masks : Fin 4 → Nat := !\[([\d,]+)\]", t).group(1)
        with open(OUT + "/chord_plans/C%s_S%s.txt" % (case, step), "w") as f:
            f.write("\n".join(recs) + "\n")
        stages.append("%s %s %d %d %d %d %d %s %s %s %s %s %s %d %d" % (
            case, step, 1 if hz else 0, lo.numerator, lo.denominator, hi.numerator, hi.denominator,
            sdom, tdom, ndoms[0], ndoms[1], ndoms[2], masks, len(order),
            sum(len(coll_ids[c]) for c in range(3))))
        tot_plans += len(order)
    with open(OUT + "/chord_stages.txt", "w") as f:
        f.write("\n".join(stages) + "\n")
    # C713 height records
    hrec = {}
    for fn in sorted(glob.glob(ROOT + "/Cases/C713/HeightData/Batch*.lean")):
        t = open(fn).read()
        for m in re.finditer(r"def entry(\d+) : Entry :=\s*⟨⟨(\d+), ⟨(-?\d+),(-?\d+),(-?\d+),(true|false)⟩, "
                             r"(none|some \d+)⟩,\s*⟨\(([-\d/]+)\),\(([-\d/]+)\)⟩⟩", t):
            i = int(m.group(1))
            src = int(m.group(2))
            cut = (int(m.group(3)), int(m.group(4)), int(m.group(5)), m.group(6) == "true")
            tg = m.group(7)
            tgt = "-" if tg == "none" else tg.split()[1]
            B, r = qparse(m.group(8)), qparse(m.group(9))
            k = ang.get(src, 0)
            kk = k if rad[k] == (B, r) else -1
            hrec[i] = "%d %d %s %s %d %d %d %d %d" % (i, src, enc_row(cut), tgt, B.numerator, B.denominator,
                                                     r.numerator, r.denominator, kk)
    assert sorted(hrec) == list(range(108))
    srcs = [int(hrec[i].split()[1]) for i in range(108)]
    assert srcs == doms[("713", "7_0")]
    tg = [int(hrec[i].split()[3]) for i in range(108) if hrec[i].split()[3] != "-"]
    assert tg == doms[("713", "7_6")]
    with open(OUT + "/c713_height.txt", "w") as f:
        f.write("\n".join(hrec[i] for i in range(108)) + "\n")
    print("chord stages", len(stages), "plans", tot_plans, "(two-close", tot_close2, ") neighbours", tot_nbrs,
          "height records", len(hrec), "radius mismatches",
          sum(1 for i in range(108) if hrec[i].split()[-1] == "-1"))


if __name__ == "__main__":
    os.chdir(".")
    main()
