#!/usr/bin/env python3
"""Extract the C898 certificate data (Compact/Cases/C898) into n12/data/cert/c898_*.  Untrusted:
everything is re-checked in HOL (n12/cert/C8_*.ml).

Outputs (n12/data/cert/):
  c898_rows.txt     id x y c strict denPred              (SharedRows sparse_rows%)
  c898_poses.txt    id angle r1,r2,...                    (SharedPoses sparse_poses%, angle < 64)
  c898_domains.txt  owner_version id1,id2,...             (SharedDomains continuousScout898Domain*Ids)
  c898_links.txt    i src tgt                             (CompactRelaxation links, 927, in order)
  c898_steps.txt    step S N T npl                        (CachedPairs StepNN, NN = 0..8, 11..14)
  c898_plans/S<NN>.txt
      P src -|b1,b2,.. | piece,piece,...                  (C898Cached.Plan, block rows by row id)
      L i,i,...                                           (stepNLinks, the link indices)
     step 14 has no plans in Lean (pure common-point overlap); we emit P src b | (empty block,
     no pieces) for each source, so that the overlap obligation is the whole pose.
  c898_fused.txt   (C898Chord.Fused, vertical windows, radius index = pose angle)
      W left|right ln ld hn hd
      N left|right coll src k lowRow highRow | p<i>.<j>;p<i>.<j>     (Neighbor, positions in poseRows)
      F src k lowCut upCut closeRow tgt|- | hint;...                  (DirectPlan; inputs = cutRows)
      D sources n1L n2L n3L n1R n2R n3R target                         (domains)
"""
import os, re, glob
from fractions import Fraction as Q

ROOT = "n12/ext/jatloe/Lean/Proofs/N12-jatloe/Compact/Cases/C898"
OUT = "n12/data/cert"


def qparse(s):
    s = s.strip().strip("()")
    if "/" in s:
        a, b = s.split("/")
        return Q(int(a), int(b))
    return Q(int(s))


def lower(b, strict):
    return (b.denominator, 0, -b.numerator, strict)


def upper(b, strict):
    return (-b.denominator, 0, b.numerator, strict)


def enc_row(r):
    return "%d,%d,%d,%d" % (r[0], r[1], r[2], 1 if r[3] else 0)


def main():
    # rows
    t = open(ROOT + "/SharedRows.lean").read()
    body = t.split('sparse_rows% "')[1].split('"')[0]
    rows = {}
    for l in body.split("\n"):
        l = l.strip()
        if not l:
            continue
        k, v = l.split(":")
        x, y, c, s, d = v.split(",")
        k = int(k)
        assert k not in rows and k < 26026
        rows[k] = (int(x), int(y), int(c), s == "true", int(d))
    t = open(ROOT + "/SharedPoses.lean").read()
    body = t.split('sparse_poses% 64 26026 "')[1].split('"')[0]
    poses = {}
    for l in body.split("\n"):
        l = l.strip()
        if not l:
            continue
        k, v = l.split(":")
        a, rs = v.split(";")
        k, a = int(k), int(a)
        assert k not in poses and k < 3317 and a < 64
        rl = [int(x) for x in rs.split(",") if x]
        assert all(r < 26026 for r in rl)
        poses[k] = (a, rl)
    with open(OUT + "/c898_rows.txt", "w") as f:
        for k in sorted(rows):
            x, y, c, s, d = rows[k]
            f.write("%d %d %d %d %d %d\n" % (k, x, y, c, 1 if s else 0, d))
    with open(OUT + "/c898_poses.txt", "w") as f:
        for k in sorted(poses):
            f.write("%d %d %s\n" % (k, poses[k][0], ",".join(map(str, poses[k][1]))))
    row = lambda i: rows.get(i, (0, 0, 0, False, 0))[:4]
    pose = lambda i: poses.get(i, (0, []))
    # domains
    t = open(ROOT + "/SharedDomains.lean").read()
    doms = {}
    for m in re.finditer(r"def continuousScout898Domain(\d+_\d+)Ids : List \(Fin poseCount\) := \[([\d,\s]*)\]", t):
        doms[m.group(1)] = [int(x) for x in m.group(2).split(",") if x.strip()]
    with open(OUT + "/c898_domains.txt", "w") as f:
        for k in sorted(doms):
            f.write("%s %s\n" % (k, ",".join(map(str, doms[k]))))
    # links
    links = []
    for n in range(15):
        t = open(ROOT + "/CompactRelaxation/Data%02d.lean" % n).read()
        ent = {}
        for m in re.finditer(r"def entry(\d+) : Entry dictionary :=\s*cached_relaxation%\(dictionary, (\d+), (\d+)\)", t):
            ent[int(m.group(1))] = (int(m.group(2)), int(m.group(3)))
        order = re.search(r"data[^\n]*:=[^\[]*\[(.*?)\]", t, re.S).group(1)
        order = [int(re.match(r"entry(\d+)$", x.strip()).group(1)) for x in order.split(",") if x.strip()]
        assert order == list(range(len(ent))) and len(ent) == (64 if n < 14 else 31), n
        links += [ent[i] for i in order]
    assert len(links) == 927
    for s, g in links:
        assert pose(s)[0] == pose(g)[0]
    with open(OUT + "/c898_links.txt", "w") as f:
        for i, (s, g) in enumerate(links):
            f.write("%d %d %d\n" % (i, s, g))
    # blocks
    t = open(ROOT + "/PairRecords.lean").read()
    bd = t.split("def blockData : Array (List (Fin rowCount)) := #[")[1].split("\n]")[0]
    blocks = [[int(x) for x in m.group(1).split(",") if x.strip()] for m in re.finditer(r"\[([\d,\s]*)\]", bd)]
    # steps
    os.makedirs(OUT + "/c898_plans", exist_ok=True)
    steps = []
    tot = 0
    for fn in sorted(glob.glob(ROOT + "/CachedPairs/Step??.lean")):
        st = re.search(r"Step(\d\d)\.lean$", fn).group(1)
        t = open(fn).read()
        dd = re.findall(r"OrientedPoseCovered continuousScout898Domain(\d+_\d+) [qt]", t)
        S, N, T = dd
        recs = []
        if st == "14":
            plans = [(s, None, []) for s in doms[S]]
            lk = []
            pieces = []
        else:
            d = open(ROOT + "/CachedPairs/Step%sData.lean" % st).read()
            n = int(st)
            pl = d.split("def step%dPlans : List Plan := [" % n)[1].split("\n]")[0]
            plans = []
            for m in re.finditer(r"⟨(\d+),(none|some \d+),\[([\d,\s]*)\]⟩", pl):
                b = None if m.group(2) == "none" else blocks[int(m.group(2).split()[1])]
                plans.append((int(m.group(1)), b, [int(x) for x in m.group(3).split(",") if x.strip()]))
            pieces = [int(x) for x in re.search(r"def step%dPieces : List \(Fin poseCount\) := \[([\d,\s]*)\]" % n, d).group(1).split(",") if x.strip()]
            lk = [int(x) for x in re.search(r"def step%dLinks : List \(Fin 927\) := \[([\d,\s]*)\]" % n, d).group(1).split(",") if x.strip()]
            assert [links[i][0] for i in lk] == pieces, st
            assert all(links[i][1] in doms[T] for i in lk), st
            for (_, _, ps) in plans:
                assert all(p in pieces for p in ps)
        assert [p[0] for p in plans] == doms[S], st
        for (s, b, ps) in plans:
            bs = "-" if b is None else "b:" + ",".join(map(str, b))
            if st == "14":
                bs = "b:"
            recs.append("P %d %s | %s" % (s, bs, ",".join(map(str, ps))))
        recs.append("L " + ",".join(map(str, lk)))
        with open(OUT + "/c898_plans/S%s.txt" % st, "w") as f:
            f.write("\n".join(recs) + "\n")
        steps.append("%s %s %s %s %d" % (st, S, N, T, len(plans)))
        tot += len(plans)
    with open(OUT + "/c898_steps.txt", "w") as f:
        f.write("\n".join(steps) + "\n")
    # fused chord
    rad = {}
    for m in re.finditer(r"def radius(\d+) : Radius := ⟨\(([-\d/]+)\), *\(([-\d/]+)\)⟩", open(ROOT + "/ChordRadii.lean").read()):
        rad[int(m.group(1))] = (qparse(m.group(2)), qparse(m.group(3)))
    assert sorted(rad) == list(range(64))
    hist = {}
    for l in open(OUT + "/chord_radii.txt"):
        k, bn, bd, rn, rd = map(int, l.split())
        hist[k] = (Q(bn, bd), Q(rn, rd))
    assert all(rad[k] == hist[k] for k in range(64))
    g = open(ROOT + "/ChordFusedGeometry.lean").read()
    W = {}
    for nm in ["leftLo", "leftHi", "rightLo", "rightHi"]:
        W[nm] = qparse(re.search(r"def %s : ℚ := ([\d/]+)" % nm, g).group(1))
    fl = []
    fl.append("W left %d %d %d %d" % (W["leftLo"].numerator, W["leftLo"].denominator, W["leftHi"].numerator, W["leftHi"].denominator))
    fl.append("W right %d %d %d %d" % (W["rightLo"].numerator, W["rightLo"].denominator, W["rightHi"].numerator, W["rightHi"].denominator))
    nt = open(ROOT + "/ChordFusedNeighbors.lean").read()
    ndoms = {}
    nnb = 0
    for side, sect in [("left", nt.split("namespace LeftNeighbors")[1].split("end LeftNeighbors")[0]),
                       ("right", nt.split("namespace RightNeighbors")[1].split("end RightNeighbors")[0])]:
        lo = W[side + "Lo"]; hi = W[side + "Hi"]
        for c in range(3):
            body = sect.split("def neighbors%d : List Neighbor := [" % c)[1].split("]")[0]
            dom = re.search(r"theorem neighbors%d_covered : NeighborCoverCheck continuousScout898Domain(\d+_\d+)Ids" % c, sect).group(1)
            ndoms[(side, c)] = dom
            srcs = []
            for m in re.finditer(r"⟨(\d+), (\d+), (\d+), (\d+), (\d+)⟩", body):
                p, ll, lr, ul, ur = map(int, m.groups())
                a, rl = pose(p)
                for x in (ll, lr, ul, ur):
                    assert x in rl
                r = rad[a][1]
                srcs.append(p)
                fl.append("N %s %d %d %d %s %s | p%d.%d;p%d.%d" % (side, c, p, a, enc_row(lower(hi - r, False)),
                          enc_row(upper(lo + r, False)), rl.index(ll), rl.index(lr), rl.index(ul), rl.index(ur)))
                nnb += 1
            assert srcs == doms[dom], (side, c)
    d = open(ROOT + "/ChordFusedData.lean").read()
    fps = []
    for m in re.finditer(r"def plan(\d+) : DirectPlan := ⟨(\d+), (none|some \d+), \[(.*?)\], (\d+), (\d+)⟩", d):
        src = int(m.group(2))
        tg = None if m.group(3) == "none" else int(m.group(3).split()[1])
        sups = [tuple(map(int, x)) for x in re.findall(r"⟨(\d+), (\d+), (\d+)⟩", m.group(4))]
        cl, cr = int(m.group(5)), int(m.group(6))
        a, rl = pose(src)
        r = rad[a][1]
        lc = lower(W["leftHi"] + r, True)
        uc = upper(W["rightLo"] - r, True)
        close = upper(W["leftHi"] + r, False)
        if tg is None:
            hints = ["p%d.%d" % (cl, cr)]
        else:
            assert pose(tg)[0] == a
            hints = []
            for t_ in pose(tg)[1]:
                if t_ in rl:
                    hints.append("c%d" % (2 + rl.index(t_)))
                else:
                    s_ = [x for x in sups if x[0] == t_][0]
                    hints.append("p%d.%d" % (s_[1], s_[2]))
        fps.append(src)
        fl.append("F %d %d %s %s %s %s | %s" % (src, a, enc_row(lc), enc_row(uc), enc_row(close),
                  "-" if tg is None else str(tg), ";".join(hints)))
        if tg is not None:
            assert tg in doms["5_11"]
    assert fps == doms["5_0"], "fused plans sources"
    fl.append("D 5_0 %s %s %s %s %s %s 5_11" % tuple(ndoms[(s, c)] for s in ("left", "right") for c in range(3)))
    with open(OUT + "/c898_fused.txt", "w") as f:
        f.write("\n".join(fl) + "\n")
    print("rows", len(rows), "poses", len(poses), "domains", len(doms), "links", len(links),
          "steps", len(steps), "plans", tot, "blocks", len(blocks), "fused neighbours", nnb,
          "fused plans", len(fps))


if __name__ == "__main__":
    os.chdir(".")
    main()
