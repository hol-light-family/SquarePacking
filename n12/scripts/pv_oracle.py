#!/usr/bin/env python3
"""W-F6 oracle (untrusted): integer roots for the historical initial covers.

Input : n12/data/cert/pv_owners.txt, pv_entries.txt (n12/scripts/pv_extract.py),
        n12/data/cert/hist_rows.txt, hist_poses.txt, hist_domains.txt (n12/scripts/cert_extract.py),
        the 192 angle enclosures (n12/certlib/AngleData64.ml, AngleData128.ml).
Output: n12/data/cert/pv_roots.txt, one root per line (Lean DirectPoseCover.sourceRoot of the recipe):
   case owner angle | base | forbidden | plan | target
   base      : x,y,c,s,den;...        integer rows with denominators (Lean Form.encode of the
               selected poseInputs rows; den = denPred+1)
   forbidden : blocks separated by '/', rows x,y,c,s,den separated by ';'
   plan      : one item per line of  base ++ flatten forbidden  (in that order, duplicates kept):
               '.' = keep, or  i:scale:multiple  (Lean PlanarBoundaryFilter.LineExclusion,
               base index i)
   target    : pose id or '-'
   plan2     : fast route (PV_Fast.ml): per line '.' or i:j:li:lj:mu (two-row exclusion)
   wits      : per remaining line (separated by '/') the witnesses of its pairs with the later
               lines (',' separated): b<i> base row i negative, k<i> forbidden block i positive,
               t = targets checked
It also re-runs the complete PlanarVertexCheck on every root (exact integers) and the
domain equality  flatten targets = continuousScout<case>Domain<owner>_0, and reports
statistics.  Nothing here is trusted: HOL re-checks everything.
With --c898: reads pv898_owners/entries.txt and the C898 dictionary tables
n12/data/cert/c898_{rows,poses,domains}.txt (same formats as hist_*, to be written by the
W-C898 extractor) and writes pv898_roots.txt.
Usage: python3 n12/scripts/pv_oracle.py [--c898]
"""
import re, sys
from fractions import Fraction as Fr
from math import lcm

D = "n12/data/cert"


def load_angles():
    res = []
    for fn in ["n12/certlib/AngleData64.ml", "n12/certlib/AngleData128.ml"]:
        t = open(fn).read()
        for m in re.finditer(r'"AngleEnc ((?:\([^)]*\)\s*){7})"', t):
            vals = re.findall(r"\(([^)]*)\)", m.group(1))
            fs = []
            for v in vals:
                v = v.replace("&", "").replace(" ", "")
                fs.append(Fr(v))
            res.append(fs)
    assert len(res) == 192, len(res)
    return res  # lower upper c s outer inner wall


def pr(s):
    p, q = s.split(":")
    return Fr(int(p), int(q))


def pts(s):
    if s == "-":
        return []
    out = []
    for item in s.split(";"):
        a, b = item.split(",")
        out.append((pr(a), pr(b)))
    return out


def point_forms(c, s, side, P):
    px, py = P
    h = side / 2
    # LinCon rows over centre (x, y):  coefficient x, coefficient y, constant, strict
    return [(-c, -s, h + c * px + s * py, 1),
            (c, s, h - c * px - s * py, 1),
            (s, -c, h - s * px + c * py, 1),
            (-s, c, h + s * px - c * py, 1)]


def pose_inputs(w, inside):
    lo, up, c, s, outer, inner, wall = w
    rows = []
    for P in inside:
        rows += point_forms(c, s, Fr(1001, 1000) * outer, P)
    rows += [(Fr(1), Fr(0), -wall / 2, 0), (Fr(-1), Fr(0), 4 - wall / 2, 0),
             (Fr(0), Fr(1), -wall / 2, 0), (Fr(0), Fr(-1), 4 - wall / 2, 0)]
    rows.append((Fr(0), Fr(0), Fr(1), 1))
    return rows


def pose_forbidden(w, outside):
    lo, up, c, s, outer, inner, wall = w
    return [point_forms(c, s, inner, P) for P in outside]


def encode(r):
    x, y, k, st = r
    d = lcm(x.denominator, y.denominator, k.denominator)
    return (int(x * d), int(y * d), int(k * d), st, d)


def det(a, b):
    return a[0] * b[1] - a[1] * b[0]


def vertex(a, b):
    dt = det(a, b)
    sg = 1 if dt >= 0 else -1
    return (sg * (a[1] * b[2] - a[2] * b[1]), sg * (a[2] * b[0] - a[0] * b[2]), sg * dt)


def veval(v, r):
    return r[0] * v[0] + r[1] * v[1] + r[2] * v[2]


def exclusion(base, line):
    """Lean BoundaryHintSyntax.findHint style: a parallel base row strictly negative on line."""
    piv = line[0] if line[0] != 0 else line[1]
    if piv == 0:
        return None
    scale = abs(piv)
    for i, r in enumerate(base):
        rp = r[0] if line[0] != 0 else r[1]
        # want scale*r = mult*line on x,y
        mult_num = rp * scale
        if mult_num % piv != 0:
            continue
        mult = mult_num // piv
        if scale * r[0] == mult * line[0] and scale * r[1] == mult * line[1] and \
                scale * r[2] < mult * line[2]:
            return (i, scale, mult)
    return None


def exclusion2(base, line):
    """Two-row exclusion: li*r_i + lj*r_j + mu*line = (0, 0, negative), li, lj >= 0."""
    h = exclusion(base, line)
    if h is not None:
        i, sc, m = h
        return (i, i, sc, 0, -m)
    Lx, Ly, Lc = line[0], line[1], line[2]
    if Lx == 0 and Ly == 0:
        return None
    # parametrise the line: p0 + t d, d = (-Ly, Lx)
    if Lx != 0:
        p0 = (Fr(-Lc, Lx), Fr(0))
    else:
        p0 = (Fr(0), Fr(-Lc, Ly))
    d = (-Ly, Lx)
    lo = hi = None
    loi = hii = None
    for i, r in enumerate(base):
        a = r[0] * d[0] + r[1] * d[1]
        b = r[0] * p0[0] + r[1] * p0[1] + r[2]
        if a == 0:
            continue
        t = -b / a
        if a > 0:
            if lo is None or t > lo:
                lo, loi = t, i
        else:
            if hi is None or t < hi:
                hi, hii = t, i
    if lo is None or hi is None or not lo > hi:
        return None
    ri, rj = base[loi], base[hii]
    ai = ri[0] * d[0] + ri[1] * d[1]
    aj = rj[0] * d[0] + rj[1] * d[1]
    li, lj = -aj, ai          # li*ai + lj*aj = 0, both > 0
    X = li * ri[0] + lj * rj[0]
    Y = li * ri[1] + lj * rj[1]
    lam = Fr(X, Lx) if Lx != 0 else Fr(Y, Ly)
    q = lam.denominator
    li, lj = li * q, lj * q
    mu = -int(lam * q)
    from math import gcd
    g = gcd(gcd(li, lj), abs(mu))
    li, lj, mu = li // g, lj // g, mu // g
    ok = (li * ri[0] + lj * rj[0] + mu * Lx == 0 and li * ri[1] + lj * rj[1] + mu * Ly == 0 and
          li * ri[2] + lj * rj[2] + mu * Lc < 0)
    return (loi, hii, li, lj, mu) if ok else None


def witness(v, base, forb):
    for i, r in enumerate(base):
        if veval(v, r) < 0:
            return "b%d" % i
    for k, blk in enumerate(forb):
        if all(veval(v, r) > 0 for r in blk):
            return "k%d" % k
    return "t"


def feasible(v, base, forb):
    for r in base:
        if veval(v, r) < 0:
            return False
    for blk in forb:
        if all(veval(v, r) > 0 for r in blk):
            return False
    return True


def main():
    c898 = "--c898" in sys.argv
    dic = "c898" if c898 else "hist"
    pre = "pv898" if c898 else "pv"
    angles = load_angles()
    rows = {}
    for l in open(D + "/%s_rows.txt" % dic):
        k, x, y, c, s, dp = l.split()
        rows[int(k)] = (int(x), int(y), int(c), int(s))
    poses = {}
    for l in open(D + "/%s_poses.txt" % dic):
        f = l.split()
        poses[int(f[0])] = (int(f[1]), [int(t) for t in f[2].split(",")] if len(f) > 2 else [])
    doms = {}
    for l in open(D + "/%s_domains.txt" % dic):
        f = l.split()
        if c898:   # c898_domains.txt: name ids
            f = ["898"] + f
        doms[(f[0], f[1])] = [int(t) for t in f[2].split(",")] if len(f) > 2 else []
    owners = {}
    for l in open(D + "/%s_owners.txt" % pre):
        c, k, g, ins, outs = l.split()
        owners[(c, int(k))] = (int(g), pts(ins), pts(outs))
    targets = {}
    out = open(D + "/%s_roots.txt" % pre, "w")
    npairs = nnonpar = nlines = nact = 0
    nact2pairs = [0]
    nact2nonpar = [0]
    maxint = 0
    nroots = 0
    for l in open(D + "/%s_entries.txt" % pre):
        c, k, a, idx, t = l.split()
        k, a = int(k), int(a)
        g, ins, outs = owners[(c, k)]
        w = angles[a]
        pin = pose_inputs(w, ins)
        idx = [int(i) for i in idx.split(",")] if idx != "-" else []
        base = [encode(pin[i]) for i in idx]
        forb = [[encode(r) for r in blk] for blk in pose_forbidden(w, outs)]
        if t == "-":
            tg = [(0, 0, -1, 0)]
        else:
            pa, prs = poses[int(t)]
            assert pa == a, (c, k, a, t, pa)
            tg = [rows.get(r, (0, 0, 0, 0)) for r in prs]
            for r in tg:  # strictOK
                assert r[3] == 0 or (r[0] == 0 and r[1] == 0 and r[2] > 0), (c, k, a, r)
        targets.setdefault((c, k), []).extend([] if t == "-" else [int(t)])
        # box normals
        assert any(r[0] > 0 and r[1] == 0 for r in base) and any(r[0] < 0 and r[1] == 0 for r in base)
        assert any(r[0] == 0 and r[1] > 0 for r in base) and any(r[0] == 0 and r[1] < 0 for r in base)
        lines = base + [r for blk in forb for r in blk]
        plan = []
        active = []
        for ln in lines:
            h = exclusion(base, ln)
            plan.append(h)
            if h is None:
                active.append(ln)
        # complete vertex check on the active lines (unordered pairs)
        for i in range(len(active)):
            for j in range(i + 1, len(active)):
                A, B = active[i], active[j]
                npairs += 1
                if det(A, B) == 0:
                    continue
                nnonpar += 1
                v = vertex(A, B)
                if feasible(v, base, forb):
                    for r in tg:
                        assert veval(v, r) >= 0, ("vertex check fails", c, k, a)
        # fast route: two-row exclusions and one witness per unordered pair
        plan2 = [exclusion2(base, ln) for ln in lines]
        act2 = [ln for ln, h in zip(lines, plan2) if h is None]
        wrows = []
        for i in range(len(act2)):
            ws = []
            for j in range(i + 1, len(act2)):
                A, B = act2[i], act2[j]
                if det(A, B) == 0:
                    ws.append("t")
                    continue
                v = vertex(A, B)
                w = witness(v, base, forb)
                if w == "t":
                    for r in tg:
                        assert veval(v, r) >= 0
                ws.append(w)
                nact2nonpar[0] += 1
            wrows.append(",".join(ws))
            nact2pairs[0] += len(ws)
        nlines += len(lines)
        nact += len(active)
        for r in lines:
            maxint = max(maxint, abs(r[0]), abs(r[1]), abs(r[2]))
        fr = lambda r: "%d,%d,%d,%d,%d" % r
        out.write("%s %d %d | %s | %s | %s | %s | %s | %s\n" % (
            c, k, a, ";".join(fr(r) for r in base),
            "/".join(";".join(fr(r) for r in blk) for blk in forb) if forb else "-",
            ";".join("." if h is None else "%d:%d:%d" % h for h in plan),
            t,
            ";".join("." if h is None else "%d:%d:%d:%d:%d" % h for h in plan2),
            "/".join(wrows)))
        nroots += 1
    out.close()
    for (c, k), ts in targets.items():
        assert ts == doms[(c, "%d_0" % k)], ("domain mismatch", c, k)
    print("roots", nroots, "lines", nlines, "active", nact, "pairs", npairs, "nonparallel", nnonpar,
          "max |coef|", maxint, "bits", maxint.bit_length(),
          "fast-route pairs", nact2pairs[0], "nonparallel", nact2nonpar[0])


if __name__ == "__main__":
    main()
