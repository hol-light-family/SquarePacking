#!/usr/bin/env python3
"""Build a pose-space box tree for a weighted point certificate (method of Evan Daniel's
lean/scripts/gen_boxtree.py, re-implemented) and write a plain data file for the HOL Light
checker n12/bounds/cert_check.ml.

Usage: gen_tree.py CERT OUT [--K 12] [--J 20] [--look 1]

Integer semantics (must agree with n12/bounds/cover_lib.ml / n12/bounds/cert_check.ml):
  Q = D*2^K (spatial scale), points (X*S, Y*S)/Q, container M/Q with M = Mq*S, Mq = s*D;
  angle parameter u = U/R with R = 70*2^J, root U in [0, 29*2^J];
  root centre box [0, M - M//2]^2; splits at floor midpoints.
"""
import sys, time, argparse
from fractions import Fraction
sys.setrecursionlimit(100000)

def read_cert(path):
    it = iter(open(path).read().split())
    snum, sden = int(next(it)), int(next(it))
    D = int(next(it)); W = int(next(it)); m = int(next(it))
    pts = [(int(next(it)), int(next(it)), int(next(it))) for _ in range(m)]
    assert next(it, None) is None
    return Fraction(snum, sden), D, W, pts

def nsub(a, b): return a - b if a > b else 0

def triples(R, U0, U1):
    RR = R * R
    return [(2 * nsub(RR, U0 * U0), 4 * R * U0, RR + U0 * U0),
            (2 * nsub(RR, U1 * U1), 4 * R * U1, RR + U1 * U1),
            (2 * nsub(RR, U0 * U1), 2 * R * (U0 + U1), RR + U0 * U1)]

def tri_ok(G, a, b, xl, xh, yl, yh, X, Y):
    aX, bY, bX, aY = a * X, b * Y, b * X, a * Y
    return (aX + bY <= G + a * xl + b * yl and a * xh + b * yh <= G + aX + bY
            and aY + b * xh <= G + bX + a * yl and bX + a * yh <= G + aY + b * xl)

def wlo(Q, R, U0, U1):
    return (Q * nsub(R * R + 2 * U0 * R, U1 * U1)) // (2 * (R * R + U1 * U1))

class Ctx: pass

def clip(c, box):
    x0, x1, y0, y1, U0, U1 = box
    WL = wlo(c.Q, c.R, U0, U1)
    return max(x0, WL), min(x1, nsub(c.M, WL)), max(y0, WL), min(y1, nsub(c.M, WL))

def certified(c, box, cands):
    x0, x1, y0, y1, U0, U1 = box
    xl, xh, yl, yh = clip(c, box)
    tr = [(g * c.Q, a, b) for a, b, g in triples(c.R, U0, U1)]
    return [p for p in cands if all(tri_ok(G, a, b, xl, xh, yl, yh, p[0], p[1]) for G, a, b in tr)]

def rect_ok(c, box, Xa, Xb, Ya, Yb):
    x0, x1, y0, y1, U0, U1 = box
    xl, xh, yl, yh = clip(c, box)
    for a, b, g in triples(c.R, U0, U1):
        G = g * c.Q
        if not (a * Xb + b * Yb <= G + a * xl + b * yl and
                a * xh + b * yh <= G + a * Xa + b * Ya and
                a * Yb + b * xh <= G + a * yl + b * Xa and
                a * yh + b * Xb <= G + a * Ya + b * xl):
            return False
    return True

def rect_leaf(c, box, ok, st):
    # group certified points into vertical strips; each strip gives a rectangle
    ok = sorted(ok)
    nstrip = max(1, min(16, len(ok) // 8))
    rects = []
    for si in range(nstrip):
        grp = ok[si * len(ok) // nstrip:(si + 1) * len(ok) // nstrip]
        grp = sorted(grp, key=lambda p: p[1])
        lo, hi = 0, len(grp)
        flip = True
        while hi - lo >= 2:
            sub = grp[lo:hi]
            Xa = min(p[0] for p in sub); Xb = max(p[0] for p in sub)
            Ya = sub[0][1]; Yb = sub[-1][1]
            if rect_ok(c, box, Xa, Xb, Ya, Yb):
                rects.append((sum(p[2] for p in sub), (Xa, Xb, Ya, Yb), sub)); break
            if flip: hi -= 1
            else: lo += 1
            flip = not flip
    rects.sort(key=lambda r: -r[0])
    need = c.W; used = set(); chosen = []
    for w, rc, sub in rects:
        if need <= 0: break
        chosen.append((rc, sub)); need -= w
        for p in sub: used.add(p)
    indiv = []
    if need > 0:
        for p in sorted(ok, key=lambda p: -p[2]):
            if need <= 0: break
            if p in used: continue
            indiv.append(p); need -= p[2]
    assert need <= 0
    parts = ["M", str(len(chosen))]
    for (Xa, Xb, Ya, Yb), sub in chosen:
        ks = sorted(c.index[p] for p in sub)
        parts += [str(Xa), str(Xb), str(Ya), str(Yb), str(len(ks))] + list(map(str, ks))
        st['claims'] += len(ks); st['rects'] = st.get('rects', 0) + 1
    ks = sorted(c.index[p] for p in indiv)
    parts += [str(len(ks))] + list(map(str, ks))
    st['claims'] += len(ks); st['indiv'] = st.get('indiv', 0) + len(ks)
    return " ".join(parts)

def deficit(c, box, cands):
    x0, x1, y0, y1, U0, U1 = box
    if U1 > c.R: return c.W + 1
    xl, xh, yl, yh = clip(c, box)
    if xh < xl or yh < yl: return -1
    tr = [(g * c.Q, a, b) for a, b, g in triples(c.R, U0, U1)]
    need = c.W
    for p in cands:
        if need <= 0: break
        if all(tri_ok(G, a, b, xl, xh, yl, yh, p[0], p[1]) for G, a, b in tr):
            need -= p[2]
    return need

def near(c, box, cands):
    x0, x1, y0, y1 = box[:4]; F = c.F
    return [p for p in cands if x0 <= p[0] + F and p[0] <= x1 + F and y0 <= p[1] + F and p[1] <= y1 + F]

def split(box, axis):
    b = list(box); mid = (b[2*axis] + b[2*axis+1]) // 2
    l = b.copy(); r = b.copy(); l[2*axis+1] = mid; r[2*axis] = mid
    return tuple(l), tuple(r)

def score(c, box, cands, depth):
    d = deficit(c, box, cands)
    if d <= 0: return 0
    if depth == 0: return d
    cn = near(c, box, cands); best = None
    for a in range(3):
        if box[2*a+1] - box[2*a] <= 0: continue
        l, r = split(box, a)
        v = score(c, l, cn, depth-1) + score(c, r, cn, depth-1)
        best = v if best is None else min(best, v)
    return best + 0.5

def build_task(args):
    c, box, cands, depth, look = args
    st = dict(leaves=0, maxdepth=0, empty=0, claims=0, look=look)
    out = []
    build(c, box, cands, depth, st, out)
    return out, st

def build(c, box, cands, depth, st, out, pool=None, pdepth=-1, tasks=None):
    if deficit(c, box, cands) <= 0:
        st['leaves'] += 1; st['maxdepth'] = max(st['maxdepth'], depth)
        x0, x1, y0, y1, U0, U1 = box
        xl, xh, yl, yh = clip(c, box)
        if xh < xl or yh < yl:
            out.append("E"); st['empty'] += 1; return
        ok = certified(c, box, cands)
        if c.rects:
            out.append(rect_leaf(c, box, ok, st)); return
        ok.sort(key=lambda p: -p[2])
        need, take = c.W, []
        for p in ok:
            if need <= 0: break
            take.append(c.index[p]); need -= p[2]
        assert need <= 0
        take.sort(); st['claims'] += len(take)
        out.append("L " + str(len(take)) + " " + " ".join(map(str, take))); return
    if depth > 90: raise RuntimeError("depth")
    ws = [(box[1]-box[0]) / c.Q, (box[3]-box[2]) / c.Q, (box[5]-box[4]) / c.R]
    cn = near(c, box, cands); best = None
    for a in range(3):
        if ws[a] == 0: continue
        l, r = split(box, a)
        key = (score(c, l, cn, st['look']) + score(c, r, cn, st['look']), -ws[a])
        if best is None or key < best[0]: best = (key, a)
    axis = best[1]
    out.append("XYU"[axis])
    l, r = split(box, axis)
    if tasks is not None and depth + 1 >= pdepth:
        for b in (l, r):
            tasks.append((c, b, cn, depth+1, st['look']))
            out.append(("TASK", len(tasks) - 1))
        return
    build(c, l, cn, depth+1, st, out, pool, pdepth, tasks)
    build(c, r, cn, depth+1, st, out, pool, pdepth, tasks)

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('cert'); ap.add_argument('out')
    ap.add_argument('--K', type=int, default=12); ap.add_argument('--J', type=int, default=20)
    ap.add_argument('--look', type=int, default=1)
    ap.add_argument('--procs', type=int, default=1)
    ap.add_argument('--pdepth', type=int, default=10)
    ap.add_argument('--rects', type=int, default=0)
    a = ap.parse_args()
    s, D, W, pts = read_cert(a.cert)
    S = 2 ** a.K; Q = D * S; Mq = s * D; assert Mq.denominator == 1; Mq = int(Mq); M = Mq * S
    R = 70 * 2 ** a.J; Umax = 29 * 2 ** a.J
    P = sorted((X * S, Y * S, w) for X, Y, w in pts)
    assert len(set((x, y) for x, y, _ in P)) == len(P), "duplicate points"
    idx = {p: i for i, p in enumerate(P)}
    pos = {(x, y): i for i, (x, y, _) in enumerate(P)}
    perm = []
    for (x, y, w) in P:
        px = pos[(M - x, y)]; py = pos[(x, M - y)]; ps = pos[(y, x)]
        assert P[px][2] == w and P[py][2] == w and P[ps][2] == w
        perm.append((px, py, ps))
    c = Ctx(); c.Q, c.R, c.M, c.W, c.F, c.index = Q, R, M, W, 3 * Q // 4, idx
    c.rects = a.rects
    st = dict(leaves=0, maxdepth=0, empty=0, claims=0, look=a.look)
    root = (0, M - M // 2, 0, M - M // 2, 0, Umax)
    out = []; t0 = time.time()
    if a.procs > 1:
        import multiprocessing as mp
        tasks = []
        build(c, root, P, 0, st, out, None, a.pdepth, tasks)
        print(f"{len(tasks)} tasks", file=sys.stderr)
        with mp.Pool(a.procs) as pool:
            res = pool.map(build_task, tasks, chunksize=1)
        out2 = []
        for tok in out:
            if isinstance(tok, tuple):
                o, s2 = res[tok[1]]
                out2.extend(o)
                for k in ('leaves', 'empty', 'claims', 'rects', 'indiv'): st[k] = st.get(k, 0) + s2.get(k, 0)
                st['maxdepth'] = max(st['maxdepth'], s2['maxdepth'])
            else:
                out2.append(tok)
        out = out2
    else:
        build(c, root, P, 0, st, out)
    print(f"rects {st.get('rects',0)} indiv {st.get('indiv',0)}", file=sys.stderr)
    print(f"leaves {st['leaves']} empty {st['empty']} claims {st['claims']} maxdepth {st['maxdepth']} "
          f"({time.time()-t0:.1f}s)", file=sys.stderr)
    with open(a.out, 'w') as f:
        f.write(f"{s.numerator} {s.denominator} {D} {W} {len(P)} {S} {Q} {M} {R} {Umax} {root[1]}\n")
        for (x, y, w), (px, py, ps) in zip(P, perm):
            f.write(f"{x} {y} {w} {px} {py} {ps}\n")
        f.write(f"{len(out)}\n")
        f.write("\n".join(out) + "\n")

if __name__ == '__main__':
    main()
