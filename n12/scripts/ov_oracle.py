#!/usr/bin/env python3
"""W-F345 oracle (UNTRUSTED; it only finds certificates, HOL re-checks everything).

For every block-overlap obligation of the 113 historical pair stages
(design n12/docs/cert_design.md §4.2) -- a source context (pose src + block rows) and a
neighbour context (pose n, no block) -- it finds directional support certificates
(F3: a nonnegative combination of <= 2 context rows whose (x, y) part is a positive
multiple k of the integer face normal N of an angle) such that the 8-axis SAT test
(F4) holds with the support bounds.  Per context, the supports are tabulated for
every angle the context is paired with (its own angle first).

Output: n12/data/cert/ov_ctx.txt, one context per line
  <pose> <B-|B=r1,r2,..> | <angle>:<sup0>/<sup1>/<sup2>/<sup3>;<angle>:...
  sup = k,e,s,w@i+w@i   (k > 0, row combination sum_t w_t * rows[i_t] = (k*Nx, k*Ny, e),
                         s = strict flag 0/1; indices into  pose rows ++ block rows)
  The direction order per angle (ref C,S): (C,S), (-C,-S), (-S,C), (S,-C).
"""
import sys, os, re, math
from fractions import Fraction as Fr

ROOT = '.'
D = ROOT + '/data/cert'

def load():
    rows = {}
    for l in open(D + '/hist_rows.txt'):
        p = l.split()
        rows[int(p[0])] = (int(p[1]), int(p[2]), int(p[3]), p[4] == '1')
    poses = {}
    for l in open(D + '/hist_poses.txt'):
        p = l.split()
        poses[int(p[0])] = (int(p[1]), [int(x) for x in p[2].split(',')] if len(p) > 2 else [])
    doms = {}
    for l in open(D + '/hist_domains.txt'):
        p = l.split()
        doms[(p[0], p[1])] = [int(x) for x in p[2].split(',')] if len(p) > 2 else []
    stages = [l.split() for l in open(D + '/hist_stages.txt')]
    return rows, poses, doms, stages

def row_of(rows, i):
    return rows.get(i, (0, 0, 0, False))

def pose_of(poses, i):
    return poses.get(i, (0, []))

def parse_q(s):
    s = s.strip()
    m = re.fullmatch(r'\(?&(\d+)(?: / &(\d+))?\)?', s)
    return Fr(int(m.group(1)), int(m.group(2) or 1))

def load_refs():
    refs = []
    for fn in ['AngleData64.ml', 'AngleData128.ml']:
        for l in open(ROOT + '/n12/certlib/' + fn):
            m = re.match(r'\s*"AngleEnc (.*)";?\s*$', l)
            if not m:
                continue
            fields = re.findall(r'\(&\d+(?: / &\d+)?\)', m.group(1))
            assert len(fields) == 7, l
            lo, up, c, s, outer, inner, wall = [parse_q(f) for f in fields]
            Dd = c.denominator * s.denominator // math.gcd(c.denominator, s.denominator)
            C = int(c * Dd); S = int(s * Dd)
            assert C * C + S * S == Dd * Dd
            refs.append((C, S, Dd, inner.numerator, inner.denominator))
    assert len(refs) == 192
    return refs

def dirs(ref):
    C, S = ref[0], ref[1]
    return [(C, S), (-C, -S), (-S, C), (S, -C)]

OPP = [1, 0, 3, 2]

def vertices(R):
    """closure vertices of {p : row(p) >= 0 for all rows} as (X, Y, W) with W > 0,
    together with the list of tight row indices."""
    vs = {}
    n = len(R)
    for i in range(n):
        ax, ay, ac, _ = R[i]
        for j in range(i + 1, n):
            bx, by, bc, _ = R[j]
            det = ax * by - ay * bx
            if det == 0:
                continue
            X = -ac * by + ay * bc
            Y = -ax * bc + ac * bx
            W = det
            if W < 0:
                X, Y, W = -X, -Y, -W
            g = math.gcd(math.gcd(abs(X), abs(Y)), W)
            X //= g; Y //= g; W //= g
            if (X, Y, W) in vs:
                continue
            tight = []
            ok = True
            for k in range(n):
                rx, ry, rc, _ = R[k]
                v = rx * X + ry * Y + rc * W
                if v < 0:
                    ok = False
                    break
                if v == 0:
                    tight.append(k)
            if ok:
                vs[(X, Y, W)] = tight
    return vs

def support(R, vs, N):
    """certificate (k, e, s, terms) for  k*(N.p) + e >= 0 on the context, best bound."""
    Nx, Ny = N
    best = None
    for (X, Y, W), tight in vs.items():
        val = Fr(Nx * X + Ny * Y, W)
        if best is None or val < best[0]:
            best = (val, tight)
    if best is None:
        return None
    val, tight = best
    # all vertices attaining the min
    cands = []
    for (X, Y, W), t in vs.items():
        if Fr(Nx * X + Ny * Y, W) == val:
            cands.append(t)
    res = []
    for t in cands:
        for i in t:
            ax, ay, ac, as_ = R[i]
            # single parallel row
            if ax * Ny == ay * Nx and ax * Nx + ay * Ny > 0:
                if Nx != 0:
                    w, k = abs(Nx), abs(ax)
                else:
                    w, k = abs(Ny), abs(ay)
                res.append((k, w * ac, as_, [(w, i)]))
            for j in t:
                if j <= i:
                    continue
                bx, by, bc, bs = R[j]
                det = ax * by - ay * bx
                if det == 0:
                    continue
                sg = 1 if det > 0 else -1
                lam = sg * (Nx * by - Ny * bx)
                mu = sg * (ax * Ny - ay * Nx)
                k = sg * det
                if lam < 0 or mu < 0:
                    continue
                terms = [(lam, i), (mu, j)] if mu > 0 else [(lam, i)]
                if lam == 0:
                    terms = [(mu, j)]
                e = lam * ac + mu * bc
                s = (lam > 0 and as_) or (mu > 0 and bs)
                res.append((k, e, s, terms))
    if not res:
        return None
    # reduce by the gcd of k and the weights (e stays integral)
    red = []
    for (k, e, st, terms) in res:
        g = k
        for (w, _) in terms:
            g = math.gcd(g, w)
        red.append((k // g, e // g, st, [(w // g, i) for (w, i) in terms]))
    res = red
    # prefer strict, then small k
    res.sort(key=lambda r: (not r[2], r[0]))
    return res[0]

def radiusG(N, ref):
    C, S = ref[0], ref[1]
    return abs(N[0] * C + N[1] * S) + abs(-N[0] * S + N[1] * C)

def axis_ok(supA, supB, refa, refb, N):
    kA, eA, sA, _ = supA
    kB, eB, sB, _ = supB
    CA, SA, DA, NA, MA = refa
    CB, SB, DB, NB, MB = refb
    GA = radiusG(N, refa); GB = radiusG(N, refb)
    lhs = 2 * MA * DA * MB * DB * (eA * kB + eB * kA)
    rhs = kA * kB * (NA * GA * MB * DB + NB * GB * MA * DA)
    return lhs < rhs or (lhs <= rhs and (sA or sB))

def own_bounds(sup, ref):
    """for the 4 own supports: list of (j, k, e, s) giving the kernel test
    2M(k N_j.(X,Y) + e W) < k D Nn W  (<= if s)"""
    return [(dirs(ref)[j], sup[j]) for j in range(4)]

def pt_in_kernel(P, sups, ref):
    X, Y, W = P
    C, S, Dd, Nn, M = ref
    for j, N in enumerate(dirs(ref)):
        k, e, s, _ = sups[j]
        lhs = 2 * M * (k * (N[0] * X + N[1] * Y) + e * W)
        rhs = k * Dd * Nn * W
        if not (lhs < rhs or (s and lhs <= rhs)):
            return False
    return True

def kernel_halfplanes(sups, ref):
    """float half-planes a.P < b of the kernel"""
    C, S, Dd, Nn, M = ref
    hs = []
    for j, N in enumerate(dirs(ref)):
        k, e, s, _ = sups[j]
        # N.P < D*Nn/(2M) - e/k
        hs.append((N[0], N[1], Dd * Nn / (2 * M) - e / k))
    return hs

def find_point(hs):
    """rational interior point of the intersection of open half-planes (floats), or None"""
    vs = []
    n = len(hs)
    for i in range(n):
        a1, b1, c1 = hs[i]
        for j in range(i + 1, n):
            a2, b2, c2 = hs[j]
            det = a1 * b2 - a2 * b1
            if abs(det) < 1e-12 * (abs(a1 * b2) + abs(a2 * b1) + 1e-300):
                continue
            x = (c1 * b2 - c2 * b1) / det
            y = (a1 * c2 - a2 * c1) / det
            if all(a * x + b * y <= c + 1e-9 * (abs(c) + 1) for (a, b, c) in hs):
                vs.append((x, y))
    if not vs:
        return None
    x = sum(v[0] for v in vs) / len(vs)
    y = sum(v[1] for v in vs) / len(vs)
    return x, y

def rationals_near(x, y):
    for den in [1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 4096, 16384, 65536, 1 << 20, 1 << 24, 1 << 30]:
        yield (round(x * den), round(y * den), den)

def empty_witness(R):
    """Farkas witness (<= 3 rows) that the closed-or-strict region R is empty:
    sum w_i row_i = (0, 0, c) with c < 0, or c <= 0 and a strict row with w > 0."""
    from itertools import combinations
    n = len(R)
    for i, j, k in combinations(range(n), 3):
        A = [R[i], R[j], R[k]]
        (x1, y1, c1, _), (x2, y2, c2, _), (x3, y3, c3, _) = A
        l = [x2 * y3 - x3 * y2, x3 * y1 - x1 * y3, x1 * y2 - x2 * y1]
        for sg in (1, -1):
            L = [sg * v for v in l]
            if min(L) >= 0 and max(L) > 0:
                g = 0
                for v in L:
                    g = math.gcd(g, v)
                L = [v // g for v in L]
                c = L[0] * c1 + L[1] * c2 + L[2] * c3
                st = any(L[t] > 0 and A[t][3] for t in range(3))
                if c < 0 or (c <= 0 and st):
                    idx = [i, j, k]
                    return idx, [(L[t], idx[t]) for t in range(3) if L[t] > 0]
    raise Exception('no empty witness')

def load898():
    rows = {}
    for l in open(D + '/c898_rows.txt'):
        p = l.split()
        rows[int(p[0])] = (int(p[1]), int(p[2]), int(p[3]), p[4] == '1')
    poses = {}
    for l in open(D + '/c898_poses.txt'):
        p = l.split()
        poses[int(p[0])] = (int(p[1]), [int(x) for x in p[2].split(',')] if len(p) > 2 else [])
    doms = {}
    for l in open(D + '/c898_domains.txt'):
        p = l.split()
        doms[p[0]] = [int(x) for x in p[1].split(',')] if len(p) > 1 else []
    stage_hdrs = []
    for l in open(D + '/c898_steps.txt'):
        st, sd, nd, td, k = l.split()
        hdrs = []
        for pl in open(D + f'/c898_plans/S{st}.txt'):
            if not pl.startswith('P'):
                continue
            a = pl.split('|')[0].split()
            if a[2] != '-':
                blk = tuple(int(x) for x in a[2][2:].split(',') if x)
                hdrs.append((int(a[1]), blk))
        stage_hdrs.append(('898', st, hdrs, doms[nd]))
    return rows, poses, stage_hdrs

PFX = 'ov'

def main():
    global PFX
    refs = load_refs()
    stage_hdrs = []
    ctxs = set()
    if len(sys.argv) > 1 and sys.argv[1] == 'c898':
        PFX = 'ov898'
        rows, poses, stage_hdrs = load898()
        for (_, _, hdrs, nbrs) in stage_hdrs:
            for h in hdrs:
                ctxs.add(h)
            for nb in nbrs:
                ctxs.add((nb, None))
        stages = []
    else:
        rows, poses, doms, stages = load()
    for (c, st, s, n, t, k) in stages:
        nbrs = doms[(c, n)]
        hdrs = []
        for pl in open(D + f'/hist_plans/C{c}_S{st}.txt'):
            a = pl.split('|')[0].split()
            if a[1] != 'B-':
                blk = tuple(int(x) for x in a[1][2:].split(',') if x)
                hdrs.append((int(a[0]), blk))
        stage_hdrs.append((c, st, hdrs, nbrs))
        for h in hdrs:
            ctxs.add(h)
        for nb in nbrs:
            ctxs.add((nb, None))
    ctx_R = {}; ctx_vs = {}; sups = {}; empty = set()
    for key in ctxs:
        p, blk = key
        a, rids = pose_of(poses, p)
        R = [row_of(rows, i) for i in rids] + [row_of(rows, i) for i in (blk or ())]
        ctx_R[key] = R
        vs = vertices(R)
        ctx_vs[key] = vs
        if not vs:
            empty.add(key)
            continue
        ss = [support(R, vs, N) for N in dirs(refs[a])]
        assert all(x is not None for x in ss), key
        sups[(key, a)] = ss
    print('contexts', len(ctxs), 'empty', empty, file=sys.stderr)
    need = {}   # key -> partner angles for axis pairs
    npt = nax = 0
    out = open(D + '/' + PFX + '_pairs.txt', 'w')
    for (c, st, hdrs, nbrs) in stage_hdrs:
        out.write('S %s %s %d %d\n' % (c, st, len(hdrs), len(nbrs)))
        for h in hdrs:
            if h in empty:
                out.write('E\n'); continue
            a = pose_of(poses, h[0])[0]
            sA = sups[(h, a)]
            hsA = kernel_halfplanes(sA, refs[a])
            cache = []
            meth = []
            for nb in nbrs:
                nk = (nb, None)
                b = pose_of(poses, nb)[0]
                sB = sups[(nk, b)]
                got = None
                for P in cache:
                    if pt_in_kernel(P, sA, refs[a]) and pt_in_kernel(P, sB, refs[b]):
                        got = P; break
                if got is None:
                    fp = find_point(hsA + kernel_halfplanes(sB, refs[b]))
                    if fp is not None:
                        for P in rationals_near(*fp):
                            if pt_in_kernel(P, sA, refs[a]) and pt_in_kernel(P, sB, refs[b]):
                                got = P; cache.insert(0, P); break
                if got is not None:
                    npt += 1
                    meth.append('%d,%d,%d' % got)
                else:
                    nax += 1
                    meth.append('A')
                    need.setdefault(h, set()).add(b)
                    need.setdefault(nk, set()).add(a)
            out.write(' '.join(meth) + '\n')
    out.close()
    print('point pairs', npt, 'axis pairs', nax, file=sys.stderr)
    for key, angs in need.items():
        R = ctx_R[key]; vs = ctx_vs[key]
        for b in angs:
            if (key, b) not in sups:
                ss = [support(R, vs, N) for N in dirs(refs[b])]
                assert all(x is not None for x in ss)
                sups[(key, b)] = ss
    # ---- rounding of the support bounds (smaller numbers for the HOL checks) ----
    # rounded entry (kr, er, True) with er/kr > e/k, kr = 2^bits; bits per (ctx, angle)
    BITS = [12, 16, 20, 24, 32, 40, 48, 64, None]
    lvl = {}
    def rounded(key, b):
        L = lvl.get((key, b), 0)
        ss = sups[(key, b)]
        if BITS[L] is None:
            return [(k, e, st, t) for (k, e, st, t) in ss]
        kr = 1 << BITS[L]
        return [(kr, (e * kr) // k + 1, True, t) for (k, e, st, t) in ss]
    rcache = {}
    def R(key, b):
        if (key, b) not in rcache:
            rcache[(key, b)] = rounded(key, b)
        return rcache[(key, b)]
    def bump(key, b):
        lvl[(key, b)] = min(lvl.get((key, b), 0) + 1, len(BITS) - 1)
        rcache.pop((key, b), None)
    pair_list = []
    lines = open(D + '/' + PFX + '_pairs.txt').read().split('\n')
    li = 0
    for (c, st, hdrs, nbrs) in stage_hdrs:
        li += 1
        for h in hdrs:
            ms = lines[li].split(); li += 1
            if h in empty:
                continue
            for nb, m in zip(nbrs, ms):
                pair_list.append((h, (nb, None), m))
    for it in range(len(BITS)):
        fails = 0
        for (h, nk, m) in pair_list:
            a = pose_of(poses, h[0])[0]; b = pose_of(poses, nk[0])[0]
            if m != 'A':
                P = tuple(int(x) for x in m.split(','))
                okA = pt_in_kernel(P, R(h, a), refs[a]); okB = pt_in_kernel(P, R(nk, b), refs[b])
                if not okA: bump(h, a)
                if not okB: bump(nk, b)
                if not (okA and okB): fails += 1
            else:
                ok = True
                for X in (a, b):
                    ds = dirs(refs[X]); sA = R(h, X); sB = R(nk, X)
                    for j in range(4):
                        if not axis_ok(sA[j], sB[OPP[j]], refs[a], refs[b], ds[j]):
                            ok = False
                    if not ok:
                        bump(h, X); bump(nk, X); break
                if not ok: fails += 1
        print('rounding pass', it, 'failures', fails, file=sys.stderr)
        if fails == 0:
            break
    assert fails == 0
    from collections import Counter
    print('levels', Counter(BITS[lvl.get(k, 0)] for k in sups), file=sys.stderr)
    nent = 0
    with open(D + '/' + PFX + '_ctx.txt', 'w') as f:
        for key in sorted(ctxs, key=lambda k: (k[0], k[1] is not None, k[1] or ())):
            p, blk = key
            a = pose_of(poses, p)[0]
            bs = 'B-' if blk is None else 'B=' + ','.join(map(str, blk))
            if key in empty:
                ins, terms = empty_witness(ctx_R[key])
                f.write('%d %s | E %s %s\n' % (p, bs, ','.join(map(str, ins)),
                        '+'.join('%d@%d' % t for t in terms))); continue
            parts = []
            for b in [a] + sorted(need.get(key, set()) - {a}):
                ss = sups[(key, b)]; rr = R(key, b)
                nent += 1
                parts.append('%d:' % b + '/'.join(
                    '%d,%d,%d,%d,%s' % (k, kr, er, 1 if sr else 0, '+'.join('%d@%d' % t for t in terms))
                    for (k, e, s, terms), (kr, er, sr, _) in zip(ss, rr)))
            f.write('%d %s | %s\n' % (p, bs, ';'.join(parts)))
    print('table entries', nent, file=sys.stderr)

if __name__ == '__main__':
    main()
