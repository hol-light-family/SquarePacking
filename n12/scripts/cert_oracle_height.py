#!/usr/bin/env python3
"""Untrusted oracle for the 108 C713 height records (n12/data/cert/c713_height.txt).

Lean checks each record by planar vertex enumeration (PlanarVertexSparse.UnorderedCheck
base [] targets).  The base polygon has no forbidden blocks, so every target row that is
nonnegative on it has a 2-D Farkas certificate with at most two rows (LP duality), and an
empty polygon has a <= 3-row infeasibility certificate (Helly).  This script finds, per
target row, a RelaxationHints hint (constant / copy / single / pair, exactly as the HOL
checker cr_hint_check recomputes them) or an EmptyContext witness on
(opposite target :: base) (BlockedTarget.Hint.impossible); HOL re-checks everything.

base = (cut :: source pose rows) ++ containerRows;  targets = rows of the target pose,
or Lean's [<0,0,-1,false>] for an empty outcome.
Output n12/data/cert/c713_height_hints.txt:  i | h;h;...   with
   h = d:k | d:c<i> | d:s<i> | d:p<i>.<j> | i:<i>,<j>,..:<w>@<i>,...
"""
import os, itertools, math

OUT = "n12/data/cert"


def read_rows():
    rows = {}
    for l in open(OUT + "/hist_rows.txt"):
        p = l.split()
        rows[int(p[0])] = (int(p[1]), int(p[2]), int(p[3]), p[4] == "1")
    return rows


def read_poses():
    poses = {}
    for l in open(OUT + "/hist_poses.txt"):
        p = l.split()
        poses[int(p[0])] = (int(p[1]), [int(x) for x in p[2].split(",")] if len(p) > 2 else [])
    return poses


ZERO = (0, 0, 0, False)
ONE = (0, 0, 1, True)
CONTAINER = [(1, 0, 0, False), (-1, 0, 4, False), (0, 1, 0, False), (0, -1, 4, False)]


def rowat(rws, i):
    return rws[i] if i < len(rws) else ZERO


def csum(rws, terms):
    if not terms:
        return ZERO
    tl = csum(rws, terms[1:])
    w, i = terms[0]
    r = rowat(rws, i)
    return (w * r[0] + tl[0], w * r[1] + tl[1], w * r[2] + tl[2], (w > 0 and r[3]) or tl[3])


def tworow(wl, wr, sc, a, b, t):
    return (wl >= 0 and wr >= 0 and sc > 0 and wl * a[0] + wr * b[0] == sc * t[0] and
            wl * a[1] + wr * b[1] == sc * t[1] and wl * a[2] + wr * b[2] == sc * t[2] and
            ((not t[3]) or (wl > 0 and a[3]) or (wr > 0 and b[3])))


def cert(terms, scale, rws, t):
    return all(w >= 0 for w, _ in terms) and tworow(1, 0, scale, csum(rws, terms), ZERO, t)


def cramer(a, b, x, y):
    det = a[0] * b[1] - a[1] * b[0]
    sg = 1 if det >= 0 else -1
    return sg * (x * b[1] - y * b[0]), sg * (a[0] * y - a[1] * x), sg * det


def rs_check(a, b, t):
    l, m, sc = cramer(a, b, t[0], t[1])
    return cert([(l, 0), (m, 1), (sc * t[2] - l * a[2] - m * b[2], 2)], sc, [a, b, ONE], t)


def single_check(src, t):
    pivot = src[1] if src[0] == 0 else src[0]
    comp = t[1] if src[0] == 0 else t[0]
    scale = abs(pivot)
    w = -comp if pivot < 0 else comp
    return cert([(w, 0), (scale * t[2] - w * src[2], 1)], scale, [src, ONE], t)


def const_check(t):
    return cert([(t[2], 0)], 1, [ONE], t)


def opposite(r):
    return (-r[0], -r[1], -r[2], not r[3])


def empty_check(rws, ins, terms):
    if not all(w >= 0 for w, _ in terms) or not all(i in ins for _, i in terms):
        return False
    s = csum(rws, terms)
    return s[0] == 0 and s[1] == 0 and (s[2] < 0 or (s[2] <= 0 and s[3]))


def find_hint(base, t):
    if const_check(t):
        return "d:k"
    for i, r in enumerate(base):
        if r == t:
            return "d:c%d" % i
    for i, r in enumerate(base):
        if single_check(r, t):
            return "d:s%d" % i
    for i, j in itertools.combinations(range(len(base)), 2):
        if rs_check(base[i], base[j], t):
            return "d:p%d.%d" % (i, j)
        if rs_check(base[j], base[i], t):
            return "d:p%d.%d" % (j, i)
    rws = [opposite(t)] + base
    w = find_empty(rws)
    if w:
        ins, terms = w
        assert empty_check(rws, ins, terms)
        return "i:%s:%s" % (",".join(map(str, ins)), ",".join("%d@%d" % x for x in terms))
    return None


def det(a, b):
    return a[0] * b[1] - a[1] * b[0]


def find_empty(rws):
    n = len(rws)
    for i, j, k in itertools.combinations(range(n), 3):
        a, b, c = rws[i], rws[j], rws[k]
        lam = [det(b, c), det(c, a), det(a, b)]
        for sg in (1, -1):
            l = [sg * x for x in lam]
            if all(x >= 0 for x in l) and any(x > 0 for x in l):
                terms = [(l[0], i), (l[1], j), (l[2], k)]
                terms = [t for t in terms if t[0] > 0]
                g = 0
                for w, _ in terms:
                    g = math.gcd(g, w)
                terms = [(w // g, x) for w, x in terms]
                if empty_check(rws, [t[1] for t in terms], terms):
                    return [t[1] for t in terms], terms
    for i, j in itertools.combinations(range(n), 2):
        a, b = rws[i], rws[j]
        if det(a, b) == 0:
            # antiparallel: weights |b|, |a| along a common axis
            ax = abs(a[0]) + abs(a[1]); bx = abs(b[0]) + abs(b[1])
            if ax and bx:
                terms = [(bx, i), (ax, j)]
                if empty_check(rws, [i, j], terms):
                    return [i, j], terms
    return None


def main():
    rows = read_rows()
    poses = read_poses()

    def row(i):
        return rows.get(i, ZERO)

    def pose(i):
        return poses.get(i, (0, []))

    out = []
    stats = {}
    for l in open(OUT + "/c713_height.txt"):
        p = l.split()
        i, src = int(p[0]), int(p[1])
        cx, cy, cc, cs = [int(x) for x in p[2].split(",")]
        cut = (cx, cy, cc, cs == 1)
        base = [cut] + [row(r) for r in pose(src)[1]] + CONTAINER
        targets = [(0, 0, -1, False)] if p[3] == "-" else [row(r) for r in pose(int(p[3]))[1]]
        hs = []
        for t in targets:
            h = find_hint(base, t)
            assert h is not None, (i, t)
            stats[h.split(":")[0] + ":" + h.split(":")[1][0]] = stats.get(h.split(":")[0] + ":" + h.split(":")[1][0], 0) + 1
            hs.append(h)
        out.append("%d | %s" % (i, ";".join(hs)))
    with open(OUT + "/c713_height_hints.txt", "w") as f:
        f.write("\n".join(out) + "\n")
    print("records", len(out), "hint kinds", stats)


if __name__ == "__main__":
    os.chdir(".")
    main()
