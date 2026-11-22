#!/usr/bin/env python3
"""Untrusted search for COVER_TAC.

Input (JSON): {"region": [[a,b,c,strict], ...],      a*X + b*Y + c >= 0 (or > 0)
               "tris": [[[a,b,c],[a,b,c],[a,b,c]], ...]}  weights, all usable
Output (JSON): a tree
   ["empty"]                      region is empty
   ["tri", k]                     all weights of triangle k are >= 0 on the region
   ["split", [a,b,c], T1, T2]     T1 under a*X+b*Y+c >= 0, T2 under < 0
Coefficients are strings "p/q".
"""
import json
import sys
from fractions import Fraction as Fr

import numpy as np
from scipy.optimize import linprog

EPS = 1e-9


def lp_min(obj, region):
    """minimise obj over the closure of region; None if infeasible."""
    A, b = [], []
    for (a, bb, c, _s) in region:
        A.append([-float(a), -float(bb)])
        b.append(float(c))
    res = linprog([float(obj[0]), float(obj[1])], A_ub=np.array(A) if A else None,
                  b_ub=np.array(b) if b else None, bounds=[(None, None), (None, None)],
                  method='highs')
    if res.status == 2:
        return None
    if res.status == 3:
        return -np.inf
    return res.fun + float(obj[2])


def empty(region):
    # check emptiness with strictness margin: maximise t s.t. constraints - t*strict >= 0
    A, b = [], []
    for (a, bb, c, s) in region:
        A.append([-float(a), -float(bb), 1.0 if s else 0.0])
        b.append(float(c))
    res = linprog([0, 0, -1], A_ub=np.array(A), b_ub=np.array(b),
                  bounds=[(None, None), (None, None), (None, 1.0)], method='highs')
    if res.status == 2:
        return True
    return res.status == 0 and -res.fun <= EPS and any(s for *_x, s in region)


def search(region, tris, depth, excl=frozenset()):
    if empty(region):
        return ["empty"]
    best = None
    for k, t in enumerate(tris):
        if k in excl:
            continue
        mins = [lp_min(w, region) for w in t]
        if any(m is None for m in mins):
            return ["empty"]
        if all(m >= -EPS for m in mins):
            return ["tri", k]
        worst = min(mins)
        if best is None or worst > best[0]:
            best = (worst, k, mins)
    if depth == 0 or best is None:
        raise SystemExit("cover_search: no cover found")
    _, k, mins = best
    i = min(range(3), key=lambda j: mins[j])
    w = tris[k][i]
    pos = region + [(w[0], w[1], w[2], False)]
    neg = region + [(-w[0], -w[1], -w[2], True)]
    return ["split", [str(x) for x in w], search(pos, tris, depth - 1, excl),
            search(neg, tris, depth - 1, excl | {k})]


def main():
    d = json.load(open(sys.argv[1]))
    region = [(Fr(a), Fr(b), Fr(c), bool(s)) for a, b, c, s in d["region"]]
    tris = [[tuple(Fr(x) for x in w) for w in t] for t in d["tris"]]
    tree = search(region, tris, int(d.get("depth", 12)))
    json.dump(tree, open(sys.argv[2], "w"))


if __name__ == '__main__':
    main()
