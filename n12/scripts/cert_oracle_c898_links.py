#!/usr/bin/env python3
"""Untrusted oracle: RelaxationHints for the 927 C898 relaxation links (Lean synthesises
them at elaboration by relaxation_hints% and does not store them).  For each target row of
the target pose: constant / copy / single / pair on the source pose rows, exactly as the HOL
checker cr_hint_check recomputes them (n12/scripts/cert_oracle_height.py functions).
Output n12/data/cert/c898_link_hints.txt:  i | h;h;...   (k | c<i> | s<i> | p<i>.<j>)
"""
import os, sys, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import cert_oracle_height as H

OUT = "n12/data/cert"


def hint(base, t):
    if H.const_check(t):
        return "k"
    for i, r in enumerate(base):
        if r == t:
            return "c%d" % i
    for i, r in enumerate(base):
        if H.single_check(r, t):
            return "s%d" % i
    for i, j in itertools.permutations(range(len(base)), 2):
        if H.rs_check(base[i], base[j], t):
            return "p%d.%d" % (i, j)
    return None


def main():
    rows, poses = {}, {}
    for l in open(OUT + "/c898_rows.txt"):
        p = l.split()
        rows[int(p[0])] = (int(p[1]), int(p[2]), int(p[3]), p[4] == "1")
    for l in open(OUT + "/c898_poses.txt"):
        p = l.split()
        poses[int(p[0])] = (int(p[1]), [int(x) for x in p[2].split(",")] if len(p) > 2 else [])
    row = lambda i: rows.get(i, H.ZERO)
    out, stats = [], {}
    for l in open(OUT + "/c898_links.txt"):
        i, s, g = map(int, l.split())
        base = [row(r) for r in poses[s][1]]
        hs = []
        for r in poses[g][1]:
            h = hint(base, row(r))
            assert h is not None, (i, s, g, r)
            stats[h[0]] = stats.get(h[0], 0) + 1
            hs.append(h)
        out.append("%d | %s" % (i, ";".join(hs)))
    open(OUT + "/c898_link_hints.txt", "w").write("\n".join(out) + "\n")
    print("links", len(out), stats)


if __name__ == "__main__":
    os.chdir(".")
    main()
