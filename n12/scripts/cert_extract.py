#!/usr/bin/env python3
"""Extract the historical certificate data (C701/713/717/973/978/979) from the
Lean sources into compact text files under n12/data/cert/.  Untrusted: everything
written here is re-checked in HOL.

Outputs (n12/data/cert/):
  hist_rows.txt     id x y c strict denPred           (decoded raw / B / M / P / tree nodes)
  hist_poses.txt    id angle r1,r2,...                 (pose lines + tree nodes)
  hist_domains.txt  case name id1,id2,...              (all continuousScoutCKDomainA_B lists)
  hist_stages.txt   case step srcDom nbrDom tgtDom nplans
  hist_plans/CK_SNN.txt  one plan per line:
        src block tgt | hint ; hint ; ...
     block: '-' = none, '' after '=' ... encoded as  B=r1,r2  or  B=  (some [])  or B-  (none)
     tgt: '-' for an empty plan
     hint: d:<rh>  (direct)   b:<rh>,<rh>,...  (block)
     rh  : k (constant) | c<i> (copy) | s<i> (single) | p<i>.<j> (pair)
Usage: n12/scripts/cert_extract.py
"""
import os, re, sys, glob

ROOT = "n12/ext/jatloe/Lean/Proofs/N12-jatloe/Compact"
OUT = "n12/data/cert"
ROWCOUNT, POSECOUNT = 114465, 28235
CASES = ["701", "713", "717", "973", "978", "979"]


def strings_of(text):
    return re.findall(r'"([^"]*)"', text, re.S)


def decode_rows(lines, rows):
    for line in lines:
        line = line.strip()
        if not line:
            continue
        kind, payload = line.split(":", 1)
        if kind == "B":
            keys, bounds, mask = payload.split(";")
            keys = [int(k) for k in keys.split(",")]
            fields = bounds.split("|")
            mask = int(mask)
            assert len(keys) == 4 and len(fields) == 4 and mask < 16
            for i in range(4):
                n, dp = fields[i].split(",")
                n, dp = int(n), int(dp)
                den = dp + 1
                st = (mask >> i) & 1
                r = [(den, 0, -n), (-den, 0, n), (0, den, -n), (0, -den, n)][i]
                put(rows, keys[i], (r[0], r[1], r[2], st, dp))
        elif kind in ("M", "P"):
            f = payload.split(";")
            if kind == "M":
                ids, normal, bounds, dens, mask = f
                scales = "1,1"
            else:
                ids, normal, scales, bounds, dens, mask = f
            lid, uid = [int(t) for t in ids.split(",")]
            x, y = [int(t) for t in normal.split(",")]
            ls, us = [int(t) for t in scales.split(",")]
            assert ls > 0 and us > 0
            lo, hi = [int(t) for t in bounds.split(",")]
            ld, ud = [int(t) for t in dens.split(",")]
            mask = int(mask)
            assert mask < 4
            put(rows, lid, (ls * x, ls * y, -lo, mask & 1, ld))
            put(rows, uid, (-(us * x), -(us * y), hi, (mask >> 1) & 1, ud))
        else:
            x, y, c, s, d = payload.split(",")
            assert s in ("true", "false")
            put(rows, int(kind), (int(x), int(y), int(c), 1 if s == "true" else 0, int(d)))


def put(tbl, k, v):
    assert k not in tbl, ("duplicate", k)
    tbl[k] = v


def main():
    os.makedirs(OUT + "/hist_plans", exist_ok=True)
    # ---------------- rows
    rows = {}
    for fn in sorted(glob.glob(ROOT + "/HistoricalData/RowsChunks/*.lean")):
        for s in strings_of(open(fn).read()):
            decode_rows(s.split("\n"), rows)
    shared = open(ROOT + "/HistoricalData/SharedRows.lean").read()
    for m in re.finditer(r"\.node (\d+) \(⟨(-?\d+),(-?\d+),(-?\d+),(true|false)⟩,(\d+)\)", shared):
        put(rows, int(m.group(1)), (int(m.group(2)), int(m.group(3)), int(m.group(4)),
                                    1 if m.group(5) == "true" else 0, int(m.group(6))))
    assert max(rows) < ROWCOUNT
    with open(OUT + "/hist_rows.txt", "w") as f:
        for k in sorted(rows):
            f.write("%d %d %d %d %d %d\n" % ((k,) + rows[k]))
    # ---------------- poses
    poses = {}
    for fn in sorted(glob.glob(ROOT + "/HistoricalData/PosesChunks/*.lean")):
        for s in strings_of(open(fn).read()):
            for line in s.split("\n"):
                line = line.strip()
                if not line:
                    continue
                k, payload = line.split(":")
                a, rs = payload.split(";")
                put(poses, int(k), (int(a), [int(r) for r in rs.split(",")] if rs else []))
    sp = open(ROOT + "/HistoricalData/SharedPoses.lean").read()
    for m in re.finditer(r"\.node (\d+) \((\d+), \[([\d,]*)\]\)", sp):
        put(poses, int(m.group(1)), (int(m.group(2)),
                                     [int(r) for r in m.group(3).split(",")] if m.group(3) else []))
    assert max(poses) < POSECOUNT
    for k, (a, rs) in poses.items():
        assert a < 192, (k, a)
        for r in rs:
            assert r < ROWCOUNT
    with open(OUT + "/hist_poses.txt", "w") as f:
        for k in sorted(poses):
            a, rs = poses[k]
            f.write("%d %d %s\n" % (k, a, ",".join(map(str, rs))))
    # ---------------- domains
    doms = {}
    srcs = [ROOT + "/Cases/C713/SharedDomains.lean"] + \
        [ROOT + "/Preservation/C%s.lean" % c for c in CASES if c != "713"]
    for fn in srcs:
        t = open(fn).read()
        for m in re.finditer(r"def (continuousScout(\d+)Domain(\d+_\d+))Ids : List \(Fin (?:HistoricalData\.)?poseCount\) := \[([\d,\s]*)\]", t):
            doms[(m.group(2), m.group(3))] = [int(x) for x in re.sub(r"\s","",m.group(4)).split(",") if x]
    with open(OUT + "/hist_domains.txt", "w") as f:
        for (c, n) in sorted(doms):
            f.write("%s %s %s\n" % (c, n, ",".join(map(str, doms[(c, n)]))))
    # ---------------- plans
    rec_re = re.compile(r"^\s*plan\d+ \((\d+),(none|\(some \[([\d,]*)\]\)),(\d+)\) \[(.*)\],?\s*$")
    emp_re = re.compile(r"^\s*plan\d+ empty\((\d+)\),?\s*$")
    stages = []
    total = 0
    for c in CASES:
        d = ROOT + "/Cases/C%s/DirectPruning" % c
        steps = sorted(set(re.match(r"Step(\d+)\.lean", os.path.basename(x)).group(1)
                           for x in glob.glob(d + "/Step??.lean")))
        for st in steps:
            meta = open(d + "/Step%s.lean" % st).read()
            m = re.search(r"⟨continuousScout\d+Domain(\d+_\d+)Ids, continuousScout\d+Domain(\d+_\d+)Ids, "
                          r"continuousScout\d+Domain(\d+_\d+)Ids, plans⟩", meta)
            sdom, ndom, tdom = m.groups()
            batches = re.findall(r"C%sDirectPruning\.Step%sBatch(\d+)\.plans" % (c, st), meta.split("def plans")[1].split("theorem")[0])
            out = []
            for b in batches:
                for line in open(d + "/Step%sBatch%s.lean" % (st, b)):
                    if not re.match(r"^\s*plan\d+", line):
                        continue
                    line = line.rstrip()
                    if line.endswith("]]") or line.endswith(")]"):
                        if line.endswith(")]") and "empty(" not in line:
                            pass
                        else:
                            line = line[:-1]
                    me = emp_re.match(line)
                    if me:
                        out.append("%s B= - |" % me.group(1))
                        continue
                    mr = rec_re.match(line)
                    assert mr, line[:200]
                    src, blk, blkrows, tgt, hints = mr.groups()
                    bt = "B-" if blk == "none" else "B=" + blkrows
                    out.append("%s %s %s | %s" % (src, bt, tgt, enc_hints(hints)))
            src_ids = [int(l.split()[0]) for l in out]
            assert src_ids == doms[(c, sdom)], (c, st, "sources mismatch")
            with open(OUT + "/hist_plans/C%s_S%s.txt" % (c, st), "w") as f:
                f.write("\n".join(out) + "\n")
            stages.append((c, st, sdom, ndom, tdom, len(out)))
            total += len(out)
    with open(OUT + "/hist_stages.txt", "w") as f:
        for s in stages:
            f.write("%s %s %s %s %s %d\n" % s)
    print("rows", len(rows), "poses", len(poses), "domains", len(doms), "stages", len(stages), "plans", total)


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


def enc_hints(s):
    out = []
    i = 0
    s = s.strip()
    # top level split on ", ." respecting brackets
    depth = 0
    cur = ""
    for ch in s:
        if ch in "([":
            depth += 1
        elif ch in ")]":
            depth -= 1
        if ch == "," and depth == 0:
            out.append(cur.strip())
            cur = ""
        else:
            cur += ch
    if cur.strip():
        out.append(cur.strip())
    res = []
    for h in out:
        m = re.match(r"^\.direct \((.*)\)$", h)
        if m:
            res.append("d:" + enc_rh(m.group(1)))
            continue
        m = re.match(r"^\.block \[(.*)\]$", h)
        if m:
            inner = [x for x in m.group(1).split(",") if x.strip()]
            res.append("b:" + ",".join(enc_rh(x) for x in inner))
            continue
        raise ValueError(h)
    return ";".join(res)


if __name__ == "__main__":
    os.chdir(".")
    main()
