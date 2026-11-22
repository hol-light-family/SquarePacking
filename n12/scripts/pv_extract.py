#!/usr/bin/env python3
"""W-F6 extractor (untrusted): historical initial-cover recipes.

Reads Compact/Cases/C<case>/RecipeInitial/{Inputs,Owner*,Data*,Batches/*}.lean
for the six historical cases and writes

  n12/data/cert/pv_owners.txt   case owner grid inside outside
        grid    : 64 | 128 (Lean angles64_cover_kernel / angles128_cover_kernel)
        inside  : x1/y1;x2/y2;...   points as p:q,p:q  (rationals p:q, '-' if empty)
  n12/data/cert/pv_entries.txt  case owner angle idx1,idx2,... target
        one Lean DirectRecipeTable.Spec per line, in Lean order
        (entriesK = entriesK_0 ++ entriesK_1 ++ ...); target = pose id or '-' (none)

With --c898 the same records are written for Cases/C898 (inputs in DirectInitial/Inputs.lean,
batches RecipeInitial/BatchKK_JJ.lean) to n12/data/cert/pv898_owners.txt / pv898_entries.txt.

Usage: python3 n12/scripts/pv_extract.py [--c898]
"""
import os, re, glob

ROOT = "n12/ext/jatloe/Lean/Proofs/N12-jatloe/Compact/Cases"
OUT = "n12/data/cert"
CASES = ["701", "713", "717", "973", "978", "979"]


def rat(tok):
    tok = tok.strip()
    while tok.startswith("(") and tok.endswith(")"):
        tok = tok[1:-1].strip()
    m = re.fullmatch(r"(-?\d+)\s*/\s*(\d+)", tok)
    if m:
        return "%s:%s" % (m.group(1), m.group(2))
    assert re.fullmatch(r"-?\d+", tok), tok
    return "%s:1" % tok


def points(text):
    # text: [ (a,b), (c,d) ]  with a,b possibly (p/q)
    text = text.strip()
    assert text.startswith("[") and text.endswith("]"), text
    body = text[1:-1].strip()
    if not body:
        return []
    pts = []
    depth = 0
    cur = ""
    for ch in body:
        if ch == "(":
            depth += 1
        if ch == ")":
            depth -= 1
        if ch == "," and depth == 0:
            pts.append(cur)
            cur = ""
        else:
            cur += ch
    pts.append(cur)
    res = []
    for p in pts:
        p = p.strip()
        assert p.startswith("(") and p.endswith(")"), p
        inner = p[1:-1]
        depth = 0
        for i, ch in enumerate(inner):
            if ch == "(":
                depth += 1
            elif ch == ")":
                depth -= 1
            elif ch == "," and depth == 0:
                res.append((rat(inner[:i]), rat(inner[i + 1:])))
                break
        else:
            raise ValueError(p)
    return res


def main():
    import sys
    c898 = "--c898" in sys.argv
    owners = []
    entries = []
    for case in (["898"] if c898 else CASES):
        d = os.path.join(ROOT, "C" + case, "RecipeInitial")
        inp = open(os.path.join(ROOT, "C898", "DirectInitial", "Inputs.lean") if c898
                   else os.path.join(d, "Inputs.lean")).read()
        ins = {int(k): points(v) for k, v in re.findall(r"def inside(\d+) : List \(ℚ × ℚ\) := (\[.*\])", inp)}
        outs = {int(k): points(v) for k, v in re.findall(r"def outside(\d+) : List \(ℚ × ℚ\) := (\[.*\])", inp)}
        grid = {}
        for fn in glob.glob(os.path.join(d, "*.lean")):
            t = open(fn).read()
            for k, body in re.findall(r"theorem owner(\d+)_checked : owner\d+\.Check :=(.*?)(?:\n\n|\Z)", t, re.S):
                m = re.search(r"angles(64|128)_cover_kernel", body)
                assert m, (fn, k)
                grid[int(k)] = int(m.group(1))
        assert sorted(grid) == sorted(ins) == sorted(outs), (case, grid.keys(), ins.keys())
        for k in sorted(grid):
            if c898:
                batches = sorted(glob.glob(os.path.join(d, "Batch%02d_*.lean" % k)),
                                 key=lambda f: int(re.search(r"_(\d+)\.lean$", f).group(1)))
            else:
                batches = sorted(glob.glob(os.path.join(d, "Batches", "Owner%02dBatch*.lean" % k)),
                                 key=lambda f: int(re.search(r"Batch(\d+)\.lean$", f).group(1)))
            assert batches
            angles = []
            for j, fn in enumerate(batches):
                t = open(fn).read()
                assert ("entries%d_%d\n" % (k, j)) in t or ("entries%d_%d " % (k, j)) in t, fn
                recs = re.findall(r"entry(\d+)_(\d+) := ⟨(\d+), \[([0-9, ]*)\], (some (\d+)|none)⟩", t)
                assert recs and len(recs) <= 8, fn
                for (kk, ii, a, idx, tgt, tid) in recs:
                    assert int(kk) == k
                    idx = [int(x) for x in idx.replace(" ", "").split(",") if x != ""]
                    entries.append((case, k, int(a), idx, tid if tgt != "none" else "-"))
                    angles.append(int(a))
            g = grid[k]
            exp = list(range(0, 64)) if g == 64 else list(range(64, 192))
            assert angles == exp, (case, k, angles[:5], len(angles))
            fmt = lambda ps: ";".join("%s,%s" % p for p in ps) if ps else "-"
            owners.append((case, k, g, fmt(ins[k]), fmt(outs[k])))
    pre = "pv898" if c898 else "pv"
    with open(os.path.join(OUT, pre + "_owners.txt"), "w") as f:
        for o in owners:
            f.write("%s %d %d %s %s\n" % o)
    with open(os.path.join(OUT, pre + "_entries.txt"), "w") as f:
        for (c, k, a, idx, t) in entries:
            f.write("%s %d %d %s %s\n" % (c, k, a, ",".join(map(str, idx)) if idx else "-", t))
    print("owners", len(owners), "entries", len(entries),
          "empty", sum(1 for e in entries if e[4] == "-"))


if __name__ == "__main__":
    main()
