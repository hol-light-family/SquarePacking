#!/usr/bin/env python3
"""Print p2 files considered done (exist, not in inprogress) in dependency order of the
Lean closure, plus non-module helper files first. Usage: done_order.py > list"""
import sys, os, json
sys.argv = ['x']
exec(open('n12/scripts/ready.py').read().split('PACK =')[0])
mods = {hname(m) for m in order}
files = [x[:-3] for x in os.listdir(P2) if x.endswith('.ml')]
seen = set()
for m in order:
    h = hname(m)
    if h in done and h not in seen and os.path.exists(P2 + h + '.ml'):
        seen.add(h); print(h)
for f in sorted(files):
    if f not in mods and f not in inprog: print('#extra', f)
