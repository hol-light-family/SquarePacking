#!/usr/bin/env python3
"""Static check: every identifier a p2 file uses that is defined (let NAME) in another p2 file
must be defined in a file in its `needs` closure."""
import re, os, glob
P2='n12/geometry/'
defs={}; src={}
for f in glob.glob(P2+'*.ml'):
    n=os.path.basename(f); s=open(f).read(); src[n]=s
    for m in re.finditer(r'^let\s+(?:rec\s+)?([A-Za-z_][A-Za-z0-9_\']*)', s, re.M):
        defs.setdefault(m.group(1), set()).add(n)
    for m in re.finditer(r'^\s+and\s+([A-Za-z_][A-Za-z0-9_\']*)\s*=', s, re.M):
        defs.setdefault(m.group(1), set()).add(n)
def needs(n):
    return [os.path.basename(x) for x in re.findall(r'needs\s+"n12/geometry/([^"]+)"', src[n])]
closure={}
def clo(n, stack=()):
    if n in closure: return closure[n]
    r={n}
    for d in needs(n):
        if d in src and d not in stack: r|=clo(d, stack+(n,))
    closure[n]=r; return r
bad=0
for n in sorted(src):
    c=clo(n); s=re.sub(r'\(\*.*?\*\)','',src[n],flags=re.S)
    toks=set(re.findall(r'[A-Za-z_][A-Za-z0-9_\']*', s))
    for t in sorted(toks):
        if t in defs and n not in defs[t] and not (defs[t] & c) and len(t)>3:
            print(f'{n}: uses {t} from {sorted(defs[t])}'); bad+=1
print(bad, 'problems')
