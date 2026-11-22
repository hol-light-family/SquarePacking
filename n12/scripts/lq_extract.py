#!/usr/bin/env python3
"""Extract Jatloe's 1703 local queries as OCaml data: for each query the mask, kind,
aux-owned set, and the inside/outside points its certificate uses (untrusted hints;
HOL re-derives every membership and the contradiction)."""
import re, glob
from fractions import Fraction as Fr
base = 'n12/ext/jatloe/Lean/Proofs/N12-jatloe/source/S12/'
num = r'\(?-?\d+(?:/\d+)?\)?'
PT = r'\(\s*(' + num + r')\s*,\s*(' + num + r')\s*\)'
def fr(s): return Fr(s.replace('(', '').replace(')', ''))
def pts(s): return [(fr(a), fr(b)) for a, b in re.findall(PT, s)]
def transform(sw, rx, ry):
    def f(p):
        u, v = (p[1], p[0]) if sw else p
        return (4 - u if rx else u, 4 - v if ry else v)
    return f
B = lambda s: s == 'true'
four = {}
for f in glob.glob(base + 'FourPointData/*.lean'):
    for m in re.finditer(r'def fourDatum(\d+) : FourPointDatum := ⟨(' + PT + r'),(' + PT + r'),(' + PT + r'),(' + PT + r'),', open(f).read()):
        g = m.groups()
        four[int(g[0])] = [pts(g[1])[0], pts(g[4])[0], pts(g[7])[0], pts(g[10])[0]]
SHORT_OUT = {'fiveLeft': [(1, Fr(87, 50)), (Fr(33, 20), Fr(47, 20)), (2, Fr(87, 50))],
             'fiveRight': [(1, Fr(87, 50)), (Fr(33, 20), Fr(47, 20)), (2, Fr(87, 50))],
             'six': [(1, Fr(8, 5)), (1, Fr(12, 5)), (Fr(33, 20), Fr(33, 20))]}
src = "".join(open(f).read() for f in sorted(glob.glob(base + 'LocalQueryDataChunks/*.lean')))
out = []
for m in re.finditer(r'def localQuery(\d+) : LocalQuery := ⟨(\d+),(\d+),(?:\{([\d,]*)\}|∅),\.(\w+) (.*)⟩\n', src):
    i, mask, kind, owned, typ, rest = m.groups()
    owned = owned or ''
    owned = [int(x) for x in owned.split(',') if x]
    if typ == 'hull':
        P = pts(rest)
        ins, outs = P[:3], [P[3]]
    elif typ == 'four':
        t = re.match(r'⟨(\w+),(\w+),(\w+)⟩ fourDatum(\d+)', rest).groups()
        T = transform(B(t[0]), B(t[1]), B(t[2]))
        a, b, p, e = four[int(t[3])]
        ins, outs = [T(a), T(b)], [T(p), T(e)]
    else:
        t = re.match(r'⟨⟨(\w+),(\w+),(\w+)⟩,\.(\w+)⟩ \[(.*)\]', rest).groups()
        T = transform(B(t[0]), B(t[1]), B(t[2]))
        ins = []
        for w in t[4].strip('⟨⟩').split('⟩,⟨'):
            parts, depth, cur = [], 0, ''
            for ch in w:
                if ch == '(':
                    depth += 1
                elif ch == ')':
                    depth -= 1
                if ch == ',' and depth == 0:
                    parts.append(cur); cur = ''
                else:
                    cur += ch
            parts.append(cur)
            assert len(parts) == 6, w
            ins += [pts(x)[0] for x in parts[:3]]
        outs = [T(p) for p in SHORT_OUT[t[3]]]
    def dd(L):
        r = []
        for p in L:
            if p not in r: r.append(p)
        return r
    q = lambda f: 'qn"%s"' % f
    pl = lambda L: '[' + '; '.join('(%s,%s)' % (q(x), q(y)) for x, y in dd(L)) + ']'
    out.append('  (%s, %s, %s, [%s], %s, %s);' % (i, mask, kind, '; '.join(map(str, owned)), pl(ins), pl(outs)))
print('let qn = nlin_rat;;\nlet LOCAL_QUERIES = [')
print('\n'.join(out))
print('];;')
