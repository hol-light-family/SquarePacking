#!/usr/bin/env python3
"""Extract the 37 hull-conflict certificates (Jatloe HullData.lean) as OCaml data."""
import re
from fractions import Fraction as Fr
src = open('n12/ext/jatloe/Lean/Proofs/N12-jatloe/source/S12/HullData.lean').read()
raw = open('n12/ext/jatloe/Lean/Proofs/N12-jatloe/source/S12/RawData.lean').read()
pairs = re.search(r'conflictingPairs : List \(Nat × Nat\) := \[(.*?)\]', raw).group(1)
pairs = [tuple(map(int, p)) for p in re.findall(r'\((\d+),(\d+)\)', pairs)]
num = r'\(?-?\d+(?:/\d+)?\)?'
def fr(s): return Fr(s.replace('(', '').replace(')', ''))
def pts(L):
    return [(fr(a), fr(b)) for a, b in re.findall(r'\(\s*(' + num + r')\s*,\s*(' + num + r')\s*\)', L)]
def ocq(f): return 'qn"%s"' % f
def ocp(p): return '(%s,%s)' % (ocq(p[0]), ocq(p[1]))
certs = []
for m in re.finditer(r'def hullCert(\d+) : HullConflictCertificate := ⟨\[(.*?)\],\[(.*?)\],⟨(.*?)⟩,⟨(.*?)⟩⟩\n', src):
    i, L, R, T1, T2 = m.groups()
    def tri(T):
        # split at top-level commas
        parts, depth, cur = [], 0, ''
        for ch in T:
            if ch == '(':
                depth += 1
            elif ch == ')':
                depth -= 1
            if ch == ',' and depth == 0:
                parts.append(cur); cur = ''
            else:
                cur += ch
        parts.append(cur)
        assert len(parts) == 6, (i, T)
        ps = [pts(x)[0] for x in parts[:4]]
        st = [fr(x) for x in parts[4:]]
        return ps, st
    certs.append((int(i), pts(L), pts(R), tri(T1), tri(T2)))
certs.sort()
assert len(certs) == 37 == len(pairs)
out = ['let HULL_CERTS = [']
for (i, L, R, (p1, st1), (p2, st2)), (mm, nn) in zip(certs, pairs):
    def t(ps, st):
        return '([%s], %s, %s, %s)' % ('; '.join(ocp(p) for p in ps[:3]), ocp(ps[3]), ocq(st[0]), ocq(st[1]))
    out.append('  (%d, %d, [%s], [%s], %s, %s);' % (mm, nn, '; '.join(ocp(p) for p in L),
               '; '.join(ocp(p) for p in R), t(p1, st1), t(p2, st2)))
out.append('];;')
print('\n'.join(out))
