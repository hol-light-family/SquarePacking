import re, glob, sys
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
def conv(typ, rest):
    if typ == 'hull':
        P = pts(rest); return P[:3], [P[3]]
    if typ == 'four':
        t = re.match(r'⟨(\w+),(\w+),(\w+)⟩ fourDatum(\d+)', rest).groups()
        T = transform(B(t[0]), B(t[1]), B(t[2]))
        a, b, p, e = four[int(t[3])]
        return [T(a), T(b)], [T(p), T(e)]
    t = re.match(r'⟨⟨(\w+),(\w+),(\w+)⟩,\.(\w+)⟩ \[(.*)\]', rest).groups()
    T = transform(B(t[0]), B(t[1]), B(t[2]))
    ins = []
    for w in t[4].strip('⟨⟩').split('⟩,⟨'):
        parts, depth, cur = [], 0, ''
        for ch in w:
            if ch == '(': depth += 1
            elif ch == ')': depth -= 1
            if ch == ',' and depth == 0: parts.append(cur); cur = ''
            else: cur += ch
        parts.append(cur)
        assert len(parts) == 6, w
        ins += [pts(x)[0] for x in parts[:3]]
    return ins, [T(p) for p in SHORT_OUT[t[3]]]
def dd(L):
    r = []
    for p in L:
        if p not in r: r.append(p)
    return r
q = lambda f: 'nlin_rat "%s"' % f
pl = lambda L: '[' + '; '.join('(%s, %s)' % (q(x), q(y)) for x, y in dd(L)) + ']'
name = sys.argv[1]
# optional: cq.py NAME [LEAN_DIR_REL TAG NAMESPACE]
rel = sys.argv[2] if len(sys.argv) > 2 else 'Compact/Bridge/C981DomainReuse'
TAG = sys.argv[3] if len(sys.argv) > 3 else 'C981DSQ'
NS = sys.argv[4] if len(sys.argv) > 4 else 'N12Compact.C981DomainSubset'
src = open('n12/ext/jatloe/Lean/Proofs/N12-jatloe/%s/%s.lean' % (rel, name)).read()
hdr = ("""(* ========================================================================= *)
(* Port of %s/%s.lean *)
(* (%s): exact inherited local queries.  Each Lean *)
(* checked_local_query is registered with slq_new (SharedLocalQueries.ml):  *)
(* the HOL kernel re-proves the query from its inside / outside points     *)
(* (a .hull query: its three hull points inside, its fourth point outside; *)
(* a .four query: the transformed FourPointDatum A, B inside, P, E outside; *)
(* a .short query: its cluster points inside, the pattern points outside).  *)
(* %s_QUERYn : |- !c1 c2 a b l. &1 < l ==> l <= &1001 / &1000 ==>  *)
(*   a * a + b * b = &1 ==> owalls .. ==> owned .. = set_of_list (bits m)   *)
(*   ==> auxown k c1 c2 a b l = set_of_list owned ==> F   (LocalQuery.sound) *)
(* ========================================================================= *)

needs "n12/geometry/SharedLocalQueries.ml";;
""" % (rel, name, NS, TAG))
print(hdr)
n = 0
for m in re.finditer(r'checked_local_query (query\w+) := ⟨(\d+),(\d+),(?:\{([\d,]*)\}|∅),\.(\w+) (.*)⟩\n', src):
    qn, mask, kind, owned, typ, rest = m.groups()
    owned = [int(x) for x in (owned or '').split(',') if x]
    ins, outs = conv(typ, rest)
    print('(* Lean: %s *)' % qn)
    if TAG == 'HOQ':   # historical queries: registered under their Lean number (slq_hist)
        print('let %s_%s = slq_hist %s (%s, %s, [%s],\n  %s,\n  %s);;' % (TAG, qn.upper(), qn[5:], mask, kind, '; '.join(map(str, owned)), pl(ins), pl(outs)))
    else:
        print('let %s_%s = slq_new (%s, %s, [%s],\n  %s,\n  %s);;' % (TAG, qn.upper(), mask, kind, '; '.join(map(str, owned)), pl(ins), pl(outs)))
    n += 1
sys.stderr.write('%s: %d queries, lean lines with checked_local_query: %d\n' % (name, n, src.count('checked_local_query ')))
