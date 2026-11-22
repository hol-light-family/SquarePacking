# generate HOL ports of Compact/Cases/CK/EntryQueryNN.lean (per-case local query aliases / literal queries)
# usage: cq_entry.py CASE NN   -> n12/geometry/EntryQueryNN.ml (hname from ready.py) ; prints counts
import re, sys
sys.argv, args = [sys.argv[0]], sys.argv[1:]
src_cq = open('n12/scripts/gen/cq_ho.py').read().split('name = sys.argv[1]')[0]
exec(src_cq)
case, nn, out = args
L = 'n12/ext/jatloe/Lean/Proofs/N12-jatloe/Compact/Cases/C%s/EntryQuery%s.lean' % (case, nn)
src = open(L).read()
tag = 'C%sEQ%s_' % (case, nn)
o = ["""(* ========================================================================= *)
(* Port of Compact/Cases/C%(c)s/EntryQuery%(n)s.lean (namespace S12): the exact   *)
(* local queries of the C%(c)s entry.  A Lean alias                             *)
(*   def queryC_j : LocalQuery := localQueryN  with  c%(c)s_query_at ..._checked  *)
(* is slq_select N (the Phase-1 local query N of S12.localQueries re-proved  *)
(* by the kernel; the Lean chunk index is only the decide mechanism), giving  *)
(* (mask, kind, owned, |- LocalQuery.sound); a literal query proved by        *)
(* decide is registered with slq_new from its inside / outside points (.hull:*)
(* three hull points inside, target outside; .four: the transformed          *)
(* FourPointDatum A, B inside, P, E outside), giving |- LocalQuery.sound:      *)
(*   |- !c1 c2 a b l. &1 < l ==> l <= &1001 / &1000 ==> a * a + b * b = &1    *)
(*        ==> owalls .. ==> owned .. = set_of_list (bits m)                   *)
(*        ==> auxown k c1 c2 a b l = set_of_list owned ==> F                  *)
(* Both register the query in LQ_TABLE for the domain checkers.               *)
(* Tag %(t)s.                                                                *)
(* ========================================================================= *)

needs "n12/geometry/Cases_C%(c)s_EntryQueryBase.ml";;
""" % {'c': case, 'n': nn, 't': tag}]
na = nl = 0
for m in re.finditer(r'^def (query\w+) : LocalQuery := (.*)$', src, re.M):
    qn, body = m.groups()
    th = re.search(r'theorem %s_checked : %s\.Check :=\s*\n?\s*(.*)' % (qn, qn), src)
    assert th, qn
    a = re.match(r'localQuery(\d+)$', body.strip())
    if a:
        o.append('(* Lean: %s, %s_checked *)' % (qn, qn))
        o.append('let %s%s = slq_select %s;;' % (tag, qn.upper(), a.group(1)))
        na += 1
        continue
    qq = re.match(r'⟨(\d+),(\d+),(?:\{([\d,]*)\}|∅),\.(\w+) (.*)⟩$', body.strip())
    assert qq, body
    mask, kind, owned, typ, rest = qq.groups()
    assert 'decide' in th.group(1), (qn, th.group(1))
    owned = [int(x) for x in (owned or '').split(',') if x]
    ins, outs = conv(typ, rest)
    o.append('(* Lean: %s, %s_checked *)' % (qn, qn))
    o.append('let %s%s = slq_new (%s, %s, [%s],\n  %s,\n  %s);;' % (tag, qn.upper(), mask, kind, '; '.join(map(str, owned)), pl(ins), pl(outs)))
    nl += 1
assert na + nl == src.count('\ndef '), (na, nl)
assert src.count('\ntheorem ') == na + nl
open('n12/geometry/%s.ml' % out, 'w').write('\n'.join(o) + '\n')
sys.stderr.write('%s: %d aliases, %d literal\n' % (out, na, nl))
