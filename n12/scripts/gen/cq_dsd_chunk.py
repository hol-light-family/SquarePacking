# generate HOL ports of Compact/Cases/CK/EntryQueryChunks/ChunkNN.lean (DirectSingleDomain tables)
# usage: cq_dsd_chunk.py CASE NN HNAME
import re, sys
case, nn, out = sys.argv[1:]
L = 'n12/ext/jatloe/Lean/Proofs/N12-jatloe/Compact/Cases/C%s/EntryQueryChunks/Chunk%s.lean' % (case, nn)
src = open(L).read()
tag = 'C%sEQC%s_' % (case, nn)
hist = sorted(set(int(x) for x in re.findall(r'HistoricalOwnership\.Queries\.query(\d+)_certified', src)))
qfiles = sorted(set(n // 32 for n in hist))
imports = re.findall(r'^import Compact\.HistoricalOwnership\.(Queries\d+)', src, re.M)
o = ["""(* ========================================================================= *)
(* Port of Compact/Cases/C%(c)s/EntryQueryChunks/Chunk%(n)s.lean (namespace S12):*)
(* direct single-owner domains of the C%(c)s entry.  A Lean DirectSingleDomain  *)
(* <mask, lower, upper, allowed, queries> is the dsd record of               *)
(* SmallOwnerDomainThree.ml; its queries are indices: (certified_query%% n)    *)
(* is n (S12.localQueries%(sel)s), HistoricalOwnership.Queries.queryN_certified is   *)
(* slq_hist_idx N (registered by QueriesNNN.ml).  Lean  w_checked : w.Check   *)
(* case%(c)sFamily k  (SmallOwnerDomain.checked / SmallOwnerDomainThree.checked,*)
(* whose private signature lists are just the query signatures) is           *)
(*   dsd_actual / sodt_checked `c%(c)seqb_family` k w : |- hdom fam mask k allowed*)
(* (budget equalities lower / upper, every subset in the interval allowed or *)
(* refuted by a kernel-checked exact query).  Tag %(t)s.                     *)
(* ========================================================================= *)

needs "n12/geometry/Cases_C%(c)s_EntryQueryBase.ml";;
needs "n12/geometry/SmallOwnerDomainThree.ml";;
""" % {'c': case, 'n': nn, 't': tag, 'sel': '; C979SharedSelections.selectedN = query N' if case == '979' else ''}]
if case == '979': o[0] = o[0] + 'needs "n12/geometry/Chunk49.ml";;\n'
for f in qfiles:
    o.append('needs "n12/geometry/Queries%03d.ml";;' % f)
o.append('')
def sets(s):
    r = []
    for t in re.findall(r'\{[\d,]*\}|∅', s):
        r.append('[' + '; '.join(x for x in t.strip('{}∅').split(',') if x) + ']')
    return '[' + '; '.join(r) + ']'
nd = 0
for m in re.finditer(r'^def (\w+) : DirectSingleDomain := ⟨(\d+),(\d+),(\d+),\[([^\]]*)\],\[([^\]]*)\]⟩$', src, re.M):
    name, mask, lo, hi, al, qs = m.groups()
    qi = []
    for q in [x for x in qs.split(",") if x.strip()]:
        a = re.match(r'\(certified_query% (\d+)\)$', q.strip())
        b = re.match(r'N12Compact\.HistoricalOwnership\.Queries\.query(\d+)_certified$', q.strip())
        c = re.match(r'N12Compact\.C979SharedSelections\.selected(\d+)$', q.strip())
        if a: qi.append(a.group(1))
        elif c: qi.append(c.group(1))
        elif b: qi.append('slq_hist_idx %s' % b.group(1))
        else: raise Exception(q)
    th = re.search(r'theorem %s_checked : %s\.Check (\w+) (\d+) :=\n(.*)' % (name, name), src)
    fam, k, body = th.groups()
    assert fam == 'case%sFamily' % case
    three = 'SmallOwnerDomainThree.checked' in body
    assert three or 'SmallOwnerDomain.checked' in body
    o.append('(* Lean: %s *)' % name)
    o.append('let %s%s = { dmask = %s; dlower = %s; dupper = %s;\n  dallowed = %s;\n  dqueries = [%s] };;'
             % (tag.lower(), name, mask, lo, hi, sets(al), '; '.join(qi)))
    o.append('(* Lean: %s_checked *)' % name)
    o.append('let %s%s_CHECKED = %s `c%seqb_family` %s %s%s;;'
             % (tag, name.upper(), 'sodt_checked' if three else 'dsd_actual', case, k, tag.lower(), name))
    nd += 1
assert nd == len(re.findall(r'^def \w+ : DirectSingleDomain', src, re.M)) == src.count('_checked : ')
open('n12/geometry/%s.ml' % out, 'w').write('\n'.join(o) + '\n')
sys.stderr.write('%s: %d domains\n' % (out, nd))
