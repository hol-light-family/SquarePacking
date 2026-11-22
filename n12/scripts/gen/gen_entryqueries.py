import re, sys
case = sys.argv[1]   # e.g. C701
L = 'n12/ext/jatloe/Lean/Proofs/N12-jatloe/Compact/Cases/%s/EntryQueries.lean' % case
s = open(L).read()
cn = case[1:]
fam = 'c%seqb_family' % cn
tag = 'C%sEQS_' % cn
imports = re.findall(r'^import Compact\.HistoricalOwnership\.(Queries\d+)', s, re.M)
imports += ['EntryQuery%s' % x for x in re.findall(r'^import Compact\.Cases\.C713\.EntryQuery(\d+)', s, re.M)]
# C713: query713_k -> Phase-1 index N (alias in EntryQuery00-03) or c713eq_idx k
alias, newq = {}, {}
if case == 'C713':
    for i in range(4):
        t = open('n12/geometry/EntryQuery%02d.ml' % i).read()
        for nm, k, n in re.findall(r'let (C713EQ\d\d_QUERY713_(\d+)) = slq_select (\d+);;', t):
            alias[int(k)] = n
        for nm, k, d in re.findall(r'let (C713EQ\d\d_QUERY713_(\d+)) = slq_new \((.*?)\);;', t, re.S):
            newq[int(k)] = (nm, d)
used_new = []
out = ['(* ========================================================================= *)',
'(* Port of Compact/Cases/%s/EntryQueries.lean (namespace S12): direct       *)' % case,
'(* single-owner domains of the %s entry.  A Lean DirectSingleDomain         *)' % case,
'(* <mask, lower, upper, allowed, queries> is the dsd record of               *)',
'(* SmallOwnerDomainThree.ml; its queries are indices: (certified_query% n)    *)',
'(* is n (S12.localQueries), HistoricalOwnership.Queries.queryN_certified is   *)',
'(* slq_hist_idx N (registered by QueriesNNN.ml).  Lean  w_checked : w.Check   *)',
'(* case%sFamily k  (SmallOwnerDomain.checked, whose private signature lists  *)' % cn,
'(* are just the query signatures) is                                        *)',
'(*   dsd_actual `%s` k w : |- hdom fam mask k allowed               *)' % fam,
'(* (budget equalities lower / upper, every subset in the interval allowed or *)',
'(* refuted by a kernel-checked exact query).  Tag %s.                     *)' % tag,
'(* ========================================================================= *)', '',
'needs "n12/geometry/Cases_%s_EntryQueryBase.ml";;' % case,
'needs "n12/geometry/SmallOwnerDomainThree.ml";;', '']
out += ['needs "n12/geometry/%s.ml";;' % q for q in imports]
out.append('')
defs = re.findall(r'def (single\w+) : DirectSingleDomain := ⟨(\d+),(\d+),(\d+),\[(.*?)\],\[(.*?)\]⟩\n', s)
chk = re.findall(r'theorem (single\w+)_checked : \1\.Check case%sFamily (\d+) :=\n  N12Compact\.(SmallOwnerDomain|SmallOwnerDomainThree)\.checked \1 case%sFamily \2\n' % (cn, cn), s)
assert len(defs) == len(chk) == s.count('DirectSingleDomain :='), (len(defs), len(chk))
ck = {c[0]: c for c in chk}
def qidx(t):
    t = t.strip()
    m = re.fullmatch(r'\(certified_query% (\d+)\)', t)
    if m: return m.group(1)
    m = re.fullmatch(r'N12Compact\.HistoricalOwnership\.Queries\.query(\d+)_certified', t)
    if m: return 'slq_hist_idx %s' % m.group(1)
    m = re.fullmatch(r'⟨query713_(\d+),query713_\1_checked⟩', t)
    if m:
        k = int(m.group(1))
        if k in alias: return alias[k]
        if k < 256:
            assert k in newq, k
            if k not in used_new: used_new.append(k)
        return 'c713eq_idx %d' % k
    raise Exception(t)
for name, mask, lo, hi, allowed, qs in defs:
    al = re.findall(r'\{([\d,]*)\}|∅', allowed)
    assert allowed.count('{') + allowed.count('∅') == len(al)
    al = '[' + '; '.join('[' + '; '.join(x.split(',')) + ']' if x else '[]' for x in al) + ']'
    ql = [qidx(t) for t in re.findall(r'⟨[^⟩]*⟩|\([^)]*\)|[\w.]+', qs)] if qs.strip() else []
    vn = 'c%seqs_%s' % (cn, name)
    out.append('(* Lean: %s *)' % name)
    out.append('let %s = { dmask = %s; dlower = %s; dupper = %s;\n  dallowed = %s;\n  dqueries = [%s] };;' % (vn, mask, lo, hi, al, '; '.join(ql)))
    _, k, kind = ck[name]
    fn = 'dsd_actual' if kind == 'SmallOwnerDomain' else 'sodt_checked'
    out.append('(* Lean: %s_checked *)' % name)
    out.append('let %s%s_CHECKED = %s `%s` %s %s;;' % (tag, name.upper(), fn, fam, k, vn))
if used_new:
    i = out.index('') if False else len(out)
    reg = ['(* the literal queries of EntryQuery00-03 used here are registered under c713eq_idx k *)',
           '(* (EntryQuery04.ml) like those of EntryQuery04-09, so that dqueries can name them  *)']
    for k in sorted(used_new):
        nm, d = newq[k]
        reg.append('let _ = let (m, k, ow, uin, uout) = (%s) in c713eq_register %d (0, m, k, ow, uin, uout) %s;;' % (d, k, nm))
    j = max(i for i, x in enumerate(out) if x.startswith('needs')) + 1
    out[j:j] = [''] + reg
open('n12/geometry/Cases_%s_EntryQueries.ml' % case, 'w').write('\n'.join(out) + '\n')
print(case, len(defs))
