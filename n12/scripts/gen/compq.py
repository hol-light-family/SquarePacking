"""compq.py LEAN_REL HOL_NAME TAG NS : port a C983 ComponentsNN/*Queries.lean data file (lists of
certified queries + signature lists + an Exact decide) in the style of
CP_OtherCases_C983_Components05_Queries.ml.  Query refs: certified_query% n -> n (S12.localQueries);
N12Compact.HistoricalOwnership.Queries.queryN_certified -> slq_hist_idx N (QueriesNNN.ml)."""
import re, sys
L = 'n12/ext/jatloe/Lean/Proofs/N12-jatloe/'
rel, hname, tag, ns = sys.argv[1:5]
src = open(L + rel).read()
imports = re.findall(r'^import\s+(\S+)', src, re.M)
def hfile(m):
    p = m.split('.')
    if p[0] == 'Compact' and p[1] == 'Completion': return 'CP_' + '_'.join(p[2:])
    return p[-1]
out = ['(* ========================================================================= *)',
       '(* Phase 2: %s' % rel, '   (namespace %s).' % ns,
       '   Literal query data.  Lean certified_query% n = local query n of S12.localQueries;',
       '   Lean N12Compact.HistoricalOwnership.Queries.queryN_certified = the historical query N',
       '   (HOQ_QUERYN of QueriesNNN.ml), referred to by index slq_hist_idx N; mq_signature gives',
       "   Lean's signature; the Exact decide is the OCaml check %s_exact (fails on mismatch)." % tag,
       '   Tag %s_.  *)' % tag,
       '(* ========================================================================= *)', '']
for m in imports:
    out.append('needs "n12/geometry/%s.ml";;' % hfile(m))
out += ['', "(* Lean signatures = queries.map signature (the Exact decides) *)",
        'let %s_exact sigs qs =' % tag,
        '  let norm (m, k, ow, bl) = (m, k, List.sort compare ow, List.sort compare bl) in',
        '  if map norm sigs <> map (fun q -> norm (mq_signature q)) qs then failwith "%s_exact";;' % tag, '']
def setl(s):
    s = s.strip()
    if s in ('∅', '{}'): return '[]'
    return '[' + '; '.join(x.strip() for x in s.strip('{}').split(',')) + ']'
for m in re.finditer(r'def (\w+) : List \{q : LocalQuery // q.Check\} :=\s*\[(.*?)\]\n', src, re.S):
    name, body = m.groups()
    items = []
    for it in re.split(r',\s*\n?\s*', body.strip()):
        it = it.strip()
        a = re.fullmatch(r'\(certified_query% (\d+)\)', it)
        b = re.fullmatch(r'N12Compact\.HistoricalOwnership\.Queries\.query(\d+)_certified', it)
        if a: items.append(a.group(1))
        elif b: items.append('slq_hist_idx %s' % b.group(1))
        else: raise SystemExit('unknown item ' + it)
    out.append('(* Lean: %s *)' % name)
    out.append('let %s_%s = [%s];;' % (tag, name, '; '.join(items)))
for m in re.finditer(r'def (\w+) : List Signature :=\s*\[(.*?)\]\n', src, re.S):
    name, body = m.groups()
    sigs = re.findall(r'\((\d+),(\d+),(\{[\d,]*\}|∅),(\{[\d,]*\}|∅)\)', body)
    assert len(sigs) == body.count('('), name
    out.append('(* Lean: %s *)' % name)
    out.append('let %s_%s =\n  [%s];;' % (tag, name, ';\n   '.join('(%s, %s, %s, %s)' % (a, b, setl(c), setl(d)) for a, b, c, d in sigs)))
for m in re.finditer(r'theorem (\w+) :\s*(\w+)\s*=\s*(\w+)\.map \(fun q => signature q\.val\)', src):
    th, sg, qs = m.groups()
    out.append('(* Lean: %s *)' % th)
    out.append('let () = %s_exact %s_%s %s_%s;;' % (tag, tag, sg, tag, qs))
open('n12/geometry/%s.ml' % hname, 'w').write('\n'.join(out) + '\n')
print(hname, src.count('theorem '), 'theorems in Lean')
