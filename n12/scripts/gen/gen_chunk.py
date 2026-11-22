import re, sys
L = 'n12/ext/jatloe/Lean/Proofs/N12-jatloe/Completion/Cases/C981/Coverage/Data/Prefix10Chunks/'
for k in sys.argv[1:]:
    src = open(L + 'Chunk%s.lean' % k).read()
    m = re.search(r'def (prefix10Chunk\d+) : List \(List \(Finset Nat\)\) := \[(.*)\]\s*end', src, re.S)
    name, body = m.group(1), m.group(2)
    rows = re.findall(r'\[([^\[\]]*)\]', body)
    rows = [[x.strip() for x in r.split(',')] for r in rows]
    assert all(re.fullmatch(r'fs\d\d', x) for r in rows for x in r)
    hname = 'Chunk%s' % k
    out = ['(* ========================================================================= *)',
           '(* Port of Completion/Cases/C981/Coverage/Data/Prefix10Chunks/Chunk%s.lean    *)' % k,
           '(* (S12Completion.C981.Coverage.%s): a literal table of C981 coverage *)' % name,
           '(* fronts (%d rows).  Entries are the FinsetPool constants c981fp_fsNN.   *)' % len(rows),
           '(* HOL file name follows n12/scripts/ready.py hname (unique short name).        *)',
           '(* ========================================================================= *)', '',
           'needs "n12/geometry/p2_base.ml";;', 'needs "n12/geometry/FinsetPool.ml";;', '',
           '(* Lean: %s *)' % name,
           'let c981cov_%s = new_definition' % name.lower(),
           ' `c981cov_%s : ((num->bool)list)list = [' % name.lower()]
    lines = ['   [' + '; '.join('c981fp_' + x for x in r) + ']' for r in rows]
    out.append(';\n'.join(lines) + ']`;;')
    open('n12/geometry/%s.ml' % hname, 'w').write('\n'.join(out) + '\n')
    print(hname, len(rows))
