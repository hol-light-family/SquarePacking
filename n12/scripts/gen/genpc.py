# generate HOL ports of C981 Coverage PrefixNN.lean (simple literal form) and C979 SharedSelections ChunkNN.lean
import re, sys
L = 'n12/ext/jatloe/Lean/Proofs/N12-jatloe/'
P = 'n12/geometry/'
def prefix(nn):
    s = open(L + 'Completion/Cases/C981/Coverage/Prefix%s.lean' % nn).read()
    m = re.search(r'def prefix%s : List \(List \(Finset Nat\)\) := \[(.*?)\n\]' % nn, s, re.S)
    body = m.group(1)
    rows = re.findall(r'\[([^\[\]]*)\]', body)
    def fs(r):
        sets = re.findall(r'\{([^}]*)\}|(∅)', r)
        return '[' + '; '.join('{' + ', '.join(x.strip() for x in st.split(',')) + '}' if st.strip() else '{}' for st, _ in sets) + ']'
    hol = '[' + ';\n    '.join(fs(r) for r in rows) + ']'
    st = re.search(r'theorem step%s : StepCheck prefix(\d+) allowed(\d+) prefix%s := by\s*\n\s*(decide \+kernel|apply stepCheck_of_extensions_eq\s*\n\s*rfl)\s*\nend' % (nn, nn), s)
    assert st, 'step form'
    prev, al = st.group(1), st.group(2)
    imports = re.findall(r'^import Completion\.Cases\.C981\.Coverage\.(\S+)', s, re.M)
    assert imports == ['Prefix' + prev], imports
    out = '''(* ========================================================================= *)
(* Port of Completion/Cases/C981/Coverage/Prefix%s.lean                       *)
(* (S12Completion.C981.Coverage.prefix%s, step%s).  StepCheck is pc_stepcheck *)
(* (PrefixCoverage.ml), its decide proof the producer c981cov_step_check      *)
(* (Prefix01.ml).  Tag C981CP%s_ / c981cov_.                                  *)
(* ========================================================================= *)

needs "n12/geometry/Prefix01.ml";;
needs "n12/geometry/Prefix%s.ml";;

(* Lean: prefix%s *)
let c981cov_prefix%s = new_definition
 `c981cov_prefix%s : ((num->bool)list)list =
   %s`;;

(* Lean: step%s *)
let C981CP%s_STEP%s = c981cov_step_check c981cov_prefix%s c981cov_allowed%s c981cov_prefix%s;;
''' % (nn, nn, nn, nn, prev, nn, nn, nn, hol, nn, nn, nn, prev, al, nn)
    if prev == '01': out = out.replace('needs "n12/geometry/Prefix01.ml";;\nneeds "n12/geometry/Prefix01.ml";;\n', 'needs "n12/geometry/Prefix01.ml";;\n')
    open(P + 'Prefix%s.ml' % nn, 'w').write(out)
def chunk(nn):
    s = open(L + 'Compact/Cases/C979/SharedSelections/Chunk%s.lean' % nn).read()
    pairs = re.findall(r'def selected(\d+) : \{q : LocalQuery // q\.Check\} := \(certified_query% (\d+)\)', s)
    ndefs = len(re.findall(r'\bdef\b', s))
    assert len(pairs) == ndefs, (len(pairs), ndefs)
    hdr = open(P + 'Cases_C979_SharedSelections_Chunk00.ml').read().split('\n(* Lean: selected0 *)')[0]
    hdr = hdr.replace('Chunk00.lean  ', 'Chunk%s.lean  ' % nn).replace('C979SS00_.', 'C979SS%s_.' % nn)
    body = ''.join('\n(* Lean: selected%s *)\nlet C979SS%s_SELECTED%s = slq_select %s;;\n' % (a, nn, a, b) for a, b in pairs)
    open(P + 'Cases_C979_SharedSelections_Chunk%s.ml' % nn, 'w').write(hdr + body)
kind, nn = sys.argv[1], sys.argv[2]
prefix(nn) if kind == 'prefix' else chunk(nn)
