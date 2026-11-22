# generates the originalComponents definition for n12/geometry/CP_OtherCases_C983_Entrance.ml
import re
R = ''
s = open(R + 'n12/ext/jatloe/Lean/Proofs/N12-jatloe/Compact/Completion/OtherCases/C983/Entrance.lean').read()
body = s.split('def originalComponents : Fin 12 → List (Finset Nat) :=')[1].split('def owners')[0]
rows = re.findall(r'\[([^\[\]]*)\]', body)
assert len(rows) == 12
def numsets(txt):
    return '[' + '; '.join('{%s}' % ', '.join(m.group(1).split(',')) if m.group(1) else '({}:num->bool)'
                           for m in re.finditer(r'\{([\d,]*)\}|∅', txt)) + ']'
print('let c983e_original_components = new_definition\n `c983e_original_components : ((num->bool)list)list =\n    [' +
      ';\n     '.join(numsets(r) for r in rows) + ']`;;')
