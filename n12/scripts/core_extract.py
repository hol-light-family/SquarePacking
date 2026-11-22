#!/usr/bin/env python3
"""Extract Jatloe's domain specs and the 419 core proofs as OCaml data (hints only)."""
import re, glob
base = 'n12/ext/jatloe/Lean/Proofs/N12-jatloe/source/S12/'
src = "".join(open(f).read() for f in sorted(glob.glob(base + 'DomainSpecDataChunks/*.lean')))
def sets(s):
    return [[int(x) for x in g.split(',') if x] if g != '∅' else [] for g in re.findall(r'\{([\d,]*)\}|∅', s)] if False else \
           [[] if t == '∅' else [int(x) for x in t.strip('{}').split(',') if x] for t in re.findall(r'\{[\d,]*\}|∅', s)]
out = ['let SINGLE_SPECS = [']
for m in re.finditer(r'def singleSpec(\d+) : SingleSpec := ⟨(\d+),(\d+),(\d+),(\d+),\[(.*?)\],\[([\d,]*)\]⟩', src):
    i, mask, kind, lo, hi, allowed, refs = m.groups()
    out.append('  (%s, %s, %s, %s, %s, [%s]);' % (i, mask, kind, lo, hi,
               '; '.join('[' + '; '.join(map(str, s)) + ']' for s in sets(allowed))))
out.append('];;')
out.append('let COMBINED_SPECS = [')
for m in re.finditer(r'def combinedSpec(\d+) : CombinedSpec := ⟨(\d+),⟨singleSpec(\d+),[^⟩]*⟩,⟨singleSpec(\d+),[^⟩]*⟩,\[(.*?)\],\[([\d,]*)\]⟩', src):
    i, mask, f, g, allowed, refs = m.groups()
    out.append('  (%s, %s, %s, %s, [%s]);' % (i, mask, f, g,
               '; '.join('[' + '; '.join(map(str, s)) + ']' for s in sets(allowed))))
out.append('];;')
core = "".join(open(f).read() for f in sorted(glob.glob(base + 'CoreDataChunks/*.lean')))
out.append('let CORES = [')
for m in re.finditer(r'def coreProof(\d+) : CoreProof := ⟨\{([\d,]*)\},(\d),\[(.*)\]⟩', core):
    i, fam, mode, specs = m.groups()
    sp = re.findall(r'\.(single|combined) (?:(\d) )?(?:single|combined)Spec(\d+)', specs)
    sps = '; '.join('(%s, %s, %s)' % ('0' if t == 'single' else '1', k or '0', n) for t, k, n in sp)
    out.append('  (%s, [%s], %s, [%s]);' % (i, '; '.join(fam.split(',')), mode, sps))
out.append('];;')
print('\n'.join(out))
