#!/usr/bin/env python3
"""List Lean files (Geometry / Completion geometry) whose project imports are all ported,
not yet ported and not yet assigned. Usage: ready.py [root]"""
import re, os, sys, json
L = 'n12/ext/jatloe/Lean/Proofs/N12-jatloe/'
P2 = 'n12/geometry/'
ASSIGNED = 'n12/port_data/assigned.json'
def path(m):
    parts = m.split('.')
    if parts[0] == 'S12': return L + 'source/' + '/'.join(parts) + '.lean'
    return L + '/'.join(parts) + '.lean'
def imports(m):
    p = path(m)
    if not os.path.exists(p): return []
    return [i for i in re.findall(r'^import\s+(\S+)', open(p).read(), re.M) if not i.startswith('Mathlib')]
args = [a for a in sys.argv[1:] if not a.startswith('--')]
root = args[0] if args else 'Compact.Assembly.Final'
order, seen = [], set()
def visit(m):
    if m in seen or m.startswith('S12') or m.startswith('Mathlib'): return
    seen.add(m)
    for i in imports(m): visit(i)
    order.append(m)
visit(root)
done = set(x[:-3] for x in os.listdir(P2) if x.endswith('.ml'))
done |= {'FourSquareAnchors', 'ClosedPointExclusion'}   # in p2_base
ALIASES = json.load(open('n12/port_data/aliases.json'))
done |= {k for k, v in ALIASES.items() if v in done}
INPROG = 'n12/port_data/inprogress.json'
inprog = set(json.load(open(INPROG))) if os.path.exists(INPROG) else set()
done -= inprog
assigned = set(json.load(open(ASSIGNED))) if os.path.exists(ASSIGNED) else set()
def kinds(m): return set(i.split('.')[1] if i.startswith('Compact') else i.split('.')[0] for i in imports(m))
from collections import Counter as _C
_LAST = _C(m.split('.')[-1] for m in order
           if not (len(m.split('.')) > 2 and m.split('.')[1] == 'Completion'))
_BARE = {'Compact.Assembly.RowIdentity', 'Compact.Cases.MergedLower.Helpers'}   # existing files
def hname(m):
    p = m.split('.')
    if len(p) > 2 and p[1] == 'Completion': return 'CP_' + '_'.join(p[2:])
    if p[1] == 'Geometry' or _LAST[p[-1]] <= 1 or m in _BARE: return p[-1]
    # ambiguous short name: qualify (Completion.Cases.X.Y -> CC_X_Y, Compact.D.X.Y -> D_X_Y)
    return ('CC_' + '_'.join(p[2:])) if p[0] == 'Completion' else '_'.join(p[1:])
def is_geo(m):
    if '.Geometry.' in m: return True
    return '.Completion.' in m and kinds(m) <= {'Geometry', 'Completion', 'S12'}
def ok(m):
    return all(hname(i) in done for i in imports(m) if not i.startswith('S12') and os.path.exists(path(i)))
_np1 = {}
def needs_phase1(m):
    # imports (transitively) a non-geometry module, i.e. the packing context -> needs the cs_load server
    if m not in _np1:
        _np1[m] = False
        _np1[m] = any(not is_geo(i) or needs_phase1(i) for i in imports(m) if not i.startswith('S12'))
    return _np1[m]
PACK = '--packing' in sys.argv
def ok_pack(m):
    return all(i.startswith('S12') or not os.path.exists(path(i)) or hname(i) in done for i in imports(m))
CERT_PREFIXES = ('Compact.HistoricalCommon', 'Compact.HistoricalData', 'Compact.HistoricalFans',
                 'Compact.Preservation', 'Compact.Cases.C701', 'Compact.Cases.C713', 'Compact.Cases.C717',
                 'Compact.Cases.C973', 'Compact.Cases.C978', 'Compact.Cases.C979', 'Compact.Cases.C898',
                 'Compact.Core', 'Compact.Assembly',
                 # 'Compact.HistoricalOwnership' is portable: p2 QueriesNNN.ml files (n12/scripts/gen/cq.py)
                 'Compact.Cases.FourSquare', 'Compact.Cases.MergedLower', 'Compact.Cases.C849851',
                 'Compact.Cases.MergedTopFurther', 'Compact.Cases.OppositeCentralWalls',
                 'Compact.Cases.Endpoint684', 'Compact.Cases.C868', 'Compact.Bridge.C84',
                 )  # template/case drivers ('cases' agent)
QUERY_DATA = tuple('Compact.Cases.%s.%s' % (c, k) for c in ('C701','C713','C717','C973','C978','C979')
                   for k in ('EntryQuer', 'SharedSelections'))
CERT_BRIDGE = {'Compact.Bridge.' + x for x in ('DirectPruningPlan AxisSection IndexedBlockedTargetSyntax '
  'CheckedCommonGroup HistoricalPoseFanRecipe IndexedCommonPoint IndexedCommonGroups ChordSyntax '
  'VertexCutRelaxation CheckedCommonFanCommand IndexedCachedPairPlans IndexedRawPairPlans DirectCachedRecipe '
  'IndexedBlockedTarget DirectPoseCover DirectOwnerRecipe RelaxationTable IndexedRelaxation CommonGroupPruning '
  'IndexedChord IndexedCommonContext CommonRectanglePartition DirectRecipeTable DirectPoseForms '
  'DirectOwnerFamily DirectRecipeDictionary DirectRecipeCheck CheckedCommonContext CheckedRecipeCommand '
  'InitialCoverBatch OccupiedRowChord ChordPacking CommonHeaderPruning').split()}   # covered by n12/cert
def portable(m):
    # everything except certificate data (cert workers), the final assembly (coordinator), non-project
    if not os.path.exists(path(m)) or m in CERT_BRIDGE: return False
    return m.startswith(QUERY_DATA) or m in ('Compact.Assembly.C981Progress',) or not m.startswith(CERT_PREFIXES)
if PACK:
    # packing-level Completion modules (they need the Phase-1 server, n12/cases/cs_load.ml)
    ready = [m for m in order if portable(m) and not is_geo(m) and hname(m) not in done
             and hname(m) not in assigned and hname(m) not in inprog and ok_pack(m)]
else:
    ready = [m for m in order if is_geo(m) and hname(m) not in done and hname(m) not in assigned and hname(m) not in inprog and ok(m)]
for m in ready:
    print(m, hname(m), open(path(m)).read().count('\n'), [hname(i) for i in imports(m)], 'PHASE1' if needs_phase1(m) else '')
