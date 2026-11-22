import re, json
D='n12/ext/jatloe/Lean/Proofs/N12-jatloe/source/S12/'
cv=open(D+'CoverData.lean').read()
raw=open(D+'RawData.lean').read()
perms=json.loads(re.search(r'def markerPerms : List \(List Nat\) := (\[\[.*?\]\])',raw).group(1))
rows=[]
for m in re.finditer(r'⟨(\d+),\{([0-9,]*)\},(\[.*?\])⟩(?=,⟨|\])',cv):
    rid=int(m.group(1)); groups=sorted(map(int,m.group(2).split(',')))
    doms=m.group(3)
    rows.append(dict(id=rid,groups=groups,domains=doms))
exp=[]
for m in re.finditer(r'def expected\d+ : List Nat := \[([0-9,]*)\]',cv):
    exp+= [int(x) for x in m.group(1).split(',') if x]
print(len(rows), len(exp), len(set(exp)))
def pm(p,m): return sum(1<<p[k] for k in range(16) if m>>k&1)
early=json.load(open('n12/port_data/early.json'))
rowkeys={tuple(r['groups']):i for i,r in enumerate(rows)}
cert=[]
for f in early:
    found=None
    for ti,p in enumerate(perms):
        g=tuple(sorted(pm(p,m) for m in f))
        if g in rowkeys: found=(ti,rowkeys[g]); break
    assert found, f
    cert.append(found)
print("all early families covered")
json.dump(dict(perms=perms,rows=rows,expected=exp,early_cert=cert),open('n12/port_data/rows.json','w'))
print(sum(1 for r in rows if r['id'] in set(exp)))
