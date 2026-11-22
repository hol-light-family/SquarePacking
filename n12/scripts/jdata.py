import re, json
D='n12/ext/jatloe/Lean/Proofs/N12-jatloe/source/S12/'
raw=open(D+'RawData.lean').read()
cands=[int(x) for x in re.search(r'def candidateMasks : List Nat := \[([^\]]*)\]',raw).group(1).split(',')]
pairs=[tuple(map(int,p)) for p in re.findall(r'\((\d+),(\d+)\)',re.search(r'def conflictingPairs[^\n]*',raw).group(0))]
ex0=[int(x) for x in re.search(r'def exempt0 : Finset Nat := \{([^}]*)\}',raw).group(1).split(',')]
ex1=[int(x) for x in re.search(r'def exempt1 : Finset Nat := \{([^}]*)\}',raw).group(1).split(',')]
json.dump(dict(cands=cands,pairs=pairs,ex0=ex0,ex1=ex1),open('n12/port_data/raw.json','w'))
print(len(cands),len(set(cands)),len(pairs),len(ex0),len(ex1))
