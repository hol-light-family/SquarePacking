import json, sys
d=json.load(open('n12/port_data/raw.json'))
C=d['cands']; P=set(map(tuple,d['pairs'])); P|={(b,a) for a,b in P}
E0=set(d['ex0']); E1=set(d['ex1'])
# raw enumeration: sets of 12 pairwise disjoint candidate masks
C=sorted(C)
raw=0; early=0; nodes=0
res=[]
def rec(start, used, chosen):
    global raw, early, nodes
    nodes+=1
    if len(chosen)==12:
        raw+=1
        f=chosen
        if sum(m in E0 for m in f)>=2 and sum(m in E1 for m in f)>=2 and not any((a,b) in P for a in f for b in f):
            early+=1; res.append(tuple(f))
        return
    for i in range(start,len(C)):
        m=C[i]
        if m & used==0:
            rec(i+1, used|m, chosen+[m])
rec(0,0,[])
print(raw, early, nodes)
json.dump(res,open('n12/port_data/early.json','w'))
