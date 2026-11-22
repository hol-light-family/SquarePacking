import json
d=json.load(open('n12/port_data/raw.json'))
C=d['cands']; P=set(map(tuple,d['pairs'])); P|={(b,a) for a,b in P}
E0=set(d['ex0']); E1=set(d['ex1'])
low=lambda m:(m&-m).bit_length()-1
byk={k:[m for m in C if low(m)==k] for k in range(16)}
nodes=0; leaves=0; out=[]
def rec(k, used, chosen):
    global nodes, leaves
    nodes+=1
    need=12-len(chosen)
    free=sum(1 for j in range(k,16) if not used>>j&1)
    if need>free: return
    fp=[(0,1),(2,3),(4,5),(6,7),(8,11),(9,10)]; gp=[(0,1),(2,3),(4,5),(6,7),(8,9),(10,11)]
    ok=lambda a,b: a>=k and b>=k and not used>>a&1 and not used>>b&1
    if sum(m in E0 for m in chosen)+sum(1 for a,b in fp if ok(a,b))<2: return
    if sum(m in E1 for m in chosen)+sum(1 for a,b in gp if ok(a,b))<2: return
    if k==16:
        if need==0 and sum(m in E0 for m in chosen)>=2 and sum(m in E1 for m in chosen)>=2:
            leaves+=1; out.append(tuple(sorted(chosen)))
        return
    if used>>k&1:
        rec(k+1,used,chosen); return
    rec(k+1,used,chosen)   # marker k unowned
    for m in byk[k]:
        if m&used==0 and not any((m,c) in P for c in chosen):
            rec(k+1,used|m,chosen+[m])
rec(0,0,[])
print(nodes,leaves)
e=set(map(tuple,json.load(open('n12/port_data/early.json'))))
print(set(out)==e)
