from fractions import Fraction as F
import itertools, json
M=[(F(1),F(457,500)),(F(457,500),F(1)),(F(3),F(457,500)),(F(1543,500),F(1)),(F(3),F(1543,500)),(F(1543,500),F(3)),(F(1),F(1543,500)),(F(457,500),F(3)),(F(33,20),F(33,20)),(F(47,20),F(33,20)),(F(47,20),F(47,20)),(F(33,20),F(47,20)),(F(457,500),F(2)),(F(2),F(457,500)),(F(1543,500),F(2)),(F(2),F(1543,500))]
lim=F(2000000,982081)
d2=lambda p,q:(p[0]-q[0])**2+(p[1]-q[1])**2
comp={(i,j) for i in range(16) for j in range(16) if d2(M[i],M[j])<lim}
inc=[(i,j) for i in range(16) for j in range(i+1,16) if (i,j) not in comp]
cl=[]
for r in range(1,17):
    for S in itertools.combinations(range(16),r):
        if all((i,j) in comp for i in S for j in S): cl.append(S)
masks=sorted(sum(1<<k for k in S) for S in cl)
d=json.load(open('n12/port_data/raw.json'))
print(len(cl), sorted(d['cands'])==masks, len(inc))
print(min(d2(M[i],M[j]) for i,j in inc), max(d2(M[i],M[j]) for (i,j) in comp))
json.dump(dict(inc=inc,cliques=cl),open('n12/port_data/groups.json','w'))
