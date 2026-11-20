"""Exact attainable variance versus distinguishability from the uniform ticket lottery."""
from collections import Counter
from fractions import Fraction as Q
from itertools import accumulate,combinations_with_replacement,product
from pathlib import Path
from hashlib import sha256
import json,zipfile

def designs(n):
    h=n//2
    for inc in product((-1,0,1),repeat=h-1):
        s=(0,*accumulate(inc))
        if sum(s):continue
        yield tuple(j+(s[j] if j<h else s[n-1-j]) for j in range(n))
from math import factorial, prod
from itertools import groupby
from collections import defaultdict
def table(x,m):
    f=Counter(x);out=defaultdict(Counter)
    for row in combinations_with_replacement(sorted(f),m):
        multiplicity=Counter(row)
        wt=factorial(m)//prod(factorial(k) for k in multiplicity.values())*prod(f[v]**k for v,k in multiplicity.items())
        g=(row[0],row[-1],sum(row))
        q=sum(y*y for y in row)
        out[g][q]+=wt
    assert sum(sum(d.values()) for d in out.values())==len(x)**m
    return out
def capacity(a,b,verify=False):
    # Greedy two-pointer matching: reserve the least feasible high score.
    keys=sorted(b);stock=dict(b);j=0;total=0
    for v,wt in sorted(a.items()):
        while j<len(keys) and wt:
            w=keys[j]
            if w<=v or not stock[w]:j+=1;continue
            n=min(wt,stock[w]);wt-=n;stock[w]-=n;total+=n
    # Threshold cut certificate, including both extreme thresholds.
    cut=min([sum(a.values()),sum(b.values())]+[sum(k for v,k in a.items() if v<t)+sum(k for w,k in b.items() if w>t) for t in a])
    assert total==cut
    if verify:
        import networkx as nx
        g=nx.DiGraph();g.add_nodes_from(['s','t'])
        for v,wt in a.items():
            g.add_edge('s',('a',v),capacity=wt)
            for w in b:
                if v<w:g.add_edge(('a',v),('b',w),capacity=sum(a.values())+1)
        for w,wt in b.items():g.add_edge(('b',w),'t',capacity=wt)
        assert nx.maximum_flow_value(g,'s','t')==total
    return total
result={}
for n in (8,10,12,14,16):
    base=table(list(range(n)),4)
    rows=[]
    for x in designs(n):
        other=table(x,4)
        success=sum(capacity(a,other.get(g,{}),verify=n==8) for g,a in base.items())
        extra=Q(sum(z*z-i*i for i,z in enumerate(x)),n)
        rows.append(dict(x=x,extra=str(extra),capacity=success,probability=str(Q(success,n**4))))
    points={(Q(r['extra']),r['capacity']) for r in rows}
    front=[next(r for r in rows if Q(r['extra'])==v and r['capacity']==z) for v,z in sorted(points) if not any(vv>=v and zz>=z and (v,z)!=(vv,zz) for vv,zz in points)]
    result[n]=dict(designs=len(rows),den=n**4,best=max(rows,key=lambda r:r['capacity']),front=front,rows=rows)
p=Path('/content/archive.zip')
with zipfile.ZipFile(p,'w',zipfile.ZIP_DEFLATED) as z:z.writestr('matched.json',json.dumps(result))
print('archive_sha256',sha256(p.read_bytes()).hexdigest())
