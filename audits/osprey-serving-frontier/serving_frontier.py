"""Exact distribution and length sensitivity for the reported batch-one rates."""
from fractions import Fraction as F
from itertools import product, combinations
from pathlib import Path
import json


def need(ok, detail):
    if not ok:
        raise ValueError(detail)


def dot(q,d):
    return sum(x*y for x,y in zip(q,d))


def tv(q,p):
    return sum(abs(x-y) for x,y in zip(q,p))/2


def shifted(p,d,rho):
    q=list(p)
    order=sorted(range(len(p)),key=d.__getitem__)
    target=order[0]
    for i in reversed(order[1:]):
        amount=min(rho,q[i],1-q[target])
        q[target]+=amount
        q[i]-=amount
        rho-=amount
    return q


def savings(q,d,lengths):
    volume=dot(q,lengths)
    return sum(x*y*z for x,y,z in zip(q,d,lengths))/volume


def worst(p,d,rho,K):
    order=sorted(range(len(p)),key=d.__getitem__)
    q=shifted(p,d,rho)
    candidates=[]
    for cut in range(len(p)+1):
        lengths=[K if i in order[:cut] else F(1) for i in range(len(p))]
        candidates.append((savings(q,d,lengths),lengths))
    return min(candidates),q


def vertices(p,rho):
    n=len(p);out=set()
    for i in range(n):
        others=[k for k in range(n) if k!=i]
        for vals in product(*[(F(0),p[k],F(1)) for k in others]):
            q=list(p)
            for k,v in zip(others,vals):q[k]=v
            q[i]=1-sum(vals)
            if min(q)>=0 and tv(q,p)<=rho:out.add(tuple(q))
    for i,j in combinations(range(n),2):
        others=[k for k in range(n) if k not in [i,j]]
        for vals in product(*[(F(0),p[k],F(1)) for k in others]):
            q=list(p)
            for k,v in zip(others,vals):q[k]=v
            already=sum(max(F(0),q[k]-p[k]) for k in others)
            # At a non-box vertex two free coordinates take opposite deviations.
            for plus,minus in [(i,j),(j,i)]:
                q[plus]=p[plus]+rho-already
                q[minus]=1-q[plus]-sum(vals)
                if min(q)>=0 and q[plus]>=p[plus] and q[minus]<=p[minus] and tv(q,p)==rho:out.add(tuple(q))
    return out


def critical(q,d,delta):
    positive=sum(x*max(z-delta,0) for x,z in zip(q,d))
    negative=sum(x*max(delta-z,0) for x,z in zip(q,d))
    return positive/negative if negative else None


def main():
    source=json.loads(Path('source.json').read_bytes())
    rates=[[F(str(y)) for y in row] for row in source['rates_tokens_per_second'].values()]
    p=[F(1,5)]*5;d=[1/a-1/b for a,b in rates]
    out={};nchecks=0
    for rho in map(F,['0','1/10','1/5','3/10','2/5']):
        V=vertices(p,rho);q=shifted(p,d,rho)
        entry={'critical':str(critical(q,d,0)),'critical_display':float(critical(q,d,0)),'q':list(map(str,q)),'rows':{}}
        for K in map(F,[1,2,4,8,16]):
            (m,l),q=worst(p,d,rho,K)
            baseline=min(savings(z,d,k) for z in V for k in product([F(1),K],repeat=5))
            need(m==baseline and q in [list(x) for x in V],'Orthant enumeration disagreed')
            horizon=F(3040*3600,4)/m if m>0 else None
            entry['rows'][str(K)]={'saving':str(m),'billions':float(horizon/10**9) if horizon else None,'lengths':list(map(str,l))}
            nchecks+=len(V)*32
        out[str(rho)]=entry
    # Exact independent rounding envelope for the critical length ratio at fixed request shares.
    corners=[]
    for u in [F(1,20),-F(1,20)]:
        dc=[1/(a+u)-1/(b-u) for a,b in rates]
        corners.append(float(critical(p,dc,0)))
    # Recover the length ratio certificate at the computed threshold itself.
    for key,entry in out.items():
        k=F(entry['critical'])
        if k>=1:need(worst(p,d,F(key),k)[0][0]==0,'Wrong sign boundary')
    result=dict(frontier=out,vertex_length_comparisons=nchecks,rounding_critical_uniform=corners)
    print(json.dumps(result,indent=2,sort_keys=True))


if __name__=='__main__':main()

