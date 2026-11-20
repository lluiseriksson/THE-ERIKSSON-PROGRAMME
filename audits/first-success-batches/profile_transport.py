"""Construct and verify integer monotone-transport certificates for full-count strata."""
from collections import Counter, defaultdict
from itertools import combinations_with_replacement, accumulate
from math import comb, factorial, lcm, prod
from pathlib import Path
from zipfile import ZipFile, ZIP_DEFLATED
import json, hashlib
import networkx as nx


def multiply(left, right):
    out = [0]*(len(left)+len(right)-1)
    for i,a in enumerate(left):
        for j,b in enumerate(right):
            out[i+j] += a*b
    return out


def coefficients(n,m):
    ways = [1]
    for _ in range(m):
        ways = multiply(ways,[1]*n)
    common = lcm(*ways)
    weights = [comb(m+s-1,s)*(common//a) for s,a in enumerate(ways)]
    by_total = defaultdict(dict)
    for profile in combinations_with_replacement(range(n+1),m):
        k=sum(profile)
        if k<m: continue
        mult=factorial(m)//prod(factorial(t) for t in Counter(profile).values())
        true_mass=mult*prod(comb(n,t) for t in profile)
        stopped=0
        if profile[0]:
            waits=[1]
            for t in profile:
                waits=multiply(waits,[comb(n-u-1,t-1) for u in range(n-t+1)])
            stopped=mult*sum(w*c for w,c in zip(weights,waits))
        by_total[k][profile]=common*true_mass-stopped
    return common,by_total


def solve(coeff):
    keys=list(coeff)
    src, sink = len(keys),len(keys)+1
    g=nx.DiGraph()
    balance=sum(v for v in coeff.values() if v>0)
    assert sum(coeff.values())==0
    if not balance: return dict(edges=[])
    ps=[i for i,p in enumerate(keys) if coeff[p]>0]
    ns=[i for i,p in enumerate(keys) if coeff[p]<0]
    prefix=[list(accumulate(reversed(p))) for p in keys]
    for i in ps:
        g.add_edge(src,i,capacity=coeff[keys[i]])
    for j in ns:
        g.add_edge(j,sink,capacity=-coeff[keys[j]])
    for i in ps:
        for j in ns:
            if all(x>=y for x,y in zip(prefix[i],prefix[j])):
                g.add_edge(i,j,capacity=balance+1)
    amount,flow=nx.maximum_flow(g,src,sink)
    if amount!=balance:
        value,cut=nx.minimum_cut(g,src,sink)
        assert value==amount
        # Upper closure of the deficit vertices on the sink side.
        unmet=[j for j in ns if j in cut[1]]
        upper=[i for i in range(len(keys)) if any(all(x>=y for x,y in zip(prefix[i],prefix[j])) for j in unmet)]
        assert sum(coeff[keys[i]] for i in upper)<0
        return dict(obstruction=[list(keys[i]) for i in upper],net=sum(coeff[keys[i]] for i in upper))
    return dict(edges=[[list(keys[i]),list(keys[j]),f] for i in ps for j,f in flow[i].items() if f and j!=src and j!=sink])


def verify(n,m,k,scale,cert):
    # Compute each orbit directly using the weak compositions of extra successes
    # implicit in first-wait polynomials. Recheck order independently by lower tails.
    coeff={}
    for r in combinations_with_replacement(range(n+1),m):
        if sum(r)!=k:continue
        multiplicity=factorial(m)
        for count in Counter(r).values(): multiplicity//=factorial(count)
        mass=scale*prod(comb(n,x) for x in r)
        if min(r)>0:
            dp={0:1}
            for x in r:
                nxt=defaultdict(int)
                for s,num in dp.items():
                    for u in range(n-x+1):nxt[s+u]+=num*comb(n-u-1,n-x-u)
                dp=nxt
            for s,count in dp.items():
                # inclusion-exclusion for [z^s](1+...+z^(n-1))^m
                ways=sum((-1)**j*comb(m,j)*comb(s-n*j+m-1,m-1) for j in range(min(m,s//n)+1))
                assert scale%ways==0
                mass-=count*comb(m+s-1,m-1)*(scale//ways)
        coeff[r]=mass*multiplicity
    assert sum(coeff.values())==0
    if 'net' in cert:
        upper={tuple(r) for r in cert['obstruction']}
        assert sum(coeff[r] for r in upper)==cert['net']<0
        for r in upper:
            for t in coeff:
                if all(sum(t[:i])<=sum(r[:i]) for i in range(1,m)):assert t in upper
        return
    rem=dict(coeff)
    for l,r,f in cert['edges']:
        l,r=tuple(l),tuple(r)
        assert type(f) is int and f>0 and coeff[l]>0 and coeff[r]<0
        assert all(sum(l[:i])<=sum(r[:i]) for i in range(1,m))
        rem[l]-=f
        rem[r]+=f
    assert not any(rem.values())


def main():
    results=[]
    path=Path('/content/archive.zip')
    with ZipFile(path,'w',ZIP_DEFLATED) as z:
        for n,limit in [(3,16),(4,10),(5,7),(6,5)]:
            for m in range(2,limit+1):
                scale,rows=coefficients(n,m)
                witnesses={}
                for k,coeff in rows.items():
                    witness=solve(coeff)
                    verify(n,m,k,scale,witness)
                    witnesses[k]=witness
                certname=f'certificates/cap-{n}-tasks-{m}.json'
                raw=json.dumps(dict(n=n,m=m,scale=scale,strata=witnesses),separators=(',',':')).encode()
                z.writestr(certname,raw)
                results.append(dict(n=n,m=m,strata=len(rows),edges=sum(len(v.get('edges',[])) for v in witnesses.values()),failed=[k for k,v in witnesses.items() if 'net' in v],file=certname,sha256=hashlib.sha256(raw).hexdigest()))
        z.writestr('transport.json',json.dumps(results,indent=2))
    print('archive_sha256',hashlib.sha256(path.read_bytes()).hexdigest())
if __name__=='__main__':main()
