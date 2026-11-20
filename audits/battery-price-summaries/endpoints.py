"""Exact revenue bounds for fixed dispatch using opening price, closing price, mean and a variation cap."""
import csv
import hashlib
import io
import json
from collections import Counter
from datetime import datetime, timedelta
from fractions import Fraction as Q
from itertools import accumulate
from urllib.request import Request, urlopen

URL = 'https://aemo.com.au/aemo/data/nem/priceanddemand/PRICE_AND_DEMAND_202501_NSW1.csv'
DIGEST = '975e8603457f1370f818c880e18a8a7f0c09794410a04d83a0b6f677dca9906a'


def hull(points):
    """Andrew's monotone chain, including the segment and point cases."""
    vertices = sorted(set(points))
    if len(vertices) < 2:
        return vertices
    def half(seq):
        result = []
        for x, y in seq:
            while len(result) >= 2:
                (a,b),(c,d) = result[-2:]
                if (c-a)*(y-b) > (d-b)*(x-a):
                    break
                result.pop()
            result.append((x,y))
        return result
    return half(vertices)[:-1] + half(reversed(vertices))[:-1]


def bounds(first,last,mean,variation,dispatch):
    m = len(dispatch)
    if m < 2 or variation < abs(last-first):
        raise ValueError('Infeasible variation cap or too few prices')
    pos = (variation+last-first)/2
    neg = (variation-last+first)/2
    target = m*(mean-first)
    total = sum(dispatch)
    atoms = [(m-j,sum(dispatch[j:])) for j in range(1,m)]
    # A point encodes a positive jump at j and a negative jump at k.
    # Record a price-path witness for each vertex in the generating set.
    generating = {}
    for j,(wj,cj) in enumerate(atoms):
        for k,(wk,ck) in enumerate(atoms):
            generating[(pos*wj-neg*wk,pos*cj-neg*ck)] = (j,k)
    polygon = hull(generating)
    hits = []
    for left,right in zip(polygon,polygon[1:]+polygon[:1]):
        if left[0]==target:
            hits.append((left[1],left,left,Q(0)))
        if min(left[0],right[0])<target<max(left[0],right[0]):
            alpha = (target-left[0])/(right[0]-left[0])
            hits.append((left[1]+alpha*(right[1]-left[1]),left,right,alpha))
    if not hits:
        raise ValueError('Endpoint levels and mean cannot be realized')
    def witness(hit):
        value,left,right,alpha = hit
        jumps = [Q(0)]*(m-1)
        for vertex,weight in [(left,1-alpha),(right,alpha)]:
            j,k=generating[vertex]
            jumps[j]+=weight*pos
            jumps[k]-=weight*neg
        path=list(accumulate(jumps,initial=first))
        cash=sum(p*d for p,d in zip(path,dispatch))
        assert path[-1]==last and sum(path)==m*mean and sum(map(abs,jumps))<=variation
        assert cash==value+first*total
        return cash,path
    return [witness(min(hits)),witness(max(hits))]


def direct_lp(first,last,mean,variation,d):
    import numpy as np
    from scipy.optimize import linprog
    m=len(d); diff=np.diff(np.eye(m),axis=0); eye=np.eye(m-1)
    a=np.vstack([np.c_[diff,-eye],np.c_[-diff,-eye],np.r_[np.zeros(m),np.ones(m-1)]])
    eq=np.c_[np.array([np.eye(m)[0],np.eye(m)[-1],np.ones(m)]),np.zeros((3,m-1))]
    values=[]
    for sign in [1,-1]:
        r=linprog(np.r_[sign*np.asarray(d,dtype=float),np.zeros(m-1)],A_ub=a,
                  b_ub=[0]*(2*(m-1))+[float(variation)],A_eq=eq,b_eq=list(map(float,[first,last,m*mean])),
                  bounds=[(None,None)]*m+[(0,None)]*(m-1),method='highs')
        assert r.success,r.message
        values.append(sign*r.fun)
    return values


def classify(lo,hi):
    if lo>0:return 'early'
    if hi<0:return 'late'
    if lo==hi==0:return 'tie'
    if lo==0:return 'early_or_tie'
    if hi==0:return 'late_or_tie'
    return 'both_signs'


def study():
    with urlopen(Request(URL,headers={'User-Agent':'Mozilla/5.0 (research replay)'}),timeout=60) as response:
        raw=response.read()
    assert hashlib.sha256(raw).hexdigest()==DIGEST
    rows=list(csv.DictReader(io.StringIO(raw.decode('utf-8-sig'))))
    start=datetime(2025,1,1)
    assert len(rows)==744*12
    for i,r in enumerate(rows,1):
        assert r['REGION']=='NSW1' and r['PERIODTYPE']=='TRADE'
        assert datetime.strptime(r['SETTLEMENTDATE'],'%Y/%m/%d %H:%M:%S')==start+timedelta(minutes=5*i)
    d=[Q(1,12)]*6+[Q(-1,12)]*6
    B=list(accumulate(d))[:-1]
    reports=[];transitions=Counter()
    for h in range(744):
        p=[Q(r['RRP']) for r in rows[12*h:12*h+12]]
        mean=sum(p)/12;g=p[-1]-p[0];v=sum(abs(x-y) for x,y in zip(p,p[1:]))
        pos,neg=(v+g)/2,(v-g)/2
        oldlo,oldhi=-pos*max(B)+neg*min(B),-pos*min(B)+neg*max(B)
        (lo,low_path),(hi,high_path)=bounds(p[0],p[-1],mean,v,d)
        observed=sum(price*energy for price,energy in zip(p,d))
        assert oldlo<=lo<=observed<=hi<=oldhi
        floating=direct_lp(p[0],p[-1],mean,v,d)
        assert all(abs(float(q)-f)<1e-7*max(1,abs(float(q))) for q,f in zip((lo,hi),floating))
        old=classify(oldlo,oldhi);new=classify(lo,hi)
        transitions[old+' -> '+new]+=1
        reports.append(dict(hour=(start+timedelta(hours=h)).isoformat(),old=[oldlo,oldhi],new=[lo,hi],
                            observed=observed,lower_witness=low_path,upper_witness=high_path,classification=new))
    return dict(url=URL,sha256=DIGEST,hours=reports,transitions=dict(sorted(transitions.items())),
                classifications=dict(Counter(r['classification'] for r in reports)),
                strict_width_reductions=sum(r['new'][1]-r['new'][0]<r['old'][1]-r['old'][0] for r in reports),
                lp_comparisons=2*len(reports))

if __name__=='__main__':
    print(json.dumps(study(),default=str))
