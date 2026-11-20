"""Check sign reversal and whether zero is attained at its exact threshold."""
import csv,json
from pathlib import Path
from fractions import Fraction as F
from verify_observed import means,need,dot

def verify():
    codes,y=means()
    with open('full-loadings.csv') as f:rows=list(csv.reader(f))[1:]
    need(codes==[r[0] for r in rows],'station order')
    X=[list(map(F,r[1:])) for r in rows]
    v=[0]*len(X[0])+[-1]
    records=json.loads(Path('breakpoint.json').read_text())
    values={};pred={}
    mp={int(k):i for k,i in records['mapping'].items()}
    need(set(mp)==set(range(len(rows))),'missing cases')
    A=[];b=[]
    for i in range(1,len(rows)):
        for sign in [1,-1]:
            A.append([sign*z for z in X[i]]+[-1]);b.append(sign*y[i])
    A.append([-x for x in X[0]]+[0]);b.append(-y[0])
    for k,r in enumerate(records['certificates']):
        p=list(map(F,r['point']));w=list(map(F,r['weights']));ss=r['active']
        need(len(w)==len(ss) and min(w)>=0 and len(set(ss))==len(ss) and all(0<=i<len(A) for i in ss),'dual indices')
        need([dot(w,[A[i][t] for i in ss]) for t in range(len(v))]==v,'stationarity')
        need(dot(p,v)==dot(w,[b[i] for i in ss]),'gap')
        bad={i for i,a in enumerate(A) if dot(a,p)>b[i]}
        for j,idx in mp.items():
            if idx!=k:continue
            omit={2*j-2,2*j-1} if j else set()
            need(not omit.intersection(ss) and bad<=omit,'infeasible')
            values[j]=p[-1];pred[j]=dot(X[0],p[:-1])
    need(set(values)==set(mp),'uncertified mapping')
    t=min(values.values());winners=sorted(j for j,z in values.items() if z==t)
    return dict(threshold=str(t),threshold_display=float(t),no_removal=float(values[0]),cases=len(values),witnesses=len(records['certificates']),removals=[codes[j] if j else None for j in winners],zero_attained=any(pred[j]==y[0] for j in winners))

