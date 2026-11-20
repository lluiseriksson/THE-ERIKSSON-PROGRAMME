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
    target=X[0];t0=y[0]
    pivot=next(i for i,t in enumerate(target) if t)
    original_X=X;original_y=y
    free=[i for i in range(len(target)) if i!=pivot]
    def lift(p):
        z=list(p[:-1])
        z.insert(pivot,(t0-sum(target[i]*p[j] for j,i in enumerate(free)))/target[pivot])
        return z
    X=[[row[i]-row[pivot]*target[i]/target[pivot] for i in free] for row in original_X]
    y=[t-row[pivot]*t0/target[pivot] for t,row in zip(original_y,original_X)]
    v=[0]*len(X[0])+[-1]
    records=json.loads(Path('zero.json').read_text())
    values={};pred={}
    mp={int(k):i for k,i in records['mapping'].items()}
    need(set(mp)==set(range(len(rows))),'missing cases')
    A=[];b=[]
    for i in range(1,len(rows)):
        for sign in [1,-1]:
            A.append([sign*z for z in X[i]]+[-1]);b.append(sign*y[i])

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
            z=lift(p)
            need(dot(target,z)==t0 and all(abs(dot(z,original_X[i])-original_y[i])<=p[-1] for i in range(1,len(rows)) if i!=j),'unreduced equality or residual fails')
            values[j]=p[-1];pred[j]=dot(target,z)
    need(set(values)==set(mp),'uncertified mapping')
    t=min(values.values());winners=sorted(j for j,z in values.items() if z==t)
    return dict(threshold=str(t),threshold_display=float(t),no_removal=float(values[0]),cases=len(values),witnesses=len(records['certificates']),removals=[codes[j] if j else None for j in winners],zero_attained=any(pred[j]==t0 for j in winners))

