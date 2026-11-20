"""Check rational support bounds and exact fitted-data feasibility."""
import csv,json,math
from fractions import Fraction as F
from pathlib import Path

def need(b,s):
    if not b:raise ValueError(s)

def dot(a,b):
    need(len(a)==len(b),'Bad dimension')
    return sum(x*y for x,y in zip(a,b))

def means():
    with open('raw.csv') as f:
        r=csv.reader(f);header=next(r);rows=list(r)
    need(header[1:]==list(map(str,range(1,73))),'Time order differs')
    data=[]
    for row in rows:
        obs=[F(v) if v else None for v in row[1:]]
        val=[]
        for t in range(48,72):
            if obs[t] is not None:
                val.append(obs[t]);continue
            left=next((v for v in obs[:t][::-1] if v is not None),None)
            right=next((v for v in obs[t+1:] if v is not None),None)
            terms=[v for v in (left,right) if v is not None]
            val.append(sum(terms)/len(terms))
        data.append(sum(val)/24)
    return [r[0] for r in rows],data

def verify_observed():
    v=json.loads(Path('observed.json').read_text());codes,y=means()
    with open('full-loadings.csv') as stream:
        r=csv.reader(stream);next(r);rows=list(r)
    need(codes==[r[0] for r in rows]==v['stations'] and y==list(map(F,v['post_means'])),'Unaligned observed data')
    X=[[F(z) for z in r[1:]] for r in rows];k=len(X[0])
    def audit(which,eligible,eps):
        A=[];b=[]
        for i in range(1,len(y)):
            for s in [1,-1]:
                A.append([s*z for z in X[i]]+([-1] if which=='tau' else []))
                b.append(s*y[i]+eps)
        objective=([0]*k+[-1]) if which=='tau' else [z*(1 if which=='hi' else -1) for z in X[0]]
        out=v[which];mp={int(j):i for j,i in out['mapping'].items()}
        need(set(mp)==set(eligible),'Missing donor deletion')
        certs=out['certificates'];values={}
        for i,rec in enumerate(certs):
            p=list(map(F,rec['point']));w=list(map(F,rec['weights']));ss=rec['active'];value=F(rec['value'])
            need(len(w)==len(ss) and len(set(ss))==len(ss) and min(w)>=0 and all(0<=a<len(A) for a in ss),'Bad certificate')
            for t,z in enumerate(objective):need(dot(w,[A[a][t] for a in ss])==z,'Dual mismatch')
            need(dot(p,objective)==dot(w,[b[a] for a in ss])==value,'Objective mismatch')
            violations={a for a in range(len(A)) if dot(A[a],p)>b[a]}
            for j,idx in mp.items():
                if i!=idx:continue
                omitted={2*(j-1),2*j-1} if j else set()
                need(not omitted.intersection(ss) and violations<=omitted,'Infeasible primal or dual')
                values[j]=value
        need(set(values)==set(eligible),'Bad mapping')
        return values
    tau={j:-v for j,v in audit('tau',range(len(y)),0).items()}
    eps=math.ceil(min(tau.values()));good=sorted(j for j,z in tau.items() if z<=eps)
    lo=-max(audit('lo',good,eps).values());hi=max(audit('hi',good,eps).values())
    d=dict(tau_no_corrupt=str(tau[0]),tau_one=str(min(tau.values())),integer_tolerance=eps,eligible=[codes[i] if i else 'no removal' for i in good],prediction=[str(lo),str(hi)],effect=[str(y[0]-hi),str(y[0]-lo)])
    need(d==v['calibration'],'Observed result differs')
    return d

