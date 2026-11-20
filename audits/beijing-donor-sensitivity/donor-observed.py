"""Certify minimax residuals and the observed target interval using rational bases."""
import csv,json,itertools,math
from fractions import Fraction as F
from pathlib import Path
import numpy as np
import sympy as sp
from scipy.optimize import linprog

def rational(v):return sp.Rational(v)
def mean_post(row):
    vals=[F(v) if v else None for v in row]
    out=[]
    for i in range(48,72):
        if vals[i] is not None:out.append(vals[i]);continue
        before=next((v for v in reversed(vals[:i]) if v is not None),None)
        after=next((v for v in vals[i+1:] if v is not None),None)
        sides=[v for v in [before,after] if v is not None]
        if not sides:raise ValueError('Station empty')
        out.append(sum(sides)/len(sides))
    return sum(out)/24

def load(name):
    with open(name) as stream:return list(csv.reader(stream))[1:]

def main():
    rows=load('full-loadings.csv');raw=load('raw.csv')
    codes=[r[0] for r in rows]
    if [r[0] for r in raw]!=codes:raise ValueError('Unaligned')
    X=sp.Matrix([[rational(v) for v in r[1:]] for r in rows])
    y=[rational(str(mean_post(r[1:]))) for r in raw]
    donor_count=len(codes)-1
    result={'post_means':list(map(str,y)),'stations':codes}
    def make_system(mode,eps):
        cons=[];bounds=[]
        for i in range(1,len(rows)):
            for sign in [1,-1]:
                cons.append([sign*x for x in X.row(i)]+([-1] if mode=='tau' else []))
                bounds.append(sign*y[i]+eps)
        objective=([0]*X.cols+[-1] if mode=='tau' else [x*(1 if mode=='max' else -1) for x in X.row(0)])
        return sp.Matrix(cons),sp.Matrix(bounds),sp.Matrix(objective)
    def run(mode,eps,omit_set):
        A,b,v=make_system(mode,eps);cache=[];mapping={};fA=np.array(A,dtype=float);fb=np.array(b,dtype=float).ravel();fv=np.array(v,dtype=float).ravel()
        for j in omit_set:
            omit={2*(j-1),2*(j-1)+1} if j else set()
            allowed=[i for i in range(A.rows) if i not in omit]
            for idx,rec in enumerate(cache):
                if not omit.intersection(rec['active']) and set(rec['violations'])<=omit:
                    mapping[j]=idx;break
            else:
                res=linprog(-fv,A_ub=fA[allowed],b_ub=fb[allowed],bounds=(None,None),method='highs')
                if not res.success:raise RuntimeError(str((mode,j,res.message)))
                marg=np.abs(res.ineqlin.marginals)
                active=[allowed[i] for i in np.argsort(-marg)[:len(v)]]
                basis=A[active,:]
                p=basis.inv()*b[active,:]
                dual=basis.T.inv()*v
                violations=[i for i,z in enumerate(A*p-b) if z>0]
                if min(dual)<0 or not set(violations)<=omit:raise ValueError(f'Exact {mode} basis failed for {j}')
                value=(v.T*p)[0]
                mapping[j]=len(cache)
                cache.append(dict(value=str(value),point=list(map(str,p)),active=active,weights=list(map(str,dual)),violations=violations))
        return dict(certificates=cache,mapping=mapping)
    tau=run('tau',0,range(len(rows)))
    values={j:-rational(tau['certificates'][t]['value']) for j,t in tau['mapping'].items()}
    tau1=min(values.values());eps=int(math.ceil(tau1))
    eligible=[j for j,t in values.items() if t<=eps]
    lo=run('min',eps,eligible);hi=run('max',eps,eligible)
    lower=-max(rational(r['value']) for r in lo['certificates'])
    upper=max(rational(r['value']) for r in hi['certificates'])
    result.update(tau=tau,lo=lo,hi=hi,calibration=dict(tau_no_corrupt=str(values[0]),tau_one=str(tau1),integer_tolerance=eps,eligible=[codes[i] if i else 'no removal' for i in eligible],prediction=[str(lower),str(upper)],effect=[str(y[0]-upper),str(y[0]-lower)]))
    Path('observed.json').write_text(json.dumps(result))
    print(eps,float(tau1),float(values[0]),len(eligible),list(map(float,[lower,upper,y[0]-upper,y[0]-lower])),flush=True)
if __name__=='__main__':main()

