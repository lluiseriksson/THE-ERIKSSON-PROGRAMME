"""Chebyshev residual needed for a nonpositive observed-minus-predicted contrast."""
import json
from pathlib import Path
import numpy as np
import sympy as sp
from scipy.optimize import linprog
from fractions import Fraction as F
import csv

def panel():
    with open('full-loadings.csv') as f: rows=list(csv.reader(f))[1:]
    recorded=json.loads(Path('observed.json').read_text())
    codes=[r[0] for r in rows]
    if codes!=recorded['stations']: raise ValueError('station order')
    X=[[F(x) for x in r[1:]] for r in rows]
    y=list(map(F,recorded['post_means']))
    A=[]; b=[]
    for i in range(1,len(X)):
        for sign in [1,-1]:
            A.append([sign*z for z in X[i]]+[-1]); b.append(sign*y[i])
    A.append([-z for z in X[0]]+[0]); b.append(-y[0])
    return codes,X,y,A,b

def generate():
    codes,X,y,A,b=panel(); A=sp.Matrix(A); b=sp.Matrix(b)
    v=sp.Matrix([0]*(A.cols-1)+[-1])
    fa=np.array(A,dtype=float);fb=np.array(b,dtype=float).ravel()
    fv=np.array(v,dtype=float).ravel();records=[];mapping={}
    for j in range(len(codes)):
        omit={2*j-2,2*j-1} if j else set()
        for k,r in enumerate(records):
            if not omit.intersection(r['active']) and set(r['violations'])<=omit:
                mapping[j]=k;break
        else:
            allowed=[i for i in range(A.rows) if i not in omit]
            res=linprog(-fv,A_ub=fa[allowed],b_ub=fb[allowed],bounds=(None,None),method='highs')
            if not res.success:raise RuntimeError(res.message)
            active=[allowed[i] for i in np.argsort(-abs(res.ineqlin.marginals))[:len(v)]]
            basis=A[active,:];p=basis.inv()*b[active,:];dual=basis.T.inv()*v
            violations=[i for i,z in enumerate(A*p-b) if z>0]
            if min(dual)<0 or not set(violations)<=omit:raise ValueError(('basis',j))
            mapping[j]=len(records)
            records.append(dict(point=list(map(str,p)),weights=list(map(str,dual)),active=active,violations=violations))
    Path('breakpoint.json').write_text(json.dumps(dict(mapping=mapping,certificates=records)))

if __name__=='__main__':generate()
