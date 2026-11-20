"""Construct synthetic overlap witnesses, using only the published count margins."""
from itertools import product
from fractions import Fraction as F
import json
import numpy as np
from scipy.optimize import milp, Bounds, LinearConstraint
rates=[('1.41','0.24'),('0.77','0.12'),('0.04','0.00'),('1.93','0.04'),('2.01','0.00'),('0.32','0.00'),('1.25','0.00'),('1.69','0.00'),('3.83','0.12'),('11.28','0.00'),('1.33','0.20'),('54.71','0.12'),('15.27','0.04'),('43.71','0.04'),('0.44','0.00'),('4.15','0.00'),('0.32','0.40'),('10.76','0.20'),('3.51','0.81'),('1.97','0.64'),('0.52','0.56')]
def recover(s):
    vs=[i for i in range(2483) if abs(F(100*i,2482)-F(s))<=F(1,200)]
    assert len(vs)==1,(s,vs)
    return vs[0]
before,after=([recover(r[j]) for r in rates] for j in [0,1])
# One case has at most one higher-tier flag: 23 such flags span 72−49=23 cases.
# Categories: math, over-refusal, completeness, well-formedness, truncation, higher.
patterns=[p for p in product(range(3),range(3),[0,1],[0,2],[0,2],range(3)) if any(p)]
def features(p):
    return [1,int(any(p[:5])),int(bool(p[5])),*[int(bool(x)) for x in p[:5]],p.count(2)]
A=np.array([features(p) for p in patterns],dtype=int).T
b=np.array([72,50,23,10,5,20,16,14,43])
def solve(kind,sign,mat=None):
    matrix=A if mat is None else np.vstack([A,[p[0]==2 for p in patterns]])
    rhs=b if mat is None else np.append(b,mat)
    c=np.array([int(2 in p) if kind=='any' else int(2 in p and 1 not in p) for p in patterns],dtype=int)
    r=milp(sign*c,integrality=np.ones(len(c)),bounds=Bounds(0,72),constraints=LinearConstraint(matrix,rhs,rhs),options={'mip_rel_gap':0.0})
    assert r.success and abs(r.mip_gap)<1e-7
    x=np.rint(r.x).astype(int);assert min(x)>=0 and np.array_equal(matrix@x,rhs)
    return dict(value=int(c@x),matrix=[dict(pattern=list(p),cases=int(n)) for p,n in zip(patterns,x) if n])
out={}
for a in [None,5]:
    for k in ['any','all_flags_confirmed']:
        out[f'{a}:{k}']=[solve(k,sign,a) for sign in [1,-1]]
print(json.dumps(dict(before=before,after=after,sums=[sum(before),sum(after)],output_after=sum(after[15:]),higher_after=sum(after[:15]),ranges=out)))