"""Exact finite certificate for optimal full-block inspections at the first exceptional capacity."""
from fractions import Fraction as Q
from itertools import combinations
from math import comb
from pathlib import Path
import hashlib,json,zipfile
from scipy.optimize import linprog
from sympy import Matrix, Rational
def C(n,k):
    return comb(n,k) if 0<=k<=n else 0
def solve_case(t,d):
    low=16-t
    js=list(range(max(0,d-low),min(d,t)+1))
    nulls=[(a,12-a) for a in range(t+1) if 0<=12-a<=low]+[(t-3,low)]
    A=[[Q(C(a,j)*C(b,d-j),C(t,j)*C(low,d-j)) for j in js] for a,b in nulls]
    def certificate(A):
        m,n=len(A),len(A[0])
        sol=linprog([0]*n+[1],A_ub=[[float(x) for x in row]+[-1] for row in A], b_ub=[0]*m,A_eq=[[1]*n+[0]],b_eq=[1],bounds=[(0,1)]*n+[(None,None)],method='highs')
        assert sol.success
        support=[j for j,v in enumerate(sol.x[:n]) if v>1e-9]
        active=[i for i,v in enumerate(sol.ineqlin.residual) if abs(v)<1e-8]
        sys=Matrix([[Rational(A[i][j]) for j in support]+[-1] for i in active]+[[1]*len(support)+[0]])
        exact,free=sys.gauss_jordan_solve(Matrix([0]*len(active)+[1]))
        assert not free.rows
        p=[Q(0)]*n
        for j,v in zip(support,exact): p[j]=Q(v)
        val=Q(exact[-1])
        assert sum(p)==1 and min(p)>=0 and all(sum(a*b for a,b in zip(row,p))<=val for row in A)
        return p,val
    x,v=certificate(A)
    y,neg=certificate([[-A[i][j] for i in range(len(A))] for j in range(len(js))])
    assert neg==-v
    return dict(t=t,d=d,classes=js,nulls=nulls,design=list(map(str,x)),least_favorable=list(map(str,y)),worst_size=str(v),power=str(min(Q(1),Q(1,20)/v)) if v else "1")
rows=[solve_case(t,d) for t in range(3,9) for d in (7,8,9,10)]
assert all(Q(r['power'])<Q(4,5) for r in rows if r['d']==7)
assert all(Q(r['power'])==1 for r in rows if r['d']==10)
# Independently enumerate all full-block nulls for each possible number of maximum deviations.
for t in range(3,9):
    caps=[6435+679]*t+[6435-679]*t+[6435]*(16-2*t)
    assert sum(caps)==16*6435
    assert all(sum(caps[i] for i in S)<=81618 for S in combinations(range(16),12))
    for S in combinations(range(16),13):
        assert (sum(caps[i] for i in S)<=81618)==(len(set(range(t)).difference(S))==3 and sum(i>=t for i in S)==16-t)
    assert all(sum(caps[i] for i in S)>81618 for S in combinations(range(16),14))
out=Path('/content/boundary.zip')
with zipfile.ZipFile(out,'x',zipfile.ZIP_DEFLATED) as z:z.writestr('boundary.json',json.dumps(dict(tolerance=679,g=16,alpha='1/20',rows=rows),indent=2))
print('archive_sha256 '+hashlib.sha256(out.read_bytes()).hexdigest())
