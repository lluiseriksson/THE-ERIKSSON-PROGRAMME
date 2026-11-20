"""Certify transportation problems over the nine published benchmark strata."""
import json
from pathlib import Path
from fractions import Fraction as F
from itertools import chain
import sympy as sp
from scipy.optimize import linprog

def require(ok, msg):
    if not ok:
        raise ValueError(msg)

def dot(a,b):
    return sum(x*y for x,y in zip(a,b))

def exact_candidate(matrix, rhs, candidate):
    # Recover the rational basic point by supplementing the defining
    # equalities with its tight zero bounds and checking them exactly.
    rows=[list(row) for row in matrix]; vals=list(rhs)
    for j,val in enumerate(candidate):
        if abs(val)<1e-8:
            rows.append([int(i==j) for i in range(len(candidate))]); vals.append(0)
    return unique(rows,vals)

def unique(rows,values):
    M=sp.Matrix(rows); indexes=M.T.rref()[1]
    if len(indexes)!=M.cols: raise ValueError('Certificate has a free coordinate')
    ids=list(indexes)
    ans=M[ids,:].inv()*sp.Matrix([values[i] for i in ids])
    return [F(x) for x in ans]

def certify(A,b,c):
    # Standard-form minimisation with nonnegative variables.
    sol=linprog(list(map(float,c)),A_eq=[list(map(float,row)) for row in A],b_eq=list(map(float,b)),bounds=(0,None),method='highs-ds')
    require(sol.success,sol.message)
    x=exact_candidate(A,b,sol.x)
    require(min(x)>=0 and all(dot(row,x)==rhs for row,rhs in zip(A,b)),'Infeasible primal')
    cols=list(zip(*A)); dualrows=[]; dualrhs=[]
    for col,cost,reduced in zip(cols,c,sol.lower.marginals):
        if abs(reduced)<1e-8:
            dualrows.append(col);dualrhs.append(cost)
    y=unique(dualrows,dualrhs)
    require(all(dot(col,y)<=cost for col,cost in zip(cols,c)),'Infeasible dual')
    value=dot(c,x)
    require(value==dot(b,y),'Duality mismatch')
    return dict(value=str(value),x=list(map(str,x)),y=list(map(str,y)))

def read_rows(data):
    counts=data['counts'];rates={};issues={}
    for row in data['rows']:
        name=row[0];vals=[];bad=[];nums=[]
        for j,n in enumerate(counts):
            p=F(row[1+j+j//3]);den=3*n
            lo=(p-F(1,20))*den/100;hi=(p+F(1,20))*den/100
            a=-(-lo.numerator//lo.denominator);z=hi.numerator//hi.denominator
            if a!=z:
                bad.append(j);vals.append((p+F(1,20))/100);nums.append(None)
            else:vals.append(F(a,den));nums.append(a)
        for k,idx in enumerate([[0,1,2],[3,4,5],[6,7,8],list(range(9))]):
            if any(nums[j] is None for j in idx):continue
            reconstructed=F(100*sum(nums[j] for j in idx),3*sum(counts[j] for j in idx))
            if abs(reconstructed-F(row[[4,8,12,13][k]]))>F(1,20):
                bad.append('aggregate'+str(k))
        if bad:
            # Use a conservative upper envelope for every cell of this row.
            issues[name]=bad
            vals=[(F(row[1+j+j//3])+F(1,20))/100 for j in range(9)]
        rates[name]=vals
    return rates,issues

def run(data):
    n=data['counts'];rates,issues=read_rows(data); names=list(rates)
    require(len(names)==12 and not any(name in issues for name in names[:2]),'Leader data')
    g=[x-y for x,y in zip(rates[names[0]],rates[names[1]])]
    A=[[int(j//3==i) for j in range(9)] for i in range(3)]+[[int(j%3==i) for j in range(9)] for i in range(2)]
    b=[dot(row,n) for row in A];minimum=certify(A,b,g);negmax=certify(A,b,[-x for x in g])
    # x=cell weights, t=mass added in each cell, s=slack in x-t<=n.
    E=[row+[0]*18 for row in A]+[g+[0]*18]
    for i in range(9):
        eye=[int(i==j) for j in range(9)]
        E.append(eye+[-v for v in eye]+eye)
    nearest=certify(E,b+[0]+n,[0]*9+[1]*9+[0]*9)
    alt=[1,41,37,65,2,29,1,23,1]
    require(min(alt)>0 and all(dot(row,alt)==rhs for row,rhs in zip(A,b)) and dot(g,alt)<0,'Interior reversal')
    separation={}
    for name in names[2:]:
        # z is 200 plus a margin in expected successful tasks.
        E=[row+[0,0,0] for row in A]
        for i in [0,1]:
            E.append([x-y for x,y in zip(rates[names[i]],rates[name])]+[-1,int(i==0),int(i==1)])
        cert=certify(E,b+[-200,-200],[0]*9+[1,0,0])
        separation[name]={'floor':str((F(cert['value'])-200)/200),'certificate':cert}
    return dict(counts=n,leaders=names[:2],gaps=list(map(str,g)),denominator_issues=issues,minimum=minimum,negative_maximum=negmax,nearest_tie=nearest,radius=str(F(nearest['value'])/200),original=str(dot(n,g)/200),interior_witness=alt,interior_gap=str(dot(alt,g)/200),separation=separation)
if __name__=='__main__':
    print(json.dumps(run(json.loads(Path(__file__).with_name('compact-cells.json').read_bytes())),indent=2,sort_keys=True))

