"""Exact support and heterogeneity certificates for arithmetic means of positive ratios."""
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import json

def solve(matrix,rhs):
    m=[list(row)+[v] for row,v in zip(matrix,rhs)]
    n=len(m)
    for k in range(n):
        pivot=next((i for i in range(k,n) if m[i][k]),None)
        if pivot is None:return None
        m[k],m[pivot]=m[pivot],m[k]
        d=m[k][k];m[k]=[v/d for v in m[k]]
        for i in range(n):
            if i!=k:
                t=m[i][k];m[i]=[v-t*b for v,b in zip(m[i],m[k])]
    return [row[-1] for row in m]

def ratios(s):
    return [sum(a/b for a,b in zip(s[i],s[j]))/len(s[0]) for i,j in [(1,0),(2,0),(3,0),(2,1),(3,1),(3,2)]]

def witness3(values):
    u,v,w,p,q,r=values
    for dx in map(F,['.02','.04','.08','.16','.32','.64']):
        x=[u-dx,u,u+dx]
        ones=[F(1)]*3;ix=[1/k for k in x]
        for dy in [F(i,100) for i in range(-30,31)]:
            y=solve([ones,ix,[0,1,0]],[3*v,3*p,v+dy])
            if y is None or min(y)<=0:continue
            z=solve([ones,ix,[1/k for k in y]],[3*w,3*q,3*r])
            if z is None or min(z)<=0:continue
            scores=[ones,x,y,z]
            if ratios(scores)!=values:raise ValueError('Wrong witness')
            return scores
    raise RuntimeError('No three-regime witness')
def run():
    cases=json.loads(Path('hss-edges.json').read_text())['rows']
    out={}
    for k,vals in cases.items():
        means=[1+F(v)/100 for v in vals]
        bands=[(m-F(1,200*10**len(s.split('.')[1])),m+F(1,200*10**len(s.split('.')[1]))) for m,s in zip(means,vals)]
        def defect_indices(v):
            u,v,w,p,q,r=v
            return p*u/v-1,q*u/w-1,r*v/w-1
        ds=[defect_indices(c) for c in product(*bands)]
        bounds=[(min(x),max(x)) for x in zip(*ds)]
        a,b,c=bounds
        # Each defect is monotone in each of its own positive arguments, so the corner bounds are exact individually.
        gap=b[0]-a[1]
        violation=gap-c[1]
        obstruction=a[1]<0 and gap>0 and violation>0
        cov={}
        for label,(i,j,k0) in {'210':(0,3,1),'310':(0,4,2),'320':(1,5,2),'321':(3,5,4)}.items():
            lows,highs=bands[k0];low=lows-bands[i][1]*bands[j][1];high=highs-bands[i][0]*bands[j][0]
            cov[label]=[low,high,max(F(0),low,-high)]
        out[k]=dict(relative_defect_bounds=bounds,gap_lower=gap,violation_lower=violation,one_factor_impossible=obstruction,covariance=cov)
        if k=='0.5':
            if not obstruction:raise ValueError('No one-factor separation')
            out[k]['three_regime_scores']=witness3(means)
    return out
if __name__=='__main__':print(json.dumps(run(),default=str,sort_keys=True,indent=2))

