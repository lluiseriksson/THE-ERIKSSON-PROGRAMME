"""Sharp bounds over rounded margins on a finite shared inventory."""
from fractions import Fraction as Q
from itertools import product
import json

ROWS = {
    'Software Developers': [44,61,78,86,95],
    'Lawyers': [32,16,11,62,61],
    'Elementary School Teachers': [39,26,12,38,19],
    'Emergency Medicine Physicians': [38,3,0,29,29],
    'Personal Care Aides': [36,11,6,17,7],
    'Dishwashers': [13,0,0,0,0],
}

def interval(p):
    return max(0,Q(2*p-1,200)), min(1,Q(2*p+1,200))

def counts(n,p):
    l,h=interval(p)
    return [i for i in range(n+1) if l<=Q(i,n)<=h]

def project(c, e, r):
    # Cell order both, E-only, R-only, neither. Each cell's mass
    # lies between zero and u[cell]. Projection onto x = mass in both.
    u=[int(i>0) for i in c]
    low,high=Q(0),Q(u[0])
    # Every affine function is stored as (constant,slope).
    a=[(0,0),(e[0],-1)]
    b=[(u[1],0),(e[1],-1)]
    d=[(0,0),(r[0],-1)]
    f=[(u[2],0),(r[1],-1)]
    cons=list(product(a,b))+list(product(d,f))
    cons += [((v+y,s+t),(1,-1)) for (v,s),(y,t) in product(a,d)]
    cons += [((1-u[3],-1),(v+y,s+t)) for (v,s),(y,t) in product(b,f)]
    for (v,s),(w,t) in cons:
        if s==t:
            if v>w:return None
        elif s>t:high=min(high,Q(w-v,s-t))
        else:low=max(low,Q(w-v,s-t))
    if high<low:return None
    def witness(x):
        al=max(0,e[0]-x);ah=min(u[1],e[1]-x)
        dl=max(0,r[0]-x);dh=min(u[2],r[1]-x)
        total=max(al+dl,1-x-u[3])
        y=max(al,total-dh);z=total-y
        cells=[x,y,z,1-x-y-z]
        if not (al<=y<=ah and dl<=z<=dh and sum(cells)==1 and all(0<=v<=cap for v,cap in zip(cells,u))):raise ValueError('Invalid support witness')
        return cells
    return witness(low),witness(high)

def solve(row):
    n,ec,et,rc,rt=row
    e,r=interval(et),interval(rt)
    ends=[];gates=[];tables=[]
    for i,j in product(counts(n,ec),counts(n,rc)):
        for k in range(max(0,i+j-n),min(i,j)+1):
            c=[k,i-k,j-k,n-i-j+k];bounds=project(c,e,r)
            if bounds is None:continue
            t=Q(k,n);lower,upper=bounds
            for cells in bounds:ends.append((cells[0]-t,c,cells))
            if 0<t<1 and t<lower[0]<1:gates.append((lower[0]*(1-t)/(t*(1-lower[0])),c,lower))
            tables.append(dict(counts=c,lower=lower,upper=upper))
    if not ends:raise ValueError('Margins do not admit the stated denominator')
    return dict(input=row,lower=min(ends),upper=max(ends),tables=tables,
                critical_relative_time_error=min(gates) if min(ends)[0]>0 and gates else None)

if __name__=='__main__':
    print(json.dumps({k:solve(v) for k,v in ROWS.items()},default=str,indent=2))