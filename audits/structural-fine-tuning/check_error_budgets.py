"""Independent rational check using all feasible face projections of a planar wedge."""
from fractions import Fraction as Q
from itertools import product
import json

def verify(condition, label):
    if not condition:
        raise ValueError(label)

def sqdist(x, y):
    return sum((a-b)**2 for a, b in zip(x,y))

def feasible(point, s):
    x,z=point
    return z<=0 and z<=s*x

def project(y, s):
    x,z=y
    coord=(x+s*z)/(1+s*s)
    candidates=[y,(x,Q(0)),(coord,s*coord),(Q(0),Q(0))]
    return min((p for p in candidates if feasible(p,s)),key=lambda p:sqdist(p,y))

def bound(s,h,L):
    return max(Q(1),(1+1/s**2)*max(Q(0),1-h/L)**2)

def audit(s,h):
    budgets=[h/2,h,2*h,5*h,10*h,100*h]
    grid=list(product(map(Q,range(-4,5)),repeat=2))
    truths=[t for t in grid if feasible(t,s)]
    tests=0
    for y in grid:
        u=(y[0],min(y[1],h))
        e=project(y,s)
        for t in truths:
            den=sqdist(u,t)
            if not den: continue
            ratio=sqdist(e,t)/den
            verify(ratio<1+1/s**2,"Finite pair attains asymptote")
            for L in budgets:
                if den<=L*L:
                    verify(ratio<=bound(s,h,L),"Budget violation")
                    tests+=1
    record=[]
    for L in budgets:
        expected=bound(s,h,L)
        if expected==1:
            y=(Q(0),Q(0));t=(Q(0),-L)
        else:
            b=L-h;a=b/s
            t=(-a,-b);y=(-a,max(h+1,a/s))
        u=(y[0],min(y[1],h));e=project(y,s)
        verify(feasible(t,s) and sqdist(u,t)==L**2 and sqdist(e,t)/L**2==expected,"Attainment")
        record.append(dict(budget=str(L),factor=str(expected),truth=list(map(str,t)),raw=list(map(str,y))))
    return dict(slope=str(s),gap=str(h),admissible_grid_comparisons=tests,sharp_witnesses=record)

if __name__=="__main__":
    rows=[audit(s,h) for s in (Q(1,4),Q(1,2),Q(1),Q(2)) for h in (Q(1),Q(3,2))]
    ref=rows[2]["sharp_witnesses"]
    verify(ref[2]["factor"]=="5/4" and ref[4]["factor"]=="81/20","Reported example")
    curved=[]
    for power in range(4,13):
        q=Q(1,2**power); delta=3*q+2*q**3
        y=(delta,Q(1)); u=(delta,Q(0)); t=(delta,-delta**2); e=(q,-q**2)
        verify(delta<1 and q<1 and t[1]>=-1,"Feasibility in compact truncation")
        verify((y[0]-e[0],y[1]-e[1])==(2*q*(1+q*q),1+q*q),"Normal certificate")
        ratio=sqdist(e,t)/sqdist(u,t)
        verify(sqdist(u,t)==delta**4 and ratio>=Q(4,9)/delta**2,"Curved inflation")
        curved.append(dict(q=str(q),baseline=str(delta**2),ratio=str(ratio)))
    print(json.dumps(dict(polyhedra=rows,curved=curved),sort_keys=True,indent=2))

