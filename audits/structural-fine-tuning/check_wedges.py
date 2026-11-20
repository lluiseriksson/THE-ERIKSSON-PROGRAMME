"""Rational witnesses for the two oriented wedges. Python 3, standard library."""
from fractions import Fraction as Q
import json

def dot(a, b):
    return sum(x*y for x,y in zip(a,b))

def add(x,y,scale=1):
    return tuple(a+scale*b for a,b in zip(x,y))

def check(ok, message):
    if not ok:
        raise ValueError(message)

def audit(r, eps):
    d=1-r*r
    a=(Q(1),eps,Q(0))
    def metric(x):
        return (x[0],x[1]+r*x[2],x[2]+r*x[1])
    def risk(x,t):
        v=add(x,t,-1)
        return dot(v,metric(v))
    def feasible(x,sign):
        return sign*x[0]<=0 and dot(a,x)<=0
    factor=(1+eps**2/d)/(1+eps**2)
    origin=(Q(0),)*3
    x=(Q(0),r,Q(0))
    t=(Q(0),Q(0),Q(1))
    check(feasible(t,-1) and feasible(origin,-1),"Minus feasibility")
    check(x==add(tuple((r/eps)*v for v in a),(-r/eps,0,0)), "Minus normal certificate")
    minus=risk(origin,t)/risk(x,t)
    check(minus==1/d,"Minus sharpness")
    # q is the M-orthogonal projection of the unit-step residual a onto its facet.
    inverse_a=(a[0],a[1]/d,-r*a[1]/d)
    q=add(a,inverse_a,-dot(a,a)/dot(a,inverse_a))
    check(dot(a,q)==0 and risk(q,origin)>0,"Facet direction")
    multiplier=risk(a,origin)/risk(q,origin)
    tangent=tuple(multiplier*v for v in q)
    e=(-eps,Q(1),Q(0))
    eta=eps/(2*(1+abs(tangent[0])))
    t=add(e,tangent,eta)
    x=add(e,a,eta)
    check(feasible(t,1) and feasible(e,1) and e[0]<0 and dot(a,e)==0,"Plus feasibility")
    check(add(x,e,-1)==tuple(eta*v for v in a) and eta>0,"Plus normal certificate")
    plus=risk(e,t)/risk(x,t)
    check(plus==factor and plus<minus,"Plus sharpness")
    return dict(r=str(r),epsilon=str(eps),plus=str(plus),minus=str(minus),
                plus_estimate=list(map(str,x)),plus_truth=list(map(str,t)),plus_projection=list(map(str,e)))

if __name__=="__main__":
    records=[audit(r,eps) for r in (Q(1,4),Q(1,2),Q(3,4),Q(99,100)) for eps in (Q(1,4),1-r*r)]
    check(records[2]["plus"]=="52/51" and records[2]["minus"]=="4/3","Manuscript example")
    print(json.dumps(records,sort_keys=True,indent=2))
