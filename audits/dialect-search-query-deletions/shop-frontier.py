"""Operating frontier under extra weight on repeated events and a cost on false hits."""
from fractions import Fraction as F
from itertools import combinations
import json,math
# Sweity, Table 3, percent success (unique,event), false hit (unique,event).
data={'M0':(439,344,0,0),'M1':(491,387,0,0),'M2':(614,656,59,77),'M2a':(825,828,294,231),'M2b':(684,742,118,115),'M3':(895,914,471,423),'LIVE':(895,935,529,462)}
def table():
    out={}
    for name,row in data.items():
        values=[]
        for p,n in zip(row,[57,93,17,26]):
            choices=[i for i in range(n+1) if abs(1000*i-p*n)*2<n]
            if len(choices)!=1:raise ValueError((name,p,n))
            values.append(choices[0])
        out[name]=values
    return out
def slopes(t):
    points={}
    for k,(a,b,c,d) in table().items():points[k]=(c+t*(d-c),a+t*(b-a))
    stack=[]
    for k in sorted(points,key=lambda k:(points[k][0],-points[k][1])):
        x,y=points[k]
        if stack and (points[stack[-1]][0]==x or points[stack[-1]][1]>=y):continue
        while len(stack)>=2:
            a,b=stack[-2:];xa,ya=points[a];xb,yb=points[b]
            if (yb-ya)*(x-xb)>(y-yb)*(xb-xa):break
            stack.pop()
        stack.append(k)
    return stack,[str(F(points[b][1]-points[a][1],points[b][0]-points[a][0])) for a,b in zip(stack,stack[1:])]
def run():
    import sympy as sp
    t=sp.Symbol('t');tab=table();P={k:(c+t*(d-c),a+t*(b-a)) for k,(a,b,c,d) in tab.items()};crossings={sp.Integer(0),sp.Integer(1)}
    for a,b,c in combinations(P,3):
        xa,ya=P[a];xb,yb=P[b];xc,yc=P[c]
        poly=sp.expand((xb-xa)*(yc-ya)-(xc-xa)*(yb-ya))
        if poly!=0:crossings.update(r for r in sp.solve(poly,t) if r.is_real and 0<r<1)
    # The x order is fixed for 0<t<1 because endpoint orders are compatible.
    for a,b in combinations(P,2):
        delta=P[a][0]-P[b][0];assert delta.subs(t,0)*delta.subs(t,1)>=0
    intervals=[];cuts=sorted(crossings,key=float)
    for l,u in zip(cuts,cuts[1:]):
        mid=F(str(((l+u)/2).evalf(24)))
        h,_=slopes(mid)
        if intervals and h==intervals[-1]['strict_hull']:intervals[-1]['right']=str(u)
        else:intervals.append(dict(left=str(l),right=str(u),strict_hull=h))
    return dict(tab=tab,rounding='tenths of percentage points; integer solution unique in each denominator',positive_cost_intervals=intervals,boundary0=slopes(F(0)),boundary1=slopes(F(1)),interior_collinearities=[str(r) for r in cuts[1:-1]])
if __name__=='__main__':print(json.dumps(run(),sort_keys=True))
