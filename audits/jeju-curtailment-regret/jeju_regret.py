"""Exact polygonal regret bounds for rounded samples in the Jeju study."""
from fractions import Fraction as F
from itertools import combinations, product
from pathlib import Path
from math import floor, ceil
import json

def require(cond, message):
    if not cond:
        raise ValueError(message)

def segment_value(knots, x):
    for (lo, a), (hi, b) in zip(knots, knots[1:]):
        if lo <= x <= hi:
            return a + (x-lo)*(b-a)/(hi-lo)
    raise ValueError('Share outside recorded range')

def worst_regret(knots, x):
    return max(segment_value(row,x) for row in knots.values())

def minimax(rows, lo, hi):
    breaks=sorted({lo,hi}|{x for row in rows.values() for x,_ in row if lo<x<hi})
    candidates=set(breaks)
    for a,b in zip(breaks,breaks[1:]):
        for p,q in combinations(rows.values(),2):
            left=segment_value(p,a)-segment_value(q,a)
            right=segment_value(p,b)-segment_value(q,b)
            if left*right<0:
                candidates.add(a+(b-a)*left/(left-right))
    risk,x=min((worst_regret(rows,x),x) for x in candidates)
    return x,risk

def rounded_wind(cap,share):
    nominal=cap*F(share)/100
    return sorted({floor(nominal),ceil(nominal)})

def allocation_bound(row,x,cap):
    if any(s==x for s,_ in row):
        return dict(row)[x]
    for (l,u),(r,v) in zip(row,row[1:]):
        if l<x<r:
            placements=product(rounded_wind(cap,l),rounded_wind(cap,r),rounded_wind(cap,x))
            vals=[]
            for a,b,t in placements:
                require(a<=t<=b and a<b,'Rounding reverses knots')
                vals.append(u+(v-u)*F(t-a,b-a))
            return max(vals)
    raise ValueError('Unbracketed input')

def run(data,extra):
    tabs=data['tables'];t9={int(r[0]):int(r[2]) for r in tabs['9']}
    t10={int(r[0]):r for r in tabs['10']}
    lo=100*F(int(t10[2029][2]),t9[2030]);hi=100*(1-F(int(t10[2029][3]),t9[2030]))
    require(all(t9[y]>=t9[y-1] for y in range(2031,2039)),'Total capacity decreases')
    rows={}
    for r in tabs['11']:
        y=int(r[0]);centre=F(t10[y][1]);levels={centre+delta:F(s.split('/')[0]) for delta,s in zip([-10,-5,0,5,10],r[1:])}
        base=levels[centre];require(base==F(t10[y][5]),'Centre mismatch')
        if extra and y==2038:levels[F(extra['share_percent'])]=F(extra['energy_GWh'])
        row=sorted((x,F(0) if x==centre else h-base+F(1,10)) for x,h in levels.items())
        slopes=[(v-u)/(b-a) for (a,u),(b,v) in zip(row,row[1:])]
        require(slopes==sorted(slopes) and all(v>=0 for _,v in row),'Endpoint witness fails convexity or reference optimality')
        rows[y]=row
    x,risk=minimax(rows,lo,hi)
    # The lower certificate comes from convexity of the maximum: active slopes bracket zero.
    active=[y for y,p in rows.items() if segment_value(p,x)==risk]
    slopes=[(v-u)/(b-a) for y in active for (a,u),(b,v) in zip(rows[y],rows[y][1:]) if a<=x<=b]
    require(min(slopes)<=0<=max(slopes),'No interior optimality certificate')
    grid={j:worst_regret(rows,F(j)) for j in range(ceil(lo),floor(hi)+1)}
    rounded={j:{y:allocation_bound(p,F(j),t9[y]) for y,p in rows.items()} for j in grid}
    return dict(feasible=[lo,hi],continuous=dict(share=x,GWh=risk,active=active,slopes=slopes),
                grid=grid,rounded_MW_upper=rounded,vertices=rows)
if __name__=='__main__':
    data=json.loads(Path('planning-tables.json').read_text());point=json.loads(Path('extra-point.json').read_text())
    print(json.dumps({'table_only':run(data,None),'with_extra_point':run(data,point)},default=str,sort_keys=True,indent=2))

