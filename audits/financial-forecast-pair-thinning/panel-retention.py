"""Exact finite-panel calculation for the published strict-sample aggregate tables."""
from fractions import Fraction as F
from itertools import combinations,product
import json
def mean(xs):return sum(xs,F(0))/len(xs)
def occupancy(inds):return tuple(sorted((sum(i//2==g for i in inds) for g in range(3)),reverse=True))
def factors(shape):
    k=sum(shape)
    return F(3*sum(l*l for l in shape)-k*k,2*k*k), F(shape.count(1),k*k)
def average_checks():
    cells={}
    for k in range(1,7):
        for group in combinations(range(6),k):cells.setdefault(occupancy(group),[]).append(group)
    checks=0
    for labels in product((0,1,2),repeat=6):
        x=[F(p,2) for p in labels];u=mean(x);g=[mean(x[i:i+2]) for i in (0,2,4)]
        B=mean([(z-u)**2 for z in g]);W=mean([(z-g[i//2])**2 for i,z in enumerate(x)])
        for shape,subsets in cells.items():
            a,b=factors(shape)
            predictions=[mean([x[i] for i in s]) for s in subsets]
            for y in (0,1):
                if mean([(p-y)**2 for p in predictions])!=(u-y)**2+a*B+b*W:raise ValueError((shape,x,y))
                checks+=1
    return checks,sorted(cells,key=lambda s:(sum(s),s))
def interval(x,digits):
    x=F(x);r=F(1,2*10**digits);return x-r,x+r
if __name__=='__main__':
    t=json.load(open('thinning.json'))
    dispersion={'GPT-4.1-mini':'0.0119','Qwen3-30B':'0.0091','OLMo-3.1-32B':'0.0113'}
    checks,cells=average_checks()
    output={'identity_checks':checks,'patterns':{},'models':{}}
    for s in cells:output['patterns'][''.join(map(str,s))]=list(map(str,factors(s)))
    for model,(e,b,w) in t['effects'].items():
        E=interval(e,5);B=interval(b,4);W=interval(w,4)
        rows={}
        for s in cells:
            alpha,beta=factors(s)
            rows[''.join(map(str,s))]=[str(x+alpha*y+beta*z) for x,y,z in zip(E,B,W)]
        permitted=[s for s in cells if sum(s)>=3]
        cap=max(max(factors(s)) for s in permitted)
        if cap!=F(1,3):raise ValueError('occupancy cap')
        D=interval(dispersion[model],4)
        upper=E[1]+cap*D[1]
        if upper>=0:raise ValueError('adaptive retention guarantee')
        output['models'][model]={'fixed':rows,'C3_dispersion':dispersion[model],'adaptive_vs_full_upper':str(upper)}
    print(json.dumps(output,indent=2))