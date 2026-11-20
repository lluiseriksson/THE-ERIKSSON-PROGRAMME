"""Recover format strata for the complement of a nested benchmark summary."""
from fractions import Fraction as Q
from itertools import combinations, product
from pathlib import Path
import json

def require(test, message):
    if not test:
        raise ValueError(message)

def hull(points):
    points = sorted(set(points))
    if len(points) < 3:
        return points
    def chain(vertices):
        edge = []
        for p in vertices:
            while len(edge) >= 2:
                a,b = edge[-2:]
                if (b[0]-a[0])*(p[1]-a[1]) > (b[1]-a[1])*(p[0]-a[0]):
                    break
                edge.pop()
            edge.append(p)
        return edge
    return chain(points)[:-1] + chain(reversed(points))[:-1]

def totals(row):
    n,m = row['n'],row['f']
    require(0 < m <= n,'Unexpected trial counts')
    a,f,d = (Q(row[k].replace('−','-')) for k in ('all','retained','delta'))
    h = Q(1,200)
    planes = [(1,0,a+h),(-1,0,h-a),(0,1,f+h),(0,-1,h-f),
              (-1,1,d+h),(1,-1,h-d),(0,-1,0),(-n,m,0)]
    if n == m:
        planes.append((1,-1,0))
    points = []
    for (i,j,k),(u,v,w) in combinations(planes,2):
        det = i*v-j*u
        if det:
            A,F = Q(k*v-w*j,det),Q(i*w-u*k,det)
            if all(x*A+y*F <= z for x,y,z in planes):
                points.append((m*F,n*A-m*F))
    require(points,'Incompatible summaries for '+row['model'])
    return hull(points)

def clip_nonnegative(points,axis):
    if not points:
        return []
    out = [p for p in points if p[axis]>=0]
    for a,b in zip(points,points[1:]+points[:1]):
        if a[axis]*b[axis]<0:
            t = a[axis]/(a[axis]-b[axis])
            out.append(tuple(x+t*(y-x) for x,y in zip(a,b)))
    return hull(out)

def recover(base,grid):
    nb,mb,ng,mg = base['n'],base['f'],grid['n'],grid['f']
    good,bad = mg-mb,ng-nb-(mg-mb)
    require(ng==4*nb and good>0 and bad>=0,'Unexpected nesting')
    inputs,pooled = totals(base),totals(grid)
    candidates = hull((g-a,h-b) for (g,h),(a,b) in product(pooled,inputs))
    for axis in (0,1):
        candidates = clip_nonnegative(candidates,axis)
    require(candidates,'Nonnegative complement infeasible')
    if not bad:
        require(any(b==0 for a,b in candidates),'Empty excluded stratum must contribute zero')
    standard = [(a/good,b/bad) for a,b in candidates] if bad else []
    baseline = [(a/mb,b/(nb-mb)) for a,b in inputs] if nb>mb else []
    return baseline,standard,[good,bad]

def score(p,z):
    return p[0]+z*(p[1]-p[0])

def contrast(a,b,z):
    left = [score(p,z) for p in a]
    right = [score(p,z) for p in b]
    return [min(left)-max(right),max(left)-min(right)]

def crossing(a,b):
    first,last = contrast(a,b,0),contrast(a,b,1)
    if not (first[1]<0<last[0] or last[1]<0<first[0]):
        return None
    roots = [(p[0]-q[0])/(p[0]-q[0]+q[1]-p[1]) for p,q in product(a,b)]
    return [min(roots),max(roots)]

def inspect(regime):
    a,b = (regime[k] for k in ('Sonnet 4.6','Mistral Small'))
    thresholds = {}
    for i,j in combinations(sorted(regime),2):
        if (t:=crossing(regime[i],regime[j])) is not None:
            thresholds[i+' / '+j] = list(map(str,t))
    return dict(eligible=len(regime),reversals=thresholds,
                intervals={str(z):list(map(str,contrast(a,b,z))) for z in (0,Q(1,50),Q(1,25),1)},
                named_threshold=list(map(str,crossing(a,b) or [])))

def main():
    folder = Path(__file__).resolve().parent
    r0,rg = [json.loads((folder/n).read_bytes())['rows'] for n in ('table17.json','full-grid.json')]
    g = {r['model']:r for r in rg}
    require(len(g)==len(rg)==len(r0)==len({r['model'] for r in r0})==18,'Duplicate or missing models')
    baseline,explicit,counts = {},{},{}
    for r in r0:
        k = r['model']
        a,b,counts[k] = recover(r,g[k])
        if a: baseline[k]=a
        if b: explicit[k]=b
    require(clip_nonnegative([(-1,Q(1)),(1,Q(1))],0)==[(0,1),(1,1)],'Axis clipping control')
    require(set(totals(dict(n=100,f=100,all='1',retained='1',delta='0',model='control')))=={(Q(199,2),0),(Q(201,2),0)},'Saturated stratum control')
    x,y = inspect(baseline),inspect(explicit)
    require(len(x['reversals'])==31 and x['named_threshold']==['362/13097','366/13097'],'Table 17 replication')
    return dict(baseline=x,explicit=y,counts=counts)
if __name__=='__main__':
    print(json.dumps(main(),indent=2,sort_keys=True))
