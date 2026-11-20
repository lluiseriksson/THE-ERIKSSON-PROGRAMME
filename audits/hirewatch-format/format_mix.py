"""Bounds from rounded trial means, without imputing missing stratum means."""
from fractions import Fraction as F
from itertools import combinations, product
import json
from pathlib import Path

def need(condition,msg):
    if not condition:raise ValueError(msg)

def model(row):
    n,m=row['n'],row['f']
    if m==n:
        return None
    need(0<m<n,'Both strata required')
    a,s,delta=(F(row[key].replace('−','-')) for key in ['all','retained','delta'])
    tol=F(1,200)
    bounds=[(u,v,center+tol) for u,v,center in
            [(1,0,a),(-1,0,-a),(0,1,s),(0,-1,-s),(-1,1,delta),(1,-1,-delta)]]
    vertices=set()
    for (u,v,b),(i,j,c) in combinations(bounds,2):
        det=u*j-v*i
        if not det:continue
        av=(b*j-v*c)/det
        sv=(u*c-b*i)/det
        if all(k*av+l*sv<=bound for k,l,bound in bounds):
            rejected=(n*av-m*sv)/(n-m)
            vertices.add((sv,rejected))
    need(vertices,'Incompatible rounded table')
    return sorted(vertices)

def interval(verts,z):
    values=[(1-z)*s+z*r for s,r in verts]
    return min(values),max(values)

def crossings(a,b):
    # Each endpoint function is affine in the common fraction of rejected-format
    # trials. Opposite signs at 0 and 1 guarantee a crossing in between.
    out=[]
    for (s1,r1),(s2,r2) in product(a,b):
        l,h=s1-s2,r1-r2
        if l*h>=0:return None
        out.append(-l/(h-l))
    return min(out),max(out)

def check(rows):
    eligible={row['model']:m for row in rows if (m:=model(row)) is not None}
    robust={}
    for a,b in combinations(eligible,2):
        ia,ib=interval(eligible[a],0),interval(eligible[b],0)
        ja,jb=interval(eligible[a],1),interval(eligible[b],1)
        if (ia[1]<ib[0] and ja[0]>jb[1]) or (ib[1]<ia[0] and jb[0]>ja[1]):
            robust[a+' vs '+b]=list(map(str,crossings(eligible[a],eligible[b])))
    A,B='Sonnet 4.6','Mistral Small'
    lo,hi=crossings(eligible[A],eligible[B])
    need(F(2,100)<lo<=hi<F(4,100),'Named crossing')
    z2,z4=F(1,50),F(1,25)
    need(interval(eligible[A],z2)[1]<interval(eligible[B],z2)[0] and
         interval(eligible[A],z4)[0]>interval(eligible[B],z4)[1],'Rank witnesses')
    bad=dict(rows[0],delta='99.99')
    try:model(bad)
    except ValueError:pass
    else:raise ValueError('Contradictory shift admitted')
    return dict(eligible=list(eligible),missing_stratum=[r['model'] for r in rows if r['f']==r['n']],
                robust_reversals=robust,rounding='closed half-unit at two decimals; table precision only',
                sonnet_excluded=list(map(str,interval(eligible[A],1))),
                named_threshold=list(map(str,(lo,hi))),
                named_examples={str(z):{t:list(map(str,interval(eligible[t],z))) for t in (A,B)} for z in (z2,z4)})
if __name__=='__main__':
    print(json.dumps(check(json.loads(Path(__file__).with_name('table17.json').read_bytes())['rows']),indent=2,sort_keys=True))

