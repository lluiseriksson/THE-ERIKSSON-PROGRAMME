"""Certified piecewise-linear radii for unequal seasonal and monthly error bounds."""
from fractions import Fraction as F
from itertools import combinations
from functools import lru_cache
import json,runpy
invert=runpy.run_path('season-inverse.py')['invert']
months=tuple(range(6))
means=[tuple(F(int(i<=j<i+3),3) for j in months) for i in range(4)]
unit=[tuple(int(j==i) for j in months) for i in months]
@lru_cache(None)
def coefficients(retained):
    rows=means+[unit[i] for i in retained]
    coords=[set() for _ in months]
    for inds in combinations(range(len(rows)),6):
        inv=invert([rows[i] for i in inds])
        if inv is None:continue
        for j,line in enumerate(inv):
            coords[j].add(tuple(sum(abs(x) for x,i in zip(line,inds) if (i<4)==which) for which in [True,False]))
    return [tuple((a,b) for a,b in g if not any((c,d)!=(a,b) and c<=a and d<=b for c,d in g)) for g in coords]
def val(line,x):return line[0]*x+line[1]
def fmt(line):return list(map(str,line))
def solve():
    from scipy.optimize import linprog
    import numpy as np
    output={}
    for n in [5,6]:
        for sample in combinations(months,n):
            groups=[(r,g) for r in combinations(sample,n-2) for g in coefficients(r)]
            assert all(g for r,g in groups)
            lines=set(v for r,g in groups for v in g)
            cuts={F(0)}|{(d-b)/(a-c) for (a,b),(c,d) in combinations(lines,2) if a!=c and (d-b)/(a-c)>0}
            segments=[]
            for l,u in zip(sorted(cuts),sorted(cuts)[1:]+[None]):
                x=(l+u)/2 if u else l+1
                line=max((min(g,key=lambda h:val(h,x)) for r,g in groups),key=lambda h:val(h,x))
                if not segments or segments[-1]['line']!=fmt(line):segments.append(dict(start=str(l),line=fmt(line)))
            witnesses={}
            for x in [F(0),F(1,4),F(1),F(4)]:
                best=-1;wit=None
                for r in combinations(sample,n-2):
                    H=np.array(means+[unit[i] for i in r],dtype=float)
                    rhs=np.array([float(x)]*4+[1.]*len(r))
                    for j in months:
                        lp=linprog(-np.eye(6)[j],A_ub=np.vstack([H,-H]),b_ub=np.tile(rhs,2),bounds=[(None,None)]*6,method='highs')
                        dual=min(val(h,x) for h in coefficients(r)[j])
                        assert lp.success and abs(-lp.fun-float(dual))<1e-8
                        if dual>best:
                            best=dual;vec=tuple(F(float(t)).limit_denominator(10000) for t in lp.x)
                            assert vec[j]==best and all(abs(sum(a*b for a,b in zip(row,vec)))<=bound for row,bound in zip(means+[unit[i] for i in r],[x]*4+[F(1)]*len(r)))
                            wit=dict(j=j+1,survivors=[i+1 for i in r],h=list(map(str,vec)),radius=str(best))
                formula=next(seg for seg in reversed(segments) if F(seg['start'])<=x)
                assert best==val(tuple(map(F,formula['line'])),x)
                witnesses[str(x)]=wit
            if witnesses['1']['radius']!=('11' if n==5 else '7'):raise ValueError('Equal-noise mismatch')
            output[','.join(str(i+1) for i in sample)]=dict(segments=segments,witnesses=witnesses)
    return output
if __name__=='__main__':print(json.dumps(solve(),sort_keys=True))
