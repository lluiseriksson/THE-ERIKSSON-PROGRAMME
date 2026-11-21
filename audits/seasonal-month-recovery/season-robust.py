"""Minimax error with bounded means, bounded anchor errors and one arbitrary anchor."""
from fractions import Fraction as F
from itertools import combinations
from functools import lru_cache
import runpy,json
invert=runpy.run_path('season-inverse.py')['invert']
win=tuple(tuple(F(int(j<=i<j+3),3) for i in range(6)) for j in range(4))
eye=tuple(tuple(int(i==j) for i in range(6)) for j in range(6))
@lru_cache(None)
def recovery(anchors):
    rows=win+tuple(eye[i] for i in anchors);cost=[None]*6
    for chosen in combinations(rows,6):
        inv=invert(chosen)
        if inv:
            for j,line in enumerate(inv):
                c=sum(abs(x) for x in line)
                if cost[j] is None or c<cost[j]:cost[j]=c
    if any(v is None for v in cost):return None
    from scipy.optimize import linprog
    import numpy as np
    H=np.array(rows,dtype=float)
    for j in range(6):
        sol=linprog(-np.eye(6)[j],A_ub=np.vstack([H,-H]),b_ub=np.ones(2*len(H)),bounds=[(None,None)]*6,method='highs')
        if not sol.success or abs(-sol.fun-float(cost[j]))>1e-8:raise ArithmeticError(('dual mismatch',anchors,j))
    return max(cost)
def run():
    out={}
    for n in range(2,7):
        for bad in range(2):
            for subset in combinations(range(6),n):
                costs=[recovery(v) for v in combinations(subset,n-2*bad)]
                key=','.join(str(i+1) for i in subset)
                out.setdefault(str(bad),{})[key]=None if None in costs else str(max(costs))
    return out
if __name__=='__main__':print(json.dumps(run(),sort_keys=True))
