"""Exact audit for four overlapping three-month means on six unknown monthly values."""
from fractions import Fraction as F
from itertools import combinations
import json

def invert(rows):
    n=len(rows);m=[list(map(F,r))+[F(i==j) for j in range(n)] for i,r in enumerate(rows)]
    for j in range(n):
        k=next((i for i in range(j,n) if m[i][j]),None)
        if k is None:return
        m[j],m[k]=m[k],m[j];pivot=m[j][j];m[j]=[x/pivot for x in m[j]]
        for i in range(n):
            if i!=j:
                b=m[i][j];m[i]=[x-b*y for x,y in zip(m[i],m[j])]
    return [r[n:] for r in m]
def answer():
    n=6;win=[[F(int(j<=i<j+3),3) for i in range(n)] for j in range(4)]
    out={}
    for a,b in combinations(range(n),2):
        rows=win+[[int(i==j) for i in range(n)] for j in (a,b)]
        inv=invert(rows)
        if bool(inv)!=((a-b)%3!=0):raise ArithmeticError('Kernel mismatch')
        if inv:
            if any(sum(inv[i][k]*rows[k][j] for k in range(n))!=(i==j) for i in range(n) for j in range(n)):raise ArithmeticError('Product')
            norms=[sum(abs(x) for x in row) for row in inv];worst=max(norms);row=inv[norms.index(worst)]
            error=[(x>0)-(x<0) for x in row]
            if sum(x*y for x,y in zip(error,row))!=worst:raise ArithmeticError('Bound not sharp')
            out[f'{a+1},{b+1}']=str(worst)
        else:out[f'{a+1},{b+1}']=None
    distances={}
    for size in range(2,7):
        v=[]
        for chosen in combinations(range(n),size):
            counts=[sum(i%3==j for i in chosen) for j in range(3)]
            witnesses=[[1,-1,0],[1,0,-1],[0,1,-1],[1,1,-2]]
            dist=min(sum(w[i%3]!=0 for i in chosen) for w in witnesses)
            if dist!=size-max(counts):raise ArithmeticError('Distance')
            v.append(dist)
        distances[size]=max(v)
    return dict(months=['Dec','Jan','Feb','Mar','Apr','May'],max_error_by_pair=out,best_anchor_distances=distances,noise='absolute bound one on each of four means and both known monthly values')
if __name__=='__main__':print(json.dumps(answer()))
