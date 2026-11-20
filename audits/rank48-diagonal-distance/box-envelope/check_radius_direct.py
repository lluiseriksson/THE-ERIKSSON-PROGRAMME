"""Evaluate eight input boxes independently from the multiplicative factors."""
from fractions import Fraction as F
import json,itertools,math
from pathlib import Path
import sympy as S
import numpy as np
doc=json.loads(Path('scheme.json').read_bytes())
certificate=json.loads(Path('polish.json').read_bytes())
assert doc['rank']==48 and certificate['field']==955614
# Exact at each point using positive rational lower/upper bounds for the four balanced row multipliers.
den=10**27;lower=math.isqrt(955614*den**2);assert lower**2<955614*den**2<(lower+1)**2
lo=(2164+2*F(lower,den))/35;hi=(2164+2*F(lower+1,den))/35
old=list(map(F,doc['meta']['row_scales']))
def scale(l,u):
    return [F(1),(7595*l-4968)/(2508*u-25320)/old[1],F(1),(1096*l+1472)/(2508*u-25320)/old[3]]
slo,shi=scale(lo,hi),scale(hi,lo)
# Per term and output, accumulate unsigned base coefficients grouped by the three sign exponents separately.
sg=list(itertools.product((-1,1),repeat=3))
def coeffs(mat):
    return [(a,b,abs(F(x))) for a,row in enumerate(mat) for b,x in enumerate(row) if F(x)]
sg=[v+(0,) for v in sg]
points=[('101/100',2420),('13291155/10000000',2420),('13291156/10000000',2922),('13291181/10000000',2922),('13291182/10000000',2898),('7/5',2898),('9/2',2898),('23/5',4532)]
# Precompute a table of conservative integer coefficient enclosures by exact fractions.
# Degree ranges for A, B, W are -2..2. Use rational t powers separately for every sign choice.
base=[]
def tables(mat,kind):
    arr=np.zeros((8,8,4,5),dtype=object)
    for a,b,v in coeffs(mat):
        for i,x in enumerate(sg):
            for j,y in enumerate(sg):
                exp=x[a]-y[b]
                arr[i,j,a,2+exp]+=v
    return arr
for U,V,W in zip(doc['u'],doc['v'],doc['w']):
    u=tables(U,'u');v=tables(V,'v').sum(axis=2)
    base.append((u,v,coeffs(W)))
rows=[]
for point,expected in points:
    t=F(point);ns=[t**i for i in range(-2,3)];pows=np.array(ns,dtype=object)
    L=np.zeros((8,8,8,16),dtype=object);H=L.copy()
    for u,v,ws in base:
        uf=u@pows
        ul=uf@np.array(slo,dtype=object);uh=uf@np.array(shi,dtype=object);vf=v@pows
        for i,k,w in ws:
            out=4*i+k
            for ix,x in enumerate(sg):
                for iz,z in enumerate(sg):
                    wd=w*t**(z[k]-x[i])
                    L[ix,:,iz,out]+=ul[ix,:]*vf[:,iz]*(wd/shi[i])
                    H[ix,:,iz,out]+=uh[ix,:]*vf[:,iz]*(wd/slo[i])
    idx=tuple(np.unravel_index(L.argmax(),L.shape))
    win=512*int(idx[3])+64*int(idx[0])+8*int(idx[1])+int(idx[2])
    winning=L[idx];H[idx]=0
    gap=winning-max(H.flat)
    assert win==expected and gap>0
    rows.append(dict(t=point,unique_winner=win,separation_lower=str(gap)))
print(json.dumps(rows))
