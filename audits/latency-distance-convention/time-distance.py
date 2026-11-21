"""Enclose the Table 2-to-3 replication and workload-shift certificate in rational arithmetic."""
from fractions import Fraction as F
from itertools import product
from math import isqrt
import json

def dot(a,b):
    return sum(x*y for x,y in zip(a,b))

def solve(matrix, vector):
    a=[row[:]+[rhs] for row,rhs in zip(matrix,vector)]
    for i in range(len(a)):
        # Principal submatrices of the full-rank design Gram matrix are positive definite.
        v=a[i][i]
        if not v:
            raise ValueError("Nonpositive principal pivot")
        a[i]=[x/v for x in a[i]]
        for j in range(len(a)):
            if j!=i:
                factor=a[j][i]
                a[j]=[x-factor*y for x,y in zip(a[j],a[i])]
    return [row[-1] for row in a]

def sqrt_bracket(v):
    n=isqrt(v.numerator*10**12//v.denominator)
    return [n/10**6,(n+1)/10**6]

data=json.load(open("fuente.json"))
lengths=list(product(data["grid"]["input"],data["grid"]["output"]))
X=[[i,i*i,o,i*o] for i,o in lengths]
if len(set(lengths))!=80: raise ValueError('Grid')
K=list(range(4))
G=[[F(sum(row[i]*row[j] for row in X),len(X)) for j in K] for i in K]
d=[F(y)-F(x) for x,y in zip(data["api"],data["local"])]
half=[F(a)+F(b) for a,b in zip(data["api_halfwidth"],data["local_halfwidth"])]
bounds=[(m-h,m+h) for m,h in zip(d,half)]
def squared(b):
    return dot(b,[dot(row,b) for row in G])
center=squared(d)
if center!=sum(dot(x,d)**2 for x in X)/len(X): raise ValueError('Direct RMS mismatch')
points=[]
for face in product((-1,0,1),repeat=4):
    free=[i for i in K if not face[i]]; fixed=[i for i in K if face[i]]
    b=[bounds[i][int(face[i]>0)] if i in fixed else F(0) for i in K]
    optimum=solve([[G[i][j] for j in free] for i in free],[-sum(G[i][j]*b[j] for j in fixed) for i in free])
    for i,val in zip(free,optimum): b[i]=val
    if all(lo<=v<=hi for v,(lo,hi) in zip(b,bounds)):
        points.append((squared(b),b))
minimum,bmin=min(points);maximum,bmax=max(points)
if minimum!=sum(dot(x,bmin)**2 for x in X)/len(X) or maximum!=max(squared(v) for v in product(*bounds)):
    raise ValueError('Extremum crosscheck')
W=F(data['reported_winner']);R=F(data['reported_second']);unit=F(1,2)
compatible=max(minimum,(W-unit)**2)<=min(maximum,(W+unit)**2)
res=dict(cells=len(X),central_ms=sqrt_bracket(center),sharp_rounding_rms_ms=[sqrt_bracket(minimum)[0],sqrt_bracket(maximum)[1]],reported_ms=[float(W-unit),float(W+unit)],compatible=compatible,central_squared=str(center),min_squared=str(minimum),max_squared=str(maximum),minimizer=list(map(str,bmin)),maximizer=list(map(str,bmax)),valid_face_solutions=len(points))
if compatible:
    cell_bounds=[max(abs(dot(x,v)) for v in product(*bounds)) for x in X]
    worst=max(cell_bounds);idx=cell_bounds.index(worst)
    spread=(R-unit)**2-min(maximum,(W+unit)**2)
    f=spread/(spread+worst**2)
    res['arbitrary_redistribution']=dict(lower_threshold=str(f),decimal=float(f),bounding_cell=lengths[idx],bound_cell_ms=str(worst),condition='(1-t) uniform + t arbitrary, bound applies for t strictly below threshold')
print(json.dumps(res,sort_keys=True,indent=2))