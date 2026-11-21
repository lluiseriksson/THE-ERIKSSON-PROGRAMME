"""Area-weighted compatibility of two candidate maps. Standard library only."""
from fractions import Fraction as F
from itertools import combinations, product
from pathlib import Path
import json, math

def constraints(a,b,i,u,j):
    """a,b,i are areas, u=a+b-i. Include printed union and IoU rounding."""
    half=F(1,200)
    cons=[]
    for v,c in [((1,0,0),a),((0,1,0),b),((0,0,1),i),((1,1,-1),u)]:
        cons.extend([(v,c+half),(tuple(-x for x in v),-c+half)])
    # (j-h)u <= i <= (j+h)u
    lo,hi=j-half,j+half
    cons.extend([((lo,lo,-1-lo),0),((-hi,-hi,1+hi),0)])
    return cons
def dot(a,b):
    return sum(x*y for x,y in zip(a,b))
def cross(a,b):
    return (a[1]*b[2]-a[2]*b[1],a[2]*b[0]-a[0]*b[2],a[0]*b[1]-a[1]*b[0])
def vertices(h):
    out=set()
    for (r,d),(s,e),(t,f) in combinations(h,3):
        v,w,z=cross(s,t),cross(t,r),cross(r,s)
        det=dot(r,v)
        if det:
            x=tuple(F(d*v[k]+e*w[k]+f*z[k],det) for k in range(3))
            if all(dot(n,x)<=k for n,k in h):out.add(x)
    return out
def compatible(a,b,i,r):
    u=a+b-i
    return b*(1-r)+i*r-u*r*r>=0
def bound(vs,all_vertices):
    test=all if all_vertices else any
    lo,hi=0,1000000
    while hi-lo>1:
        mid=(lo+hi)//2
        if test(compatible(*x,F(mid,1000000)) for x in vs):lo=mid
        else:hi=mid
    return [lo,hi]
def check_small():
    # Independently bound any discrete centre using exhaustive masks on five nonuniform cells.
    tests=0
    weights=[1,4,2,3,6]
    mass=[sum(w for k,w in enumerate(weights) if bits>>k&1) for bits in range(32)]
    for a,b in product(range(1,32),repeat=2):
        A,B=sorted((mass[a],mass[b]),reverse=True);I=mass[a&b]
        best=max(min(F(mass[a&c],mass[a|c]),F(mass[b&c],mass[b|c])) for c in range(32))
        assert compatible(A,B,I,best)
        tests+=1
    return tests

def run():
    data=json.loads(Path('tables-values.json').read_bytes())['t05'][0]
    ans={}
    for key,k in [('AlphaEarth',2),('Tessera',10)]:
        assert 'Strongest' in data[k][0]
        similarity=F(str(data[k+1][2]))
        h=constraints(*(F(str(data[k+n][2])) for n in [2,3,4,5,6]))
        vs=vertices(h);assert vs and all(a>=b>=i>0 for a,b,i in vs)
        phi=math.acos(float(similarity-F(1,200)));theta=math.acos(.9)
        ans[key]=dict(vertex_count=len(vs),min_optimum_millionths=bound(vs,True),max_optimum_millionths=bound(vs,False),
            loss_area_interval=[str(f(a-i for a,b,i in vs)) for f in (min,max)],
            gain_area_interval=[str(f(b-i for a,b,i in vs)) for f in (min,max)],
            lost_local_score_upper=math.cos(max(0,theta-phi)),entered_local_score_lower=math.cos(theta+phi),
            source_centroid_cosine=str(similarity),local_map_year=2022 if key=='AlphaEarth' else 2024,
            vertices=[[str(x) for x in v] for v in sorted(vs)])
    return dict(model='area may be subdivided; resulting upper bound applies to every pixel map',audited='P1564 Table 5',results=ans,discrete_tests=check_small())
if __name__=='__main__':print(json.dumps(run()))
