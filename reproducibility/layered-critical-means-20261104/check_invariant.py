"""Unit127 finite exact diagnostics: own Colab Linux only, not universal proof."""
from fractions import Fraction as F
from itertools import product
from collections import Counter
import runpy
import json
import hashlib
import platform
import time

base = runpy.run_path('/content/tep128-base.py', run_name='tep128_base')
require, psd, power = base['require'], base['psd'], base['half_power']


def constants(k, D):
    require(2 <= k < D, 'invariant-coordinate scope requires 2<=k<D')
    R = F(3**k * 2**(k-1)) / (1-F(2, 3)**(k-1))
    B = 1+2*k*3**(k-1)
    C = 1+k*R*R*F(B*(D-1), D-k)**2
    r = D-k
    T = F(2**k * 3**r-1)/(1-F(2, 3)**r)
    return R, C, T


def points(box):
    return list(product(*(range(lo, hi) for lo, hi in box)))


def root_lower(m, D, denominator=2**20):
    target = m*m
    lo, hi = 0, denominator
    while F(hi, denominator)**D <= target:
        hi *= 2
    while hi-lo > 1:
        mid = (lo+hi)//2
        if F(mid, denominator)**D <= target:
            lo = mid
        else:
            hi = mid
    lower = F(lo, denominator)
    require(lower**D <= target < F(lo+1, denominator)**D, 'root enclosure')
    return lower


def check_potential(u, edges, k, R):
    sites=list(u);mean=sum(u.values(),F(0))/len(sites)
    g={x:F(0) for x in sites}
    for x,y in edges:g[x]+=abs(u[y]-u[x])
    for x in sites:
        potential=sum((g[y]/(1+max(abs(a-b) for a,b in zip(x,y)))**(k-1)
                       for y in sites),F(0))
        require(abs(u[x]-mean)<=R*potential,'finite potential bound')


def check_coverage(rectangles,n,D):
    coverage=Counter(x for b in rectangles for x in points(b))
    require(len(coverage)==n**D and all(v==1 for v in coverage.values()),'coverage')


def local(shape, D, fixture):
    k, L = len(shape), max(shape)
    R, C, _ = constants(k, D)
    box = tuple((0, l) for l in shape)
    sites = points(box)
    alpha = {x: F((1, 4, 100)[(sum((i+1)*v for i,v in enumerate(x))+fixture)%3])
             for x in sites}
    index = {x:i for i,x in enumerate(sites)}
    lap = [[F(0) for _ in sites] for _ in sites]
    edges = []
    for x in sites:
        for i in range(k):
            if x[i]+1 < shape[i]:
                y = list(x); y[i] += 1; y=tuple(y)
                edges.append((x,y))
                a,b=index[x],index[y]
                lap[a][a]+=alpha[x];lap[b][b]+=alpha[x]
                lap[a][b]-=alpha[x];lap[b][a]-=alpha[x]
    m = sum((1/power(a,D) for a in alpha.values()), F(0))/len(sites)
    lower = root_lower(m,D)
    # A PSD matrix at a rigorous LOWER coefficient certifies the larger claimed one.
    K = C*L*L*lower
    N=len(sites)
    Q=[[K*lap[i][j]-F(i==j)+F(1,N) for j in range(N)] for i in range(N)]
    require(psd(Q),'profile PSD failed at certified lower moment root')
    for field in (0,1):
        u={x:F((sum((i+1)*v*v for i,v in enumerate(x)) if field else x==sites[0]))
           for x in sites}
        check_potential(u,edges,k,R)
    return {'shape':shape,'D':D,'fixture':fixture,'matrix_size':N,
            'root_lower':str(lower),'C':str(C)}


def partition(n,k,D,fixture,scale):
    _,C,T=constants(k,D);r=D-k
    root=tuple((0,n) for _ in range(k));sites=points(root)
    alpha={x:F((1,4,n*n)[(sum((i+1)*v for i,v in enumerate(x))+fixture)%3])
           for x in sites}
    mass=lambda xs:sum((1/power(alpha[x],D) for x in xs),F(0))
    kappa=power(F(scale),D) # c=scale/C, hence (cC)^p is rational in fixtures.
    bad=[];terminal=[];leaves=[]
    def visit(box):
        lengths=[hi-lo for lo,hi in box];L=max(lengths);xs=points(box)
        require(max(lengths)-min(lengths)<=1,'profile node not near-balanced')
        m=mass(xs)/len(xs)
        if L==1 or kappa*L**D*m<=1:
            leaves.append(box);return False
        bad.append(box)
        child_axes=[]
        for lo,hi in box:
            mid=lo+(hi-lo)//2
            child_axes.append([(lo,hi)] if hi-lo==1 else [(lo,mid),(mid,hi)])
        child_bad=[]
        for child in product(*child_axes):
            ll=max(hi-lo for lo,hi in child)
            require(F(L,3)<=ll<=F(2*L,3),'child maximal side bounds')
            require(len(points(child))*3**k>=len(xs),'child volume ratio')
            child_bad.append(visit(child))
        if not any(child_bad):terminal.append(box)
        require(2**k*kappa*mass(xs)>F(1,L**r),'bad-node critical mass charge')
        return True
    visit(root)
    w=lambda nodes:sum((F(1,max(hi-lo for lo,hi in b)**r) for b in nodes),F(0))
    require(w(bad)<=w(terminal)/(1-F(2,3)**r),'bad-child injection bound')
    require(w(leaves)<=F(1,n**r)+(2**k*3**r-1)*w(bad),'leaf increment')
    require(w(terminal)<=2**k*kappa*mass(sites),'terminal disjoint charge')
    rectangles=[]
    for b in leaves:
        L=max(hi-lo for lo,hi in b)
        tiles=[(i,min(i+L,n)) for i in range(0,n,L)]
        rectangles.extend(b+z for z in product(tiles,repeat=r))
    check_coverage(rectangles,n,D)
    bound=2**r*(1+2**k*T*kappa*n**r*mass(sites))
    require(len(rectangles)<=bound,'critical target count')
    return {'n':n,'k':k,'D':D,'fixture':fixture,'scale':scale,
            'profile_leaves':len(leaves),'rectangles':len(rectangles),
            'bound_exact':str(bound),'c_exact':str(F(scale)/C)}


def main():
    require(platform.system()=='Linux','own Colab Linux only')
    start=time.perf_counter();local_cases=[];tree_cases=[]
    for k,D in ((2,3),(2,4),(3,4)):
        for shape in ((2,)*k,(2,)*(k-1)+(3,),(3,)*k):
            for fixture in range(3):local_cases.append(local(shape,D,fixture))
        for n in (1,2,3,5):
            for fixture in range(3):
                for scale in (1,2,3):tree_cases.append(partition(n,k,D,fixture,scale))
    rejected=False
    try:constants(3,3)
    except ValueError as e:rejected=str(e)=='invariant-coordinate scope requires 2<=k<D'
    require(rejected,'fully variable endpoint wrongly accepted')
    rejected=False
    try:check_potential({(0,0):F(0),(1,0):F(1)},[((0,0),(1,0))],2,F(0))
    except ValueError as e:rejected=str(e)=='finite potential bound'
    require(rejected,'zero-potential mutation not rejected')
    rejected=False
    try:check_coverage([((0,1),)*3,((0,1),)*3],1,3)
    except ValueError as e:rejected=str(e)=='coverage'
    require(rejected,'duplicate-cell mutation accepted')
    report={'status':'finite_exact_checks_passed','local_PSD_and_potential_cases':len(local_cases),
            'partition_cases':len(tree_cases),'local':local_cases,'partitions':tree_cases,
            'mutation_rejections':['k=D scope','zero potential constant','duplicate cell'],
            'arithmetic':'exact Fraction; rational certified lower root and exact PSD',
            'scope':'unit127 only; finite fixtures, not universal/Lean/independent proof',
            'elapsed_seconds':time.perf_counter()-start,'platform':platform.platform()}
    payload=json.dumps(report,sort_keys=True,separators=(',',':'))
    print('REPORT_JSON_BEGIN');print(payload);print('REPORT_JSON_END')
    print('REPORT_SHA256',hashlib.sha256(payload.encode()).hexdigest())


if __name__=='__main__':main()
