"""Exact finite adapter180; scientific execution restricted to Linux Colab."""
import argparse
from fractions import Fraction as F
from itertools import product
import json
from math import isqrt
from pathlib import Path
import platform


def require(ok, message):
    if not ok:
        raise ValueError(message)


def reject(name, fn):
    try:
        fn()
    except ValueError as error:
        return {'mutation': name, 'rejected_by': str(error)}
    raise ValueError('Mutation survived: '+name)


def vertices(rect):
    return list(product(*(range(lo, hi+1) for lo, hi in rect)))


def contains(rect, x):
    return all(lo <= v <= hi for (lo, hi), v in zip(rect, x))


def partition(n, D, S, A, c):
    L = min(n, max(1, isqrt((A/c).numerator//(A/c).denominator)))
    intervals = [(i, min(n-1, i+L-1)) for i in range(0, n, L)]
    cells = list(product(intervals, repeat=D))
    q0 = len(cells)
    cuts = 0
    for x in sorted(S):
        hits = [i for i, rect in enumerate(cells) if contains(rect, x)]
        require(len(hits) == 1, 'Unique current leaf')
        mid = list(cells.pop(hits[0]))
        for j in range(D):
            lo, hi = mid[j]
            if lo < x[j]:
                slab = list(mid)
                slab[j] = (lo, x[j]-1)
                cells.append(tuple(slab))
                mid[j] = (x[j], hi)
                cuts += 1
            lo, hi = mid[j]
            if x[j] < hi:
                slab = list(mid)
                slab[j] = (x[j]+1, hi)
                cells.append(tuple(slab))
                mid[j] = (lo, x[j])
                cuts += 1
        cells.append(tuple(mid))
    return cells, L, q0, cuts


def validate(n, D, S, cells, L, q0, cuts):
    seen = set()
    singleton = set()
    for rect in cells:
        require(len(rect) == D and all(0 <= lo <= hi < n for lo, hi in rect), 'Integer nonempty rectangle')
        require(all(hi-lo+1 <= L for lo, hi in rect), 'Side length bound')
        vs = vertices(rect)
        require(not seen.intersection(vs), 'Disjointness')
        seen.update(vs)
        if len(vs) == 1:
            singleton.add(vs[0])
        else:
            require(not S.intersection(vs), 'No weak vertex in nonsingleton')
    require(len(seen) == n**D, 'Exhaustive coverage')
    require(S <= singleton, 'Every weak vertex is singleton')
    require(len(cells) == q0+cuts, 'Actual cut/leaf count')
    require(cuts <= 2*D*len(S), 'Linear isolation cost')


def laplacian(vs, n, a, end=False):
    index = {x:i for i,x in enumerate(vs)}
    mat = [[F(0) for _ in vs] for _ in vs]
    for i, x in enumerate(vs):
        for j in range(len(x)):
            y = list(x); y[j] = (y[j]+1)%n; y = tuple(y)
            k = index[y]
            w = a[y] if end else a[x]
            mat[i][i] += w; mat[k][k] += w
            mat[i][k] -= w; mat[k][i] -= w
    return mat


def means_matrix(vs, cells, unnormalized=False):
    index = {x:i for i,x in enumerate(vs)}
    mat = [[F(0) for _ in vs] for _ in vs]
    for rect in cells:
        points = vertices(rect)
        w = F(1, len(points)**(2 if unnormalized else 1))
        for x in points:
            for y in points:
                mat[index[x]][index[y]] += w
    return mat


def qform(mat, u):
    return sum((u[i]*sum((v*u[j] for j,v in enumerate(row)), F(0)) for i,row in enumerate(mat)), F(0))


def psd(mat):
    n = len(mat)
    require(all(mat[i][j] == mat[j][i] for i in range(n) for j in range(n)), 'PSD symmetry')
    work = [row[:] for row in mat]
    positive = zero = 0
    for k in range(n):
        pivot = work[k][k]
        require(pivot >= 0, 'PSD negative pivot')
        if pivot == 0:
            require(all(work[k][j] == 0 for j in range(k+1,n)), 'PSD zero pivot with nonzero residual row')
            zero += 1
            continue
        positive += 1
        for i in range(k+1,n):
            if work[i][k] == 0:
                continue
            ratio = work[i][k]/pivot
            for j in range(i,n):
                work[i][j] -= ratio*work[k][j]
                work[j][i] = work[i][j]
    require(positive+zero == n, 'PSD pivot count')
    return {'dimension': n, 'positive_pivots': positive, 'zero_pivots': zero}


def direct_energy(vs, n, a, values):
    total = F(0)
    for x in vs:
        for j in range(len(x)):
            y=list(x); y[j]=(y[j]+1)%n; y=tuple(y)
            total += a[x]*(values[y]-values[x])**2
    return total


def basic_case(name, S, c=F(1), A=F(16), mean_target=None):
    n=4; D=3; vs=list(product(range(n), repeat=D))
    if mean_target is not None:
        s=F(len(S),len(vs))
        A=(mean_target-s)/(1-s)
    a={x:F(1) if x in S else A for x in vs}
    cells,L,q0,cuts=partition(n,D,S,A,c)
    validate(n,D,S,cells,L,q0,cuts)
    E=laplacian(vs,n,a)
    P=means_matrix(vs,cells)
    mat=[[E[i][j]+c*P[i][j]-(c if i==j else 0) for j in range(len(vs))] for i in range(len(vs))]
    pivots=psd(mat)
    field={x:F((7*x[0]+3*x[1]+x[2])%11-5,3) for x in vs}
    u=[field[x] for x in vs]
    energy=direct_energy(vs,n,a,field)
    require(qform(E,u)==energy, 'Direct/matrix start-weighted energy')
    norm=sum(v*v for v in u)
    mean_norm=F(0); residual=F(0)
    for rect in cells:
        points=vertices(rect); avg=sum((field[x] for x in points),F(0))/len(points)
        mean_norm += len(points)*avg**2
        residual += sum((field[x]-avg)**2 for x in points)
    require(norm==mean_norm+residual and qform(P,u)==mean_norm, 'Orthogonal mean/variance identity')
    require(c*residual <= energy/4, 'Actual residual energy bound')
    mu=sum(a.values(),F(0))/len(vs)
    # D3 critical moment is algebraic; report exact squared summands and a safe rational upper bound.
    # For positive r, r^(3/2)<=max(1,r^2). This avoids claiming a rational exact value of a radical.
    moment_upper=sum((max(F(1),(mu/a[x])**2) for x in vs),F(0))/len(vs)
    if mean_target is not None:
        require(mu==mean_target, 'Exact coefficient mean')
    record={'name':name,'n':n,'D':D,'weak_sites':len(S),'q0':q0,'q':len(cells),'cuts':cuts,'L':L,
            'coefficient_mean':str(mu),'critical_moment_rational_upper_bound':str(moment_upper),
            'critical_moment_exact_radicands':[{'mu_over_a_squared':str((mu/w)**2),'count':sum(v==w for v in a.values())} for w in sorted(set(a.values()))],
            'A':str(A),'c':str(c),'psd':pivots,'field_energy':str(energy),'field_norm':str(norm),
            'nonuniform_rectangle_sides':any(len({hi-lo+1 for lo,hi in rect})>1 for rect in cells)}
    return record, (vs,a,cells,L,q0,cuts,E,P)


def island(t):
    D=3; n=t*t; N=n**D; mu=F(t**4); b=F(t*t); s=F(1,t**D)
    H=(mu-s*b)/(1-s)
    S=set(product(range(t),repeat=D)); vs=list(product(range(n),repeat=D))
    cells=[tuple((0,t-1) for _ in range(D))]
    for i in range(D):
        cells.append(tuple((0,t-1) if j<i else (t,n-1) if j==i else (0,n-1) for j in range(D)))
    covered=set()
    for rect in cells:
        points=set(vertices(rect));require(not covered.intersection(points),'Island disjointness');covered.update(points)
        coeff=b if points<=S else H
        require(points<=S or not points.intersection(S),'Island coefficient homogeneous')
        require(F(max(hi-lo+1 for lo,hi in rect)**2,1)/(4*coeff)<=F(1,4),'Island local residual coefficient')
    require(len(covered)==N and len(cells)==D+1,'Island complete D+1 partition')
    require(s*b+(1-s)*H==mu and 1<=b<=H<=2*mu,'Island original coefficient hypotheses')
    require(s*s*(mu/b)**3==1,'Exact squared critical weak contribution equals1')
    require(mu/H<=1,'Strong critical contribution at most1-s, hence total<2')
    L=isqrt(b.numerator//b.denominator)
    q0=((n+L-1)//L)**D
    require(q0==t**D and len(S)==t**D,'Exhaustive threshold regimes: empty weak set or >=t^D singletons')
    a={x:b if x in S else H for x in vs}
    field={x:F((x[0]+2*x[1]-x[2])%7-3,2) for x in vs}
    norm=sum(v*v for v in field.values()); means=F(0); residual=F(0)
    for rect in cells:
        points=vertices(rect); avg=sum((field[x] for x in points),F(0))/len(points)
        means+=len(points)*avg**2;residual+=sum((field[x]-avg)**2 for x in points)
    E=direct_energy(vs,n,a,field)
    require(norm==means+residual and residual<=E/4 and norm<=E+means,'Island actual field/energy/mean inequality')
    return {'name':'intermediate_island_t'+str(t),'n':n,'D':D,'mu':str(mu),'b':str(b),'H':str(H),'weak_sites':len(S),'moment_strict_upper':'2',
            'actual_rectangles':len(cells),'optimal_threshold_singleton_cost':t**D,'field_energy':str(E),'field_norm':str(norm),'full_matrix_factorization':False}


def main():
    require(platform.system()=='Linux','Linux scientific execution plane required')
    X=set(product(range(4),repeat=3))
    declared=[('empty',set()),('origin',{(0,0,0)}),('last_corner',{(3,3,3)}),('wrap_pair',{(0,0,0),(3,0,0)}),
              ('chain',{(0,0,0),(1,0,0),(2,0,0)}),('diagonal',{(0,0,0),(2,2,2)}),
              ('plane',{x for x in X if x[0]==0}),('checkerboard',{x for x in X if sum(x)%2==0}),('all',X)]
    records=[]; saved={}
    for name,S in declared:
        rec,data=basic_case(name,S,c=F(16) if name=='all' else F(1),A=F(256) if name=='all' else F(16))
        records.append(rec);saved[name]=data
    rec,_=basic_case('exact_mean_gap',{(0,0,0),(3,3,3)},mean_target=F(16));records.append(rec)
    records += [island(2),island(3)]
    vs,a,cells,L,q0,cuts,E,P=saved['origin']
    mutations=[]
    mutations.append(reject('drop_side_slab',lambda:validate(4,3,{(0,0,0)},cells[1:],L,q0,cuts)))
    mutations.append(reject('false_cut_count',lambda:validate(4,3,{(0,0,0)},cells,L,q0,cuts-1)))
    vs0,a0,cells0,_,_,_,E0,_=saved['empty']
    bad=means_matrix(vs0,cells0,unnormalized=True)
    mutations.append(reject('unnormalized_mean',lambda:require(qform(E0,[F(1)]*64)+qform(bad,[F(1)]*64)>=64,'Constant-field target with wrong mean normalization')))
    vsA,aA,_,_,_,_,EA,_=saved['all']
    u=[F((1,0,-1,0)[x[0]]) for x in vsA]
    mutations.append(reject('skip_weak_isolation',lambda:require(qform(EA,u)>=16*sum(v*v for v in u),'Actual mean-zero Rayleigh2 versus target16')))
    field={x:F(1 if x[0]==0 else 3 if x[0]==1 else 0) for x in vs}
    endE=laplacian(vs,4,a,end=True)
    discrepancy=qform(endE,[field[x] for x in vs])-direct_energy(vs,4,a,field)
    require(discrepancy==45,'Declared orientation mutation witness')
    mutations.append(reject('end_weighted_edges',lambda:require(discrepancy==0,'Actual start/end energy discrepancy45')))
    # Acceptance solver itself must reject both a negative pivot and a zero pivot with a nonzero row.
    solver_attacks=[reject('solver_negative_pivot',lambda:psd([[F(-1)]])),reject('solver_zero_row',lambda:psd([[F(0),F(1)],[F(1),F(0)]]))]
    require(len(records)==12 and len(mutations)==5,'Explicit case and mutation counts')
    result={'unit':180,'arithmetic':'exact Fraction; radical moment inequality retained analytically with exact squared weak contribution',
            'case_count':12,'mutation_count':5,'solver_attack_count':2,'cases':records,'mutations':mutations,'solver_attacks':solver_attacks,
            'component_extension':'h identical orthogonal scalar blocks; all-cochain inequality implies divergence-free restriction',
            'Lean_verified':False,'independent_review':False,'all_size_theorem_computationally_certified':False}
    ap=argparse.ArgumentParser();ap.add_argument('--output',required=True);args=ap.parse_args()
    Path(args.output).write_text(json.dumps(result,sort_keys=True,indent=2)+'\n')
    print('FINITE_RECTANGLE_CHECKS_COMPLETE cases=12 rejected_mutations=5 solver_attacks=2')


if __name__=='__main__':
    main()