"""Exact finite detour dictionary182; scientific execution only in Linux Colab."""
import argparse
from collections import Counter, defaultdict
from fractions import Fraction as F
from itertools import combinations, product
import json
from pathlib import Path
import platform
from rectangular_gap180 import psd, qform, laplacian


def require(ok, message):
    if not ok:
        raise ValueError(message)


def rejected(name, fn):
    try:
        fn()
    except ValueError as error:
        return {'mutation':name,'rejected_by':str(error)}
    raise ValueError('Mutation survived: '+name)


def shift(x, i, amount, n):
    y=list(x);y[i]=(y[i]+amount)%n;return tuple(y)


def distance(x, y, n):
    return max(min((a-b)%n,(b-a)%n) for a,b in zip(x,y))


def canonical(a,b,n):
    changed=[i for i in range(len(a)) if a[i]!=b[i]]
    require(len(changed)==1,'Actual nearest-neighbour path step')
    i=changed[0]
    if shift(a,i,1,n)==b:
        return (a,i,1)
    require(shift(a,i,-1,n)==b,'Unit periodic path step')
    return (b,i,-1)


def detours(D,n,W,mode=None):
    if mode!='skip_separation':
        require(all(distance(x,y,n)>=3 for x,y in combinations(W,2)),'Weak separation at least3')
    edges=defaultdict(list);paths=[]
    for x in sorted(W):
        for i in range(D):
            j=i if mode=='identity_sigma' else (i+1)%D
            require(j!=i,'Transverse fixed-point-free sigma')
            p1=shift(x,j,-1,n);p2=shift(p1,i,1,n);end=shift(x,i,1,n)
            path=[x,p1,p2,end]
            if mode=='drop_edge':path.pop(1)
            require(len(path)==4 and path[0]==x and path[-1]==end,'Three-edge endpoint/telescoping dictionary')
            actual=[]
            for number,(a,b) in enumerate(zip(path,path[1:])):
                start,k,sign=canonical(a,b,n)
                if mode=='wrong_first_start' and number==0:start=x
                expected=((p1,j,-1),(p1,i,1),(p2,j,1))[number]
                require((start,k,sign)==expected,'Actual positive start/orientation dictionary')
                require(start not in W,'Every detour positive start is strong')
                edges[(start,k)].append((x,i,number))
                actual.append((start,k,sign))
            paths.append((x,i,path,actual))
    require(len(paths)==D*len(W),'All weak-start edges have detours')
    require(sum(map(len,edges.values()))==3*D*len(W),'Actual edge-use counter')
    for (y,k),uses in edges.items():
        prev=(k-1)%D
        candidates=[(shift(y,k,1,n),prev,0),
                    (shift(y,(k+1)%D,1,n),k,1),
                    (shift(shift(y,prev,-1,n),k,1,n),prev,2)]
        require(len({x for x,_,_ in candidates})==3,'Three distinct source preimages')
        require(all(distance(x,z,n)<=2 for (x,_,_),(z,_,_) in combinations(candidates,2)),'Preimage pair distances at most2')
        expected={v for v in candidates if v[0] in W}
        require(set(uses)==expected,'Actual complete path-preimage equality')
    congestion=max(map(len,edges.values()),default=0)
    require(congestion<=1,'Congestion at most1')
    require(len(edges)==3*D*len(W),'Disjoint canonical edge uses')
    return paths,edges,congestion


def energies(D,n,W,values):
    strong=weak=F(0)
    for x,v in values.items():
        for i in range(D):
            square=(values[shift(x,i,1,n)]-v)**2
            if x in W:weak+=square
            else:strong+=square
    return strong,weak


def finite_case(name,D,n,W,matrix=False):
    paths,edges,congestion=detours(D,n,W)
    vs=list(product(range(n),repeat=D))
    fields=[{x:F(1) for x in vs},
            {x:F(x[0]) for x in vs},
            {x:F((sum((i+1)*v for i,v in enumerate(x))+product_term(x))%13-6,3) for x in vs}]
    checks=[]
    for values in fields:
        strong,weak=energies(D,n,W,values)
        require(weak<=3*strong,'Actual weak<=3strong energy')
        for x,i,path,uses in paths:
            increments=[values[b]-values[a] for a,b in zip(path,path[1:])]
            require(sum(increments)==values[shift(x,i,1,n)]-values[x],'Actual field telescoping')
            require(sum(increments)**2<=3*sum(v*v for v in increments),'Actual three-step Cauchy-Schwarz')
        checks.append({'strong':str(strong),'weak':str(weak),'E0':str(strong+weak)})
    record={'name':name,'D':D,'n':n,'weak_sites':len(W),'paths':len(paths),'used_positive_edges':len(edges),'actual_congestion':congestion,'field_checks':checks}
    if matrix:
        one={x:F(1) for x in vs};strong_a={x:F(0) if x in W else F(1) for x in vs}
        L0=laplacian(vs,n,one);Ls=laplacian(vs,n,strong_a)
        compare=[[4*Ls[i][j]-L0[i][j] for j in range(len(vs))] for i in range(len(vs))]
        record['exact_PSD_4Lstrong_minus_L0']=psd(compare)
        for values in fields:
            u=[values[x] for x in vs];strong,weak=energies(D,n,W,values)
            require(qform(L0,u)==strong+weak and qform(Ls,u)==strong,'Independent exact matrix/direct energies')
    return record


def product_term(x):
    result=1
    for v in x:result*=v+1
    return result


def family(m,t):
    require(t%m==0 and m>=4 and t>=m,'Predeclared integer family')
    D=3;n=t*t;N=n**D;mu=F(t**4);b=F(t*t)
    W=set(product(range(0,n,m*t),repeat=D));k=len(W);s=F(k,N);H=(mu-s*b)/(1-s)
    paths,edges,congestion=detours(D,n,W)
    require(k==(t//m)**D and s==F(1,m**D*t**D),'Exact weak-grid volume')
    require(s*b+(1-s)*H==mu and 1<=b<=mu<=H<2*mu,'Exact original mean/coefficient bounds')
    require(mu/b==t*t and s*t**D==F(1,m**D),'Exact weak critical moment contribution')
    require(mu/H<1,'Strong critical moment contribution strictly less than1-s')
    require(4*H/n**2>=4,'Actual one-mean coercivity lower factor')
    require(mu==n*n,'Original target rank scale is1')
    require(all(distance(x,y,n)>=m*t for x,y in combinations(W,2)),'Weak-pair minimum periodic separation')
    require(m*m>12,'Cut-path necessary side bound excludes two weak sites')
    if m==7:require(m*m>40,'Full-period uniform necessary side bound')
    return {'name':'admissible_m'+str(m)+'_t'+str(t),'D':D,'n':n,'mu':str(mu),'b':str(b),'H':str(H),'weak_sites':k,
            'paths':len(paths),'actual_congestion':congestion,'used_edges':len(edges),'weak_critical_moment':str(F(1,m**D)),
            'critical_moment_strict_upper':str(1+F(1,m**D)),'strong_critical_moment_expression':'(1-'+str(s)+')*('+str(mu/H)+')^(3/2)',
            'minimum_certificate_leaf_lower_bound':k,'actual_global_mean_cells':1,'full_lattice_enumerated':False,
            'periodic_uniform_constant40_checked':m==7}


def divergent():
    D=3;n=6;mu=F(n*n);W=set(product(range(0,n,3),repeat=D));s=F(len(W),n**D);H=(mu-s)/(1-s)
    _,_,congestion=detours(D,n,W)
    require(s==F(1,3**D) and s+(1-s)*H==mu and 1<=mu<=H<2*mu,'Divergent-family original coefficient conditions')
    require(4*H/n**2>=4,'Divergent-family one-mean comparison')
    lower=s*n**D
    require(lower==8,'Actual weak contribution of mu^(3/2), since mu=n^2')
    vs=list(product(range(n),repeat=D));values={x:F((sum(x)+product_term(x))%7-3,2) for x in vs}
    strong,weak=energies(D,n,W,values);E=H*strong+weak
    avg=sum(values.values(),F(0))/len(vs);variance=sum((v-avg)**2 for v in values.values())
    require(strong+weak<=4*strong and E>=H*(strong+weak)/4,'Divergent-family actual comparison')
    require(E>=4*variance,'Divergent-family actual field one-mean inequality')
    return {'name':'divergent_moment_n6','n':n,'D':D,'mu':str(mu),'H':str(H),'weak_sites':len(W),'weak_critical_moment_lower':str(lower),
            'actual_congestion':congestion,'actual_global_mean_cells':1,'asymptotic_lower_expression':'3^(-D)*n^D','field_energy':str(E),'field_variance':str(variance)}


def ramps():
    records=[]
    for l in (2,3,4,8):
        v=[F(r)-F(l-1,2) for r in range(l)]
        norm=sum(x*x for x in v);path=sum((v[r+1]-v[r])**2 for r in range(l-1));cycle=path+(v[0]-v[-1])**2
        require(sum(v)==0 and norm==F(l*(l*l-1),12),'Exact mean-zero ramp norm')
        require(path==l-1 and path/norm==F(12,l*(l+1)),'Exact cut-path ramp energy quotient')
        require(cycle==l*(l-1) and cycle>path,'Actual full-cycle wrap edge retained')
        records.append({'l':l,'norm':str(norm),'path_energy':str(path),'cycle_energy':str(cycle),'path_Rayleigh_upper':str(path/norm)})
    return {'name':'path_cycle_ramp_dictionary','ramps':records,'periodic_analytic_bound':'4*pi^2/l^2<40/l^2; not numerically certified'}


def main():
    require(platform.system()=='Linux','Linux scientific execution plane required')
    cases=[finite_case('D2_n3_empty',2,3,set(),True),finite_case('D2_n3_single',2,3,{(0,0)},True),
           finite_case('D3_n4_origin',3,4,{(0,0,0)},True),finite_case('D3_n4_wrap_corner',3,4,{(3,3,3)},True),
           finite_case('D3_n6_grid',3,6,set(product((0,3),repeat=3))),finite_case('D4_n6_grid',4,6,set(product((0,3),repeat=4))),
           family(4,4),family(4,8),family(7,7),divergent(),ramps()]
    W={(0,0,0)};mutations=[]
    mutations.append(rejected('weak_label_on_reversed_first_edge',lambda:detours(3,4,W,'wrong_first_start')))
    mutations.append(rejected('identity_sigma',lambda:detours(3,4,W,'identity_sigma')))
    mutations.append(rejected('drop_path_edge',lambda:detours(3,4,W,'drop_edge')))
    congestion=detours(3,4,W)[2]
    mutations.append(rejected('false_zero_congestion',lambda:require(congestion==0,'Actual nonempty detour congestion is1')))
    mutations.append(rejected('adjacent_pair_without_separation',lambda:detours(3,6,{(0,0,0),(1,0,0)},'skip_separation')))
    l=4;v=[F(r)-F(l-1,2) for r in range(l)];path=sum((v[r+1]-v[r])**2 for r in range(l-1));cycle=path+(v[0]-v[-1])**2
    mutations.append(rejected('drop_full_cycle_wrap',lambda:require(cycle==path,'Full-period ramp wrap edge changes energy3 to12')))
    m=4;t=8;n=t*t;b=t*t;length=m*t+1
    require(length<=n,'Actual large weak-containing rectangle fits the original torus')
    mutations.append(rejected('accept_long_weak_rectangle',lambda:require(F(12*b,length*(length+1))>=1,'Actual ramp necessary bound rules out certificate on length33,min64')))
    solver_attacks=[rejected('negative_pivot',lambda:psd([[F(-1)]])),rejected('zero_pivot_nonzero_row',lambda:psd([[F(0),F(1)],[F(1),F(0)]]))]
    require(len(cases)==11 and len(mutations)==7 and len(solver_attacks)==2,'Explicit acceptance counters')
    payload={'unit':182,'arithmetic':'exact Fraction and integers; irrational strong moments retained symbolically with valid upper bounds',
             'case_count':11,'mutation_count':7,'solver_attack_count':2,'cases':cases,'mutations':mutations,'solver_attacks':solver_attacks,
             'Lean_verified':False,'independent_review':False,'all_size_theorem_computationally_certified':False,
             'scope':'Actual finite path/coefficient/boundary adapter checks only; all-size analytical claim remains note181'}
    ap=argparse.ArgumentParser();ap.add_argument('--output',required=True);args=ap.parse_args()
    Path(args.output).write_text(json.dumps(payload,sort_keys=True,indent=2)+'\n')
    print('FINITE_DETOUR_CHECKS_COMPLETE cases=11 rejected_mutations=7 solver_attacks=2')


if __name__=='__main__':
    main()