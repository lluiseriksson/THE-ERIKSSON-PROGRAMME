# SPDX-License-Identifier: MIT
"""Exact finite D=3 fixtures for source219; not an all-size/Lean certificate."""
from collections import Counter,defaultdict
from fractions import Fraction as F
from itertools import permutations,product
import hashlib,json

def require(ok,message):
    if not ok:raise ValueError(message)

def variance(part,f):
    return sum(f[x]**2 for x in part)-F(sum(f[x] for x in part)**2,len(part))

def edges(X):
    for x in sorted(X):
        for j in range(3):
            y=tuple(v+(i==j) for i,v in enumerate(x))
            if y in X:yield x,y

def classify(x,pi,s,refine):
    nonzero=[i for i in pi if x[i]]
    if not nonzero:return ('origin',)
    i=nonzero[0];sign=1 if x[i]>0 else -1
    if not refine:return ('base',i,sign)
    if len(nonzero)==1:return ('weak',i,sign,(abs(x[i])-1)//s)
    j=nonzero[1]
    return ('strong',i,sign,j,1 if x[j]>0 else -1)

def partition(X,pi,s,refine):
    result=defaultdict(set)
    for x in X:result[classify(x,pi,s,refine)].add(x)
    return dict(result)

def cover(X,parts):
    counts=Counter(x for part in parts for x in part)
    require(set(counts)==X and all(v==1 for v in counts.values()),'Not a disjoint full cover')
    for part in parts:
        require(bool(part),'Empty rectangle')
        axes=[sorted({x[i] for x in part}) for i in range(3)]
        require(all(v==list(range(v[0],v[-1]+1)) for v in axes),'Noncontiguous rectangle side')
        sizes=[len(v) for v in axes]
        require(len(part)==sizes[0]*sizes[1]*sizes[2],'Not a Cartesian rectangle')

def parameters(s):
    R=s**3;n=2*R+1;N=n**3;A=s*s;H=n*n;w=6*R
    mu=F((N-w)*H+w*A,N);S=F(N-w,N)+6
    require(F(w,N)<=F(1,3) and 1<=A<H<=2*mu and mu>=1,'Actual envelope or mean')
    require(S==F(N-w,H**1)*F(1,n)+F(w,s**3),'Actual inverse mass identity')
    # H^(3/2)=n^3=N and A^(3/2)=s^3=R; no float roots.
    require(S==F(N-w,N)+F(w,R) and S<7,'Critical mass')
    require(mu**3*S**2<49*N*N,'Original normalized moment squared bound')
    require(n*n<=2*(1+mu),'Original target-order factor squared bound')
    return R,n,N,A,H,w,mu,S

def tent(ell):
    return [t if t<=ell else 2*ell-t if t<=3*ell else t-4*ell for t in range(4*ell+1)]

def main():
    base_cases=refined_cases=full_fields=refined_cell_checks=linear_formula_checks=0
    large_profile_checks=lowspace_checks=negative=0;records=[];c=F(1,4032)
    for s in [1,2]:
        R,n,N,A,H,w,mu,S=parameters(s);X=set(product(range(-R,R+1),repeat=3))
        a={x:A if sum(v!=0 for v in x)==1 else H for x in X};ee=list(edges(X))
        require(len(X)==N and sum(v==A for v in a.values())==w,'Actual coefficient sites')
        require(F(sum(a.values()),N)==mu,'Actual arithmetic mean')
        for pi in permutations(range(3)):
            base=partition(X,pi,s,False);refined=partition(X,pi,s,True)
            cover(X,base.values());cover(X,refined.values())
            require(len(base)==7 and len(refined)==13+6*s*s,'Actual partition row counts')
            base_cases+=1;refined_cases+=1
            for key,part in refined.items():
                if key[0]=='weak':require(len(part)==s and all(a[x]==A for x in part),'Actual weak segment')
                if key[0]=='strong':require(all(a[x]==H for x in part),'Strong complement excludes all weak axes')
            last=pi[-1];line={x for x in X if x[last]>0 and all(x[j]==0 for j in range(3) if j!=last)}
            require(len(line)==R and base[('base',last,1)]==line,'Final actual weak half-axis')
            for mode in range(5):
                if mode==0:f={x:1 for x in X}
                elif mode==1:f={x:x[last] for x in X}
                elif mode==2:f={x:1 if sum(x)%2 else -1 for x in X}
                elif mode==3:f={x:int(x==(0,0,0)) for x in X}
                else:f={x:2*x[last]-(R+1) if x in line else 0 for x in X}
                E=sum(a[x]*(f[y]-f[x])**2 for x,y in ee)
                V=variance(X,f);require(c*V<=E,'Actual one-rectangle inequality fixture')
                Eb=sum(a[x]*(f[y]-f[x])**2 for x,y in ee if classify(x,pi,s,False)==classify(y,pi,s,False))
                Er=sum(a[x]*(f[y]-f[x])**2 for x,y in ee if classify(x,pi,s,True)==classify(y,pi,s,True))
                require(Er<=Eb<=E,'Retained original internal energies')
                sumV=F(0);rowmass=F(0)
                for key,part in refined.items():
                    ep=sum(a[x]*(f[y]-f[x])**2 for x,y in edges(part));vv=variance(part,f)
                    require(4*vv<=ep,'Derived individual refined-cell gap');refined_cell_checks+=1
                    sumV+=vv;rowmass+=F(sum(f[x] for x in part)**2,len(part))
                norm=sum(v*v for v in f.values())
                require(sumV+rowmass==norm and Er+c*rowmass>=c*norm,'Actual fixed-penalty refined certificate')
                if mode==4 and R>=2:
                    normline=F(R*(R*R-1),3)
                    require(all(sum(f[x] for x in part)==0 for part in base.values()),'Base rows must vanish')
                    require(norm==normline and Eb==4*A*(R-1),'Exact linear internal formula')
                    expected=Eb+2*(H+A)*norm+H*(1-R)**2
                    require(E==expected and E>=2*H*norm,'Full transverse incoming starts and endpoint energy');linear_formula_checks+=1
                records.append([s,list(pi),mode,str(V),E,Eb,Er])
                full_fields+=1
    for s in [1,2,4,8,16,32,40,48,64,80]:
        R,n,N,A,H,w,mu,S=parameters(s);large_profile_checks+=1
        if R>=2:
            ratio=F(12*A,R*(R+1));require(ratio==F(4*A*(R-1),R*(R*R-1)//3),'Exact quotient')
        records.append(['profile',s,str(mu),str(S)])
    for s in [40,48,64,80]:
        R,n,N,A,H,w,mu,S=parameters(s);ell=384*s;m=(R-1)//(4*ell);g=tent(ell)
        norm=sum(v*v for v in g);gradient=sum((y-x)**2 for x,y in zip(g,g[1:]))
        require(g[0]==g[-1]==0 and sum(g)==0 and all(g[-1-t]==-g[t] for t in range(len(g))),'Exact zero-mean tent')
        require(norm==F(2*ell*(2*ell*ell+1),3) and gradient==4*ell,'Exact tent norm/energy formulas')
        rho=F(A*gradient,norm);require(rho==F(6*A,2*ell*ell+1) and rho<=c/4 and m>=1,'Lowspace quotient and dimension')
        joined=g[:-1]+[-2*v for v in g]
        require(sum(joined)==0 and sum(v*v for v in joined)==5*norm and sum((y-x)**2 for x,y in zip(joined,joined[1:]))==5*gradient,'Adjacent zero-endpoint tents have no cross energy')
        require(1+m*4*ell<=R and 2*m<=13+6*s*s,'Placement and matching upper row count')
        records.append(['lowspace',s,m,str(rho),norm,gradient]);lowspace_checks+=1
    # Actual failure classes, rejected by the same explicit predicates.
    X=set(product(range(-1,2),repeat=3));overlap=[{x for x in X if x[i]*sign>0} for i in range(3) for sign in [-1,1]]+[{(0,0,0)}]
    try:cover(X,overlap)
    except ValueError:negative+=1
    else:raise ValueError('Overlapping-cell mutation accepted')
    R,n,N,A,H,w,mu,S=parameters(2);norm=F(R*(R*R-1),3);actual=4*A*(R-1)+2*(H+A)*norm+H*(1-R)**2
    false=4*A*(R-1)+4*A*norm+A*(1-R)**2
    try:require(actual==false,'Incoming strong starts incorrectly weakened')
    except ValueError:negative+=1
    else:raise ValueError('Missing incoming-start mutation accepted')
    R,n,N,A,H,w,mu,S=parameters(32)
    try:require(F(12*A,R*(R+1))>=c,'False canonical internal-gap inheritance')
    except ValueError:negative+=1
    else:raise ValueError('False uniform internal gap accepted')
    require((base_cases,refined_cases,full_fields,refined_cell_checks,linear_formula_checks,large_profile_checks,lowspace_checks,negative)==(12,12,60,1680,6,10,4,3),'Actual finite counters')
    print(json.dumps({'status':'FINITE_RATIONAL_DIAGNOSTICS_CHECKED','dimension':3,'base_partition_cases':base_cases,'refined_partition_cases':refined_cases,'full_grid_fields':full_fields,'refined_cell_checks':refined_cell_checks,'linear_energy_checks':linear_formula_checks,'profile_checks':large_profile_checks,'lowspace_checks':lowspace_checks,'negative_controls_rejected':negative,'transcript_sha256':hashlib.sha256(json.dumps(records,separators=(',',':')).encode()).hexdigest(),'scope':'Small full-grid fields plus exact 1D/closed-count fixtures; not an all-size, formal, coexact or unrestricted-partition falsifier.'},sort_keys=True))

if __name__=='__main__':main()
