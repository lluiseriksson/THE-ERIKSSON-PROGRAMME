# SPDX-License-Identifier: MIT
"""Finite exact D=3 fixtures only; the all-size source220 proof is separate."""
from fractions import Fraction as F
from itertools import product
import hashlib,json

def require(ok,message):
    if not ok:raise ValueError(message)

def edges(points):
    for x in sorted(points):
        for j in range(3):
            y=tuple(v+(i==j) for i,v in enumerate(x))
            if y in points:yield x,y,j

def variance(points,f):
    return sum(f[x]**2 for x in points)-F(sum(f[x] for x in points)**2,len(points))

def mean(points,f):return F(sum(f[x] for x in points),len(points))

def closed(s):
    L=s**3;Q=4*L+1;NX=Q**3;N=NX-(2*L)**3;w=(2*L)**2;A=s**4;H=Q*Q
    mu=F((N-w)*H+w*A,N);S=4+F(N-w,NX)
    require(1<=A<H<=2*mu and mu>=1 and F(w,N)<=F(1,14),'Original actual mean/envelope')
    require(S==F(w,L*L)+F(N-w,Q**3) and S<5,'Original inverse critical mass')
    require(mu**3*S*S<100*N*N,'Original normalized moment squared bound')
    T=F((L-1)*L*(2*L-1),3);sumh=L*(L-1);norm=T*T;mass=sumh*sumh
    V=norm-F(mass*mass,N);E=A*2*(2*L-2)*T
    require(V>=norm/2 and E>0,'Actual centered variance')
    require(F(E,norm)==F(12*A,L*(2*L-1)),'Actual plate energy formula')
    require(V>=F(s*s,24)*E and V<=7350*s*s*E,'Matching source order on witness')
    return L,Q,NX,N,w,A,H,mu,S,T,norm,mass,V,E

def main():
    geometries=fields=slab_checks=transport_checks=root_checks=0
    full_profile_checks=filled_checks=closed_profiles=negative=0;records=[];plate_data=None
    for L in [1,2,3,8]:
        Q=4*L+1;X=set(product(range(Q),repeat=3));hole=set(product(range(1,2*L+1),repeat=3));O=X-hole
        plate={x for x in O if x[0]==0 and all(1<=x[j]<=2*L for j in [1,2])}
        require(len(O)==Q**3-(2*L)**3 and len(plate)==(2*L)**2,'Actual geometry counts')
        slabs={(i,sign):{x for x in O if x[i]==0} if sign==-1 else {x for x in O if x[i]>2*L} for i in range(3) for sign in [-1,1]}
        require(set().union(*slabs.values())==O and len(slabs)==6,'Actual cover')
        for (i,sign),part in slabs.items():
            require(len(part)==(1 if sign==-1 else 2*L)*Q*Q,'Actual slab volume')
        root=(0,1);parent={key:(1,1) if key==(0,-1) else root for key in slabs if key!=root}
        require(all(p[1]==1 and key[0]!=p[0] for key,p in parent.items()),'Fat parents and different normals')
        eo=list(edges(O));es={key:list(edges(part)) for key,part in slabs.items()};ex=list(edges(X)) if L==8 else None
        geometries+=1
        for mode in range(5):
            def h(t):return min(t-1,2*L-t)
            if mode==0:f={x:1 for x in O}
            elif mode==1:f={x:x[0]+2*x[1] for x in O}
            elif mode==2:f={x:1 if sum(x)%2 else -1 for x in O}
            elif mode==3:f={x:h(x[1])*h(x[2]) if x in plate else 0 for x in O}
            else:f={x:int(x==(0,0,0)) for x in O}
            E0=sum((f[y]-f[x])**2 for x,y,j in eo);V=variance(O,f)
            energies={key:sum((f[y]-f[x])**2 for x,y,j in ee) for key,ee in es.items()}
            means={key:mean(part,f) for key,part in slabs.items()};Z=sum(energies.values())
            for key,part in slabs.items():
                require(variance(part,f)<=F(Q*Q,4)*energies[key],'Actual slab product estimate');slab_checks+=1
            for key,pkey in parent.items():
                intersection=slabs[key]&slabs[pkey];require(bool(intersection),'Actual nonempty intersection')
                mi=mean(intersection,f)
                for side,other in [(key,pkey),(pkey,key)]:
                    directional=sum((f[y]-f[x])**2 for x,y,j in es[side] if j==other[0])
                    require((means[side]-mi)**2<=F(Q*Q,len(slabs[side]))*directional,'Actual fiber mean transport');transport_checks+=1
            for key,part in slabs.items():
                cursor=key;depth=0
                while cursor!=root:
                    cursor=parent[cursor];require(len(part)<=len(slabs[cursor]),'Descendant volume bound');depth+=1
                require(depth<=2 and len(part)*(means[key]-means[root])**2<=8*Q*Q*Z,'Actual root mean estimate');root_checks+=1
            require(Z<=6*E0 and V<=6*(F(1,4)+48)*Q*Q*E0,'Actual global unweighted cover estimate')
            require(V<=7350*L*L*E0,'Loose integer upper constant')
            if L==8:
                data=closed(2);_,_,NX,N,w,A,H,mu,S,T,norm,mass,Vformula,Eformula=data
                a={x:A if x in plate else H for x in O};ax={x:A if x in plate else H for x in X}
                require(F(sum(a.values()),len(O))==mu,'Actual grid mean')
                actualS=sum((F(1,L*L) if value==A else F(1,Q**3) for value in a.values()),F(0))
                require(actualS==S,'Actual grid inverse moment')
                Ea=sum(a[x]*(f[y]-f[x])**2 for x,y,j in eo);fx={x:f[x] if x in O else 0 for x in X}
                EX=sum(ax[x]*(fx[y]-fx[x])**2 for x,y,j in ex);VX=variance(X,fx)
                require(V<=7350*4*Ea,'Actual weighted annular upper estimate')
                require(F(1,2880)*VX<=EX,'Actual filled-cube one-row bound')
                require(EX+F(sum(fx.values())**2,2880*len(X))>=F(sum(v*v for v in fx.values()),2880),'Filled normalized-mean identity and penalty')
                full_profile_checks+=1;filled_checks+=1
                if mode==3:
                    require(sum(v*v for v in f.values())==norm and sum(f.values())==mass and V==Vformula and Ea==Eformula,'Actual product-tent field and energy')
                    require(EX==Ea+A*norm,'Restored edge starts WEAK, not strong')
                    require(all(a[x]==A for x,y,j in eo if f[x]!=f[y]),'All actual nonzero annular starts are weak')
                    plate_data=(Ea,EX,norm,A,H)
            records.append([L,mode,str(V),E0,str(Z)])
            fields+=1
    for s in [2,3,4,8,16,32]:
        data=closed(s);records.append(['closed',s,str(data[-2]),str(data[-1])]);closed_profiles+=1
    require(plate_data is not None,'Missing actual field guard')
    Ea,EX,norm,A,H=plate_data
    try:require(EX==Ea+H*norm,'False strong restored-start formula')
    except ValueError:negative+=1
    else:raise ValueError('Wrong restored starting site accepted')
    try:require(Ea==EX,'Hole edges falsely included in annular domain')
    except ValueError:negative+=1
    else:raise ValueError('Wrong annular edge set accepted')
    L,Q,NX,N,w,A,H,mu,S,T,norm,mass,V,E=closed(4096)
    try:require(V**3<=1000**3*Q**6*(S/F(N))**2*E**3,'False uniform offcenter critical-moment bound at fixed test constant1000')
    except ValueError:negative+=1
    else:raise ValueError('False inherited offcenter bound accepted')
    require((geometries,fields,slab_checks,transport_checks,root_checks,full_profile_checks,filled_checks,closed_profiles,negative)==(4,20,120,200,120,5,5,6,3),'Exact diagnostic counters')
    print(json.dumps({'status':'FINITE_RATIONAL_DIAGNOSTICS_CHECKED','dimension':3,'geometries':geometries,'fields':fields,'slab_checks':slab_checks,'transport_checks':transport_checks,'root_checks':root_checks,'full_profile_checks':full_profile_checks,'filled_cube_checks':filled_checks,'closed_profile_checks':closed_profiles,'negative_controls_rejected':negative,'transcript_sha256':hashlib.sha256(json.dumps(records,separators=(',',':')).encode()).hexdigest(),'scope':'Unweighted small shapes and one full weighted grid plus closed-count/1D product formulas; no enormous-grid, all-size, formal, coexact or full-domain counterexample claim.'},sort_keys=True))

if __name__=='__main__':main()
