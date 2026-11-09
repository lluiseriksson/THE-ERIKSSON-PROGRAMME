# SPDX-License-Identifier: MIT
"""Finite rational D=3 diagnostics, not an all-size or formal proof. Colab only."""
from collections import Counter
from fractions import Fraction as F
from itertools import product
import hashlib,json

def require(ok, message):
    if not ok:
        raise ValueError(message)

def shell(k,z):
    return {tuple(t+v for t,v in zip(x,z)) for x in product(range(-k,k+1),repeat=len(z)) if max(map(abs,x))==k}

def faces(k,z):
    result=[]
    for i in range(len(z)):
        for sign in [-1,1]:
            ranges=[range(-k+1,k) if j<i else [sign*k] if j==i else range(-k,k+1) for j in range(len(z))]
            result.append({tuple(t+v for t,v in zip(x,z)) for x in product(*ranges)})
    return result

def cover(A,parts):
    require(all(parts),'Empty face')
    count=Counter(x for part in parts for x in part)
    require(set(count)==A and all(v==1 for v in count.values()),'Cover is not exact and disjoint')
    for part in parts:
        require(len(part)==__import__('math').prod(len({x[i] for x in part}) for i in range(3)),'Not a rectangle')

def edges(part):
    for x in sorted(part):
        for j in range(len(x)):
            y=tuple(v+(i==j) for i,v in enumerate(x))
            if y in part:
                yield x,y

def variance(part,f):
    values=[f[x] for x in part]
    return sum(v*v for v in values)-F(sum(values)**2,len(values))

def fold(t,length):
    r=t%(2*length)
    return r if r<length else 2*length-1-r

def fold_check(part,k,normal,f):
    # Keep both tangential axes, including singleton sides at k=1.
    # Geometry and actual edge preimages only; no weights are reflected.
    axes=[sorted({x[i] for x in part}) for i in range(3)]
    tangent=[i for i in range(3) if i!=normal]
    cube=set(product(range(2*k+1),repeat=2));mapped={}
    for t in cube:
        x=[axes[i][0] for i in range(3)]
        for index,i in enumerate(tangent):
            x[i]=axes[i][fold(t[index],len(axes[i]))]
        mapped[t]=tuple(x)
    counts=Counter(mapped.values());require(set(counts)==part and max(counts.values())<=9,'Vertex fold multiplicity')
    original={tuple(sorted(e)) for e in edges(part)};preimages=Counter()
    for x,y in edges(cube):
        u,v=mapped[x],mapped[y]
        if u!=v:
            edge=tuple(sorted((u,v)));require(edge in original,'Fold introduced nonlocal edge');preimages[edge]+=1
    require(all(v<=9 for v in preimages.values()),'Edge fold multiplicity')
    field={x:f[mapped[x]] for x in cube}
    V=variance(part,f);Vcube=variance(cube,field)
    Fcube=sum(abs(field[x]-field[y]) for x,y in edges(cube));Foriginal=sum(abs(f[x]-f[y]) for x,y in edges(part))
    require(V<=Vcube and Fcube<=9*Foriginal and Vcube<=4*Fcube**2,'Actual folded counting inequality')

def main():
    geometries=profiles=fields=face_checks=moment_checks=fold_checks=scale_checks=0
    transcripts=[]
    for L,z in product(range(1,5),[(0,0,0),(7,-4,2)]):
        candidates={k:shell(k,z) for k in range(L,2*L)}
        omega=set().union(*candidates.values());geometries+=1
        require(len(omega)==(4*L-1)**3-(2*L-1)**3,'Annulus cardinality')
        for profile in range(4):
            def uvalue(x):
                rel=tuple(a-b for a,b in zip(x,z));r=max(map(abs,rel))
                if profile==0:return 1
                if profile==1:return 1+(sum(rel)%2)
                if profile==2:return 7 if r==L else 1
                return 5 if sum((j+1)*v for j,v in enumerate(rel))%13==0 else 1
            u={x:uvalue(x) for x in omega};a={x:F(1,u[x]**2) for x in omega}
            B=sum(v**3 for v in u.values());weights={k:sum(u[x]**3 for x in part) for k,part in candidates.items()}
            k=min(weights,key=lambda j:(weights[j],j));require(weights[k]*L<=B,'Selected critical mass')
            A=candidates[k];parts=faces(k,z);cover(A,parts);profiles+=1
            require(len(parts)==6,'Actual observation count')
            for part in parts:
                U=sum(u[x]**2 for x in part);W=sum(u[x]**3 for x in part)
                require(U**3<=len(part)*W**2,'Critical-to-face Holder')
                require(len(part)<=(4*L)**2 and U**3<=16*B**2,'Selected moment cancellation');moment_checks+=1
            for field in range(5):
                def value(x):
                    r=tuple(a-b for a,b in zip(x,z))
                    if field==0:return 1
                    if field==1:return r[1]
                    if field==2:return 1 if sum(r)%2 else -1
                    if field==3:return int(x==min(A))
                    return sum((j+1)*v*v for j,v in enumerate(r))%11-5
                f={x:value(x) for x in A};totalV=F(0);totalE=F(0)
                for number,part in enumerate(parts):
                    V=variance(part,f);ee=list(edges(part));G=sum(abs(f[x]-f[y]) for x,y in ee)
                    E=sum((a[x]*(f[x]-f[y])**2 for x,y in ee),F(0));U=sum(u[x]**2 for x in part)
                    require(V<=324*G**2,'Unweighted face estimate')
                    require(G**2<=2*U*E,'Original starting-site Holder')
                    require(V<=648*U*E,'Weighted face estimate')
                    fold_check(part,k,number//2,f);fold_checks+=1;face_checks+=1;totalV+=V;totalE+=E
                EA=sum((a[x]*(f[x]-f[y])**2 for x,y in edges(A)),F(0))
                require(totalE<=EA,'Disjoint energy selection')
                require(totalV**3<=648**3*16*B**2*totalE**3,'Selected all-face inequality')
                require(totalV**3<=2592**3*B**2*EA**3,'Stated selected-shell constant')
                qmass=sum(F(sum(f[x] for x in part)**2,len(part)) for part in parts)
                require(totalV+qmass==sum(v*v for v in f.values()),'Exact normalized observation identity')
                fields+=1
                transcripts.append([L,list(z),profile,k,field,str(totalV),str(totalE),str(EA),B])
            if profile==0:
                for j,Aj in candidates.items():
                    f={x:x[1]-z[1] for x in Aj};parts_j=faces(j,z)
                    V=sum((variance(part,f) for part in parts_j),F(0));EA=sum((f[x]-f[y])**2 for x,y in edges(Aj))
                    require(V>=F(L*L,18)*EA,'All-radius homogeneous lower bound');scale_checks+=1
    # Real attack classes: previously overlapping slab cover and missing
    # incoming starting sites; plus a coefficient-dependent selection trap.
    rejected=0
    A=shell(1,(0,0,0));overlap=[]
    for i in range(3):
        for sign in [-1,1]:overlap.append({x for x in A if x[i]==sign})
    try:cover(A,overlap)
    except ValueError:rejected+=1
    else:raise ValueError('Overlapping slab mutation accepted')
    L=2;weights={j:sum((7 if j==L else 1)**3 for x in shell(j,(0,0,0))) for j in range(L,2*L)};B=sum(weights.values())
    try:require(weights[L]*L<=B,'Fixed-radius selection trap')
    except ValueError:rejected+=1
    else:raise ValueError('Wrong radius mutation accepted')
    part=faces(1,(0,0,0))[1];x0=(1,0,0);eps=F(1,97)
    a={x:eps if x==x0 else F(1) for x in part};f={x:int(x==x0) for x in part}
    actual=sum((a[x]*(f[x]-f[y])**2 for x,y in edges(part)),F(0));false=4*eps
    try:require(actual==false,'Incoming starts omitted')
    except ValueError:rejected+=1
    else:raise ValueError('Missing incoming mutation accepted')
    require((geometries,profiles,fields,face_checks,moment_checks,fold_checks,scale_checks,rejected)==(8,32,160,960,192,960,20,3),'Diagnostic counters')
    print(json.dumps({'status':'FINITE_RATIONAL_DIAGNOSTICS_CHECKED','dimension':3,'geometries':geometries,'profiles':profiles,'fields':fields,'face_checks':face_checks,'moment_checks':moment_checks,'fold_checks':fold_checks,'scale_checks':scale_checks,'negative_controls_rejected':rejected,'transcript_sha256':hashlib.sha256(json.dumps(transcripts,separators=(',',':')).encode()).hexdigest(),'scope':'Finite fixtures only; no all-size, formal, global-partition or priority claim.'},sort_keys=True))

if __name__=='__main__':main()
