#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Lluis Eriksson
"""Selected exact-rational diagnostics, not an all-size or formal proof.

Run only in the assigned Colab Linux runtime, normal and -O. No acceptance
decision depends on assert. All edges use the original positive-start weight.
"""
from fractions import Fraction as F
from itertools import product
import hashlib,json

COUNTS={'geometries':0,'BV_extensions':0,'partitions':0,'region_fields':0,
        'global_fields':0,'negative_controls_rejected':0,'cross_piece_edges':0}
TRANSCRIPT=[]
def require(v,m):
    if not v:raise ValueError(m)
def points(q):return set(product(*(range(lo,hi) for lo,hi in q)))
def children(q):
    spans=[]
    for lo,hi in q:
        m=hi-lo
        spans.append([(lo,hi)] if m==1 else [(lo,lo+m//2),(lo+m//2,hi)])
    return [tuple(x) for x in product(*spans)]
def edges(vs):
    for x in sorted(vs):
        for i in range(len(x)):
            y=x[:i]+(x[i]+1,)+x[i+1:]
            if y in vs:yield x,y
def tv(vs,f):return sum(abs(f[y]-f[x]) for x,y in edges(vs))
def energy(vs,f,a):return sum(a[x]*(f[y]-f[x])**2 for x,y in edges(vs))
def mean(vs,f):return sum(f[x] for x in vs)/F(len(vs))
def variance(vs,f):
    m=mean(vs,f);return sum((f[x]-m)**2 for x in vs)
def mass(vs,w):return sum(w[x] for x in vs)
def rectpieces(q,i):
    if i is None:return [q]
    ans=[]
    for k in range(len(q)):
        for span in [(q[k][0],i[k][0]),(i[k][1],q[k][1])]:
            if span[0]<span[1]:ans.append(tuple(list(i[:k])+[span]+list(q[k+1:])))
    return ans
def actual_partition(q,w,t):
    out=[]
    def visit(cur):
        vv=points(cur)
        if mass(vv,w)<=t or len(vv)==1:
            out.append((cur,None));return
        cs=children(cur);hs=[z for z in cs if mass(points(z),w)>t]
        if len(hs)!=1:
            for z in cs:
                if z in hs:visit(z)
                else:out.append((z,None))
            return
        outer=cur;accum=F(0)
        while len(points(cur))>1:
            cs=children(cur);hs=[z for z in cs if mass(points(z),w)>t]
            if len(hs)!=1:break
            nex=hs[0];accum+=mass(points(cur)-points(nex),w)
            if accum>=t:
                out.append((outer,nex));outer=nex;accum=F(0)
            cur=nex
        if outer!=cur:out.append((outer,cur))
        visit(cur)
    visit(q);return out
def check_cover(groups,whole):
    seen=set()
    for g in groups:
        require(bool(g) and not seen.intersection(g),'Empty/overlapping group')
        seen.update(g)
    require(seen==whole,'Coverage differs')
def fields(vs):
    first=min(vs)
    return [{x:F(1) for x in vs},
            {x:F(sum((j+1)*z for j,z in enumerate(x))) for x in vs},
            {x:F((sum((j+1)*(z+1)**2 for j,z in enumerate(x))%11)-5) for x in vs},
            {x:F(int(x==first)) for x in vs}]
def bv_check(q,i,f):
    D=len(q);hole=points(i);om=points(q)-hole
    if min(hi-lo for lo,hi in q)==1:return
    # Independently use the actual minimal positive side/gap in this selected
    # geometry. For midpoint ancestors this is a valid h lower bound.
    positive=[i[j][0]-q[j][0] for j in range(D) if i[j][0]>q[j][0]]
    positive += [q[j][1]-i[j][1] for j in range(D) if i[j][1]<q[j][1]]
    h=min([hi-lo for lo,hi in i]+positive)
    require(all(h<=hi-lo<=2*h for lo,hi in i),'Hole balance')
    B=tuple((lo-h if lo>q[j][0] else lo,hi+h if hi<q[j][1] else hi)
            for j,(lo,hi) in enumerate(i))
    slabs=[]
    for j,(lo,hi) in enumerate(i):
        for side,span in [('low',(lo-h,lo)),('high',(hi,hi+h))]:
            if (side=='low' and lo==q[j][0]) or (side=='high' and hi==q[j][1]):continue
            s=list(B);s[j]=span;slabs.append((j,points(tuple(s))))
    require(D<=len(slabs)<=2*D,'Slab count')
    aa=points(B)-hole;require(set.union(*(v for _,v in slabs))==aa,'Actual slab cover')
    require(all(v<=om for _,v in slabs),'Slab outside actual ring')
    for axis,sv in slabs:
        for axis2,sv2 in slabs:
            if axis!=axis2:
                require(len(sv)<=4*len(sv&sv2) and len(sv)<=2*len(sv2),'Overlap/volume constants')
    c0=mean(slabs[0][1],f);ff=dict(f);ff.update({x:c0 for x in hole})
    J=2*D;PD=2*J*(1+12*J);Cext=1+J*(PD+1)
    require(sum(abs(f[x]-c0) for x in aa)<=PD*h*tv(aa,f),'Actual collar L1 bound')
    require(tv(points(q),ff)<=Cext*tv(om,f),'Constant-fill BV extension')
    COUNTS['BV_extensions']+=1
def main():
    for D,ns in [(3,[1,2,3,5,7,9]),(4,[1,2,3,5])]:
        b=2**D;J=2*D;Cext=1+J*(2*J*(1+12*J)+1)
        G=2**(2*D+10)*D*D*Cext*Cext
        for n in ns:
            q=tuple((0,n) for _ in range(D));whole=points(q);fs=fields(whole)
            # Actual nested ancestor/descendant samples: corner, central,
            # odd-sized and singleton directions all occur.
            stack=[q];nodes=[]
            while stack:
                z=stack.pop();nodes.append(z)
                if len(points(z))>1:stack.extend(children(z))
            candidates=[z for z in nodes if z!=q]
            chosen=candidates if len(candidates)<=32 else [candidates[k*(len(candidates)-1)//31] for k in range(32)]
            for i in chosen:
                om=whole-points(i);pieces=[points(z) for z in rectpieces(q,i)]
                check_cover(pieces,om);require(len(pieces)<=2*D,'Rectangular piece count')
                COUNTS['geometries']+=1
                for f in fs[1:]:bv_check(q,i,f)
            profiles=[]
            for kind in range(5):
                scales={x:(1 if kind==0 else
                    (1 if x==min(whole) else 8) if kind==1 else
                    (1 if sum(z*z for z in x)%3==0 else 5) if kind==2 else
                    (1+sum((j+1)*z for j,z in enumerate(x))%7) if kind==3 else
                    (1 if sum(z!=0 for z in x)<=1 else 11)) for x in whole}
                a={x:F(scales[x]**2) for x in whole};w={x:F(1,scales[x]**D) for x in whole}
                profiles.append((a,w))
            for a,w in profiles:
                for r in [F(1,2),F(1),F(2),F(5)]:
                    t=r**D/b;c=1/(G*r*r);groups=actual_partition(q,w,t)
                    regions=[points(z)-(points(i) if i else set()) for z,i in groups]
                    check_cover(regions,whole)
                    require(len(groups)<=1+(2*b+3)*mass(whole,w)/t,'Compressed region count')
                    rects=[]
                    for (z,i),reg in zip(groups,regions):
                        localpieces=[points(v) for v in rectpieces(z,i)];check_cover(localpieces,reg)
                        rects.extend(localpieces)
                        if len(reg)>1:require(mass(reg,w)<=b*t,'Nonsingleton mass cap')
                        owner={x:k for k,p in enumerate(localpieces) for x in p}
                        cross=[(x,y) for x,y in edges(reg) if owner[x]!=owner[y]]
                        COUNTS['cross_piece_edges']+=len(cross)
                        for f in fs:
                            require(energy(reg,f,a)>=c*variance(reg,f),'Actual regional gap on field')
                            COUNTS['region_fields']+=1
                    check_cover(rects,whole)
                    require(len(rects)<=2*D*(1+(2*b+3)*mass(whole,w)/t),'Actual rectangle/rank count')
                    for f in fs:
                        penalty=sum(sum(f[x] for x in v)**2/F(len(v)) for v in rects)
                        require(energy(whole,f,a)+c*penalty>=c*sum(f[x]**2 for x in whole),'Actual global energy/means')
                        COUNTS['global_fields']+=1
                    COUNTS['partitions']+=1
                    TRANSCRIPT.append([D,n,len(groups),len(rects),str(t),str(mass(whole,w))])
    # Real field mutations of coverage/geometry/retained-edge accounting.
    whole=set(product(range(3),repeat=3));hole={(1,1,1)};om=whole-hole
    q=((0,3),)*3;i=((1,2),)*3;pieces=[points(z) for z in rectpieces(q,i)]
    mutations=[pieces[:-1],pieces+[pieces[0]]]
    for groups in mutations:
        try:check_cover(groups,om)
        except ValueError:COUNTS['negative_controls_rejected']+=1
        else:raise ValueError('Mutated coverage falsely accepted')
    owner={x:k for k,p in enumerate(pieces) for x in p}
    f={x:F(owner[x]) for x in om};a={x:F(1) for x in om}
    true=energy(om,f,a);discarded=sum(energy(p,f,a) for p in pieces)
    require(true>discarded and discarded==0,'Interface-discard negative control must be nontrivial')
    try:require(true==discarded,'Mutated ring energy discarded actual cross-piece edges')
    except ValueError:COUNTS['negative_controls_rejected']+=1
    else:raise ValueError('Wrong energy dictionary falsely accepted')
    require(COUNTS['partitions']==200 and COUNTS['global_fields']==800 and COUNTS['negative_controls_rejected']==3,'Exact acceptance counters')
    print(json.dumps({'status':'FINITE_RATIONAL_DIAGNOSTICS_CHECKED',**COUNTS,
        'transcript_sha256':hashlib.sha256(json.dumps(TRANSCRIPT,separators=(',',':')).encode()).hexdigest(),
        'scope':'Selected D3/D4 odd and singleton geometries; exact rational BV/cover/count/actual-gradient fields. Not all-size, formal, spectral or independent reproduction proof.'},sort_keys=True))
if __name__=='__main__':main()
