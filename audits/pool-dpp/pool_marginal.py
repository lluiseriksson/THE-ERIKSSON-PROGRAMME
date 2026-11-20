"""Finite-pool laws and Taylor coefficients. Standard-library Python, rational arithmetic."""
from decimal import Decimal, localcontext
from fractions import Fraction as F
from itertools import combinations, product
from math import comb, prod
from functools import cache
import json

def check(ok, label):
    if not ok:
        raise ValueError(label)

def add(a, b, c=1):
    out=a.copy()
    for mon,val in b.items():
        out[mon]=out.get(mon,0)+c*val
    return {k:v for k,v in out.items() if v}

def mul(a,b):
    out={}
    for i,x in a.items():
        for j,y in b.items():
            if len(i)+len(j)<=4:
                m=tuple(sorted(i+j));out[m]=out.get(m,0)+x*y
    return out

def moments(P,q):
    """Expand each rational conditional probability independently through degree four."""
    polys={};z={}
    for S,p in P.items():
        w={m:F(1) for k in range(min(4,len(S))+1) for m in combinations(S,k)}
        polys[S]=w;z=add(z,w,p)
    v=add(z,{():F(1)},-1)
    inverse={():F(1)};term=inverse
    for k in range(1,5):
        term=mul(term,v);inverse=add(inverse,term,(-1)**k)
    @cache
    def joint(m):
        return sum(q[j]*prod(F(int(j==i),1)/q[i]-1 for i in m) for j in range(len(q)))
    def pair(i,j):
        return joint(tuple(sorted((i,j))))
    ans={}
    for S,w in polys.items():
        first=second=F(0)
        for m,k in mul(w,inverse).items():
            if len(m)==2:first+=k*joint(m)
            if len(m)==3:second+=k*joint(m)
            if len(m)==4:
                a,b,c,d=m
                second+=k*(pair(a,b)*pair(c,d)+pair(a,c)*pair(b,d)+pair(a,d)*pair(b,c))
        ans[S]=(first,second)
    return ans

def inclusion(P,I):
    return sum(p for S,p in P.items() if set(I)<=set(S))

def compositions(n,k):
    if k==1:
        yield (n,)
    else:
        for i in range(n+1):
            for tail in compositions(n-i,k-1):
                yield (i,)+tail

def enumeration(P,q,n):
    sums=dict.fromkeys(P,F(0));valid=F(0);states=0
    for counts in compositions(n,len(q)):
        states+=1
        raw={S:p*prod(F(counts[i])/q[i] for i in S) for S,p in P.items()}
        z=sum(raw.values())
        if not z:continue
        remaining=n;pool=F(1)
        for count,qi in zip(counts,q):
            pool*=comb(remaining,count)*qi**count;remaining-=count
        valid+=pool
        for S,v in raw.items():sums[S]+=pool*v/z
    law={S:v/valid for S,v in sums.items()}
    check(sum(law.values())==1,'Marginal normalization')
    return law,states

def dec(v):
    return Decimal(v.numerator)/Decimal(v.denominator)

def audit(P,q,matched,sizes):
    k=len(next(iter(P)))
    p1=[inclusion(P,(i,)) for i in range(len(q))]
    tau={S:sum(p1[i]/q[i] for i in S) for S in P}
    tau2={S:sum(inclusion(P,(i,j))/(q[i]*q[j]) for i,j in combinations(S,2)) for S in P}
    a=moments(P,q)
    avg=sum(P[S]*tau[S] for S in P)
    av2=sum(P[S]*tau2[S] for S in P)
    check(all(z[0]==avg-tau[S] for S,z in a.items()),'First-order bias')
    if matched:
        check(all(p1[i]==k*q[i] for i in range(len(q))),'Proposal mismatch')
        check(all(z==(0,av2-tau2[S]) for S,z in a.items()),'Second-order bias')
    idx=int(matched)
    leading=sum(P[S]*a[S][idx]**2 for S in P)/2
    results=[]
    for n in sizes:
        law,states=enumeration(P,q,n)
        if not leading and matched and k==2:
            check(law==P,'Exact symmetry control')
        with localcontext() as ctx:
            ctx.prec=55
            kl=sum(dec(P[S])*(dec(P[S])/dec(law[S])).ln() for S in P)
            results.append(dict(N=n,count_vectors=states,scaled_KL=str(kl*n**(4 if matched else 2)),
                                max_bias=str(max(abs(dec(law[S]-P[S])) for S in P))))
    return dict(coefficients={str(S):list(map(str,v)) for S,v in a.items()},leading_KL=str(leading),enumeration=results)

def diag(weights,k):
    vals={s:F(prod(weights[i] for i in s)) for s in combinations(range(len(weights)),k)}
    return {s:v/sum(vals.values()) for s,v in vals.items()}

def matched_q(P,n):
    return tuple(inclusion(P,(i,))/len(next(iter(P))) for i in range(n))

if __name__=='__main__':
    pair=diag((6,3,2),2)
    sizes=(2,8,16,32,64)
    un=audit(pair,(F(1,3),)*3,False,sizes)
    ma=audit(pair,matched_q(pair,3),True,sizes)
    check((un['leading_KL'],ma['leading_KL'])==('5/72','4/25'),'Reported constants')
    # A regular simplex of three class directions gives equal angular determinants.
    q=(F(1,12),F(1,4),F(1,3),F(1,3))
    labels=(0,0,1,2)
    sym={s:3*q[s[0]]*q[s[1]] for s in combinations(range(4),2) if labels[s[0]]!=labels[s[1]]}
    ctrl=audit(sym,q,True,(2,3,6,9))
    triple=diag((1,2,3,4),3);third=audit(triple,matched_q(triple,4),True,(3,6,12))
    print(json.dumps(dict(uniform=un,matched=ma,symmetry_control=ctrl,three_item_sets=third),sort_keys=True,indent=2))

