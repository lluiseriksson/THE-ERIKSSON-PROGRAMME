"""Exact coverage of fixed parameter intervals by transported finite moment witnesses."""
from math import comb, gcd, lcm
from functools import reduce
from fractions import Fraction as F
from pathlib import Path
import gzip,json
from importlib import import_module
core=import_module('apery-witness')

def chart(w,transport):
    P=[int(v,16) for v in w['coefficients_hex']]
    x=F(w['parameter']);p=x.numerator;q=x.denominator
    s=w['shift'];n=len(P)-1
    # Moving test polynomial P(q*t/L(x)), where L(x)=1+transport*(x-x0).
    # The polynomial below absorbs the positive factor (b*q*L)^(2n).
    a=transport.numerator;b=transport.denominator
    u=b*q-a*p;v=a*q;scale=b*q*q
    B=[];g=1
    for k in range(2*n+1):
        B=[(B[j]*u if j<len(B) else 0)+(B[j-1]*v if j else 0) for j in range(len(B)+1)]
        square=sum(P[i]*P[k-i] for i in range(max(0,k-n),min(k,n)+1))
        row=core.coefficients(k+s)
        if len(B)<len(row):B.extend([0]*(len(row)-len(B)))
        for j,val in enumerate(row):B[j]+=g*square*val
        g*=scale
    while len(B)>1 and B[-1]==0:B.pop()
    d=reduce(gcd,B,0)
    B=[v//d for v in B]
    if sum(v*x**j for j,v in enumerate(B))>=0:raise ValueError('Transport lost center witness')
    return B

def positive_denominators(w,a,b,t):
    x=F(w['parameter'])
    if min(1+t*(k-x) for k in (a,b))<=0:raise ValueError('Pole in test')

def standard(B,l,r):
    d=len(B)-1;v=core.bernstein_signs(B,l,r);cs=[comb(d,k) for k in range(d+1)]
    D=reduce(lcm,cs,1)
    return [a*(D//c) for a,c in zip(v,cs)]

def split(B):
    n=len(B)-1;L=[];R=[]
    for k in range(n+1):
        L.append(B[0]<<(n-k));R.append(B[-1]<<(n-k))
        B=[a+b for a,b in zip(B,B[1:])]
    return L,R[::-1]

def cover(l,r,matrices,depth,path,rows):
    accepted=next((key for key,B in matrices if max(B)<0),None)
    if accepted is not None:
        rows.append([path,str(l),str(r),accepted]);return
    survivors=[(k,v) for k,v in matrices if min(v)<0]
    if not survivors or depth==0:
        rows.append([path,str(l),str(r),None]);return
    halves=[(k,*split(v)) for k,v in survivors];mid=(l+r)/2
    cover(l,mid,[(k,v) for k,v,_ in halves],depth-1,path+'0',rows)
    cover(mid,r,[(k,v) for k,_,v in halves],depth-1,path+'1',rows)

def main():
    witnesses=json.loads(gzip.decompress(Path('witnesses.json.gz').read_bytes()))
    # Add one published control in the large gap between 1/2 and 9/10.
    p,q,s=3,4,1;hit=core.point(p,q,s,12)
    if hit['degree']!=12:raise ValueError('3/4 control')
    witnesses.append(core.validate_witness(hit['P'],p,q,s,hit['form']))
    l=F(2,3);r=F(49,50);rows=[];matrices=[]
    for idx,w in enumerate(witnesses):
        for trans in [F(0),F(3,4)]:
            positive_denominators(w,l,r,trans);poly=chart(w,trans)
            matrices.append((str(idx)+'@'+str(trans),standard(poly,l,r)))
    cover(l,r,matrices,10,'',rows)
    gaps=[]
    for _,a,b,key in rows:
        if key is None:
            if gaps and gaps[-1][1]==a:gaps[-1][1]=b
            else:gaps.append([a,b])
    print(json.dumps(dict(domain=[str(l),str(r)],centers=[w['parameter'] for w in witnesses],rows=rows,uncovered=gaps,complete=not gaps,max_depth=10)))
if __name__=='__main__':main()