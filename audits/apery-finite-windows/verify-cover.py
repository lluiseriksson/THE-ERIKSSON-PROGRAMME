"""Verify the eight-cell certificate by interpolation of the original squared forms."""
from fractions import Fraction as F
from math import comb, factorial, lcm
from pathlib import Path
import gzip,json

def need(test, msg):
    if not test:raise ValueError(msg)

def polynomial_sign(w, a, b, slope):
    x=F(w['parameter']);q=x.denominator
    P=[int(x,16) for x in w['coefficients_hex']];s=w['shift']
    n=len(P)-1;d=2*n+s
    need(x.denominator==w['scaling_q'] and len(P)==w['degree']+1 and s in (0,1),'witness shape')
    for end in (a,b):need(1+slope*(end-x)>0,'scale sign')
    den=lcm(a.denominator,b.denominator)
    linear=slope.numerator*q
    const=slope.denominator*q-slope.numerator*x.numerator
    scale=slope.denominator*q
    squared=[sum(P[j]*P[k-j] for j in range(max(0,k-n),min(n,k)+1))*(q*scale)**k for k in range(2*n+1)]
    table=[[comb(k,j)**2*comb(k+j,j)**2 for j in range(k+1)] for k in range(d+1)]
    values=[]
    for z in range(d+1):
        X=int(a*den)+int(b*den)*z;Y=den*(1+z)
        xp=[1];yp=[1];lp=[1]
        for j in range(d):
            xp.append(xp[-1]*X);yp.append(yp[-1]*Y);lp.append(lp[-1]*(const*Y+linear*X))
        values.append(sum(v*lp[2*n-k]*sum(t*xp[j]*yp[k+s-j] for j,t in enumerate(table[k+s])) for k,v in enumerate(squared)))
    # D! times the monomial coefficients of the unique interpolating polynomial.
    coeff=[0]*(d+1);basis=[1];df=factorial(d)
    for j in range(d+1):
        mult=values[0]*(df//factorial(j))
        for i,u in enumerate(basis):coeff[i]+=mult*u
        values=[v-u for u,v in zip(values,values[1:])]
        basis=[(basis[i-1] if i else 0)-(j*basis[i] if i<len(basis) else 0) for i in range(len(basis)+1)]
    need(all(v<0 for v in coeff),'Interval contains a nonnegative coefficient')
    return d+1

def check(c,witnesses):
    l=F(2,3);r=F(49,50);edge=l;counts=[];used=[]
    need(c['complete'] is True and not c['uncovered'] and list(map(F,c['domain']))==[l,r],'domain')
    for path,lo,hi,key in c['rows']:
        a,b=F(lo),F(hi);need(a==edge and a<b<=r,'gap or overlap')
        index,t=key.split('@');w=witnesses[int(index)];slope=F(t)
        need(slope in (0,F(3,4)) and w['parameter']==c['centers'][int(index)] and w['degree']<=61,'witness identity')
        counts.append(polynomial_sign(w,a,b,slope));edge=b;used.append(w['degree'])
    need(edge==r and max(used)==61,'last endpoint or bound')
    return counts

def main():
    c=json.loads(Path('cover.json').read_bytes());ws=json.loads(gzip.decompress(Path('witnesses.json.gz').read_bytes()));counts=check(c,ws)
    import copy
    for mode in ['gap','pole','wrong polynomial']:
        bad=copy.deepcopy(c);wbad=copy.deepcopy(ws)
        if mode=='gap':bad['rows'][0][1]='1/2'
        elif mode=='pole':bad['rows'][0][3]='2@10000'
        else:wbad[2]['coefficients_hex']=['0x1'];wbad[2]['degree']=0
        try:check(bad,wbad)
        except ValueError:continue
        raise ValueError('Accepted '+mode)
    print(json.dumps(dict(cells=len(counts),checked_coefficients=sum(counts),counts=counts,uniform_upper_degree=61,rejected_mutations=3)))
if __name__=='__main__':main()