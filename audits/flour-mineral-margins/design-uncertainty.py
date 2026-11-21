"""Exact rational perturbation bounds for the 19 published mixture-design rows."""
from fractions import Fraction as F
from itertools import permutations
from math import isqrt
import hashlib,json,re,sys,zipfile
import fitz

def det(A):
    if len(A)==1:return A[0][0]
    return sum((-1)**j*A[0][j]*det([row[:j]+row[j+1:] for row in A[1:]]) for j in range(len(A)))
def dot(u,v):return sum(a*b for a,b in zip(u,v))
def norm_upper(v):
    squared=dot(v,v)*10**12
    return F(isqrt(squared.numerator//squared.denominator)+1,10**6)
def dataset(pdf):
    if hashlib.sha256(pdf).hexdigest()!='e556708e9405fee2e72d1df8f7aeeaaa54979f617f6362f14b1aa4719bf56fb5':raise ValueError('PDF mismatch')
    with fitz.open(stream=pdf,filetype='pdf') as doc:
        design=doc[3].get_text(sort=True)
        measurements='\n'.join(doc[i].get_text(sort=True) for i in [9,10])
    X={};Y={}
    for line in design.splitlines():
        m=re.search(r'\bF(\d+)\s+([\d.]+)\s+([\d.]+)\s+([\d.]+)\s*$',line)
        if m:X[int(m[1])]=list(map(F,m.groups()[1:]))
    for line in measurements.splitlines():
        m=re.match(r'\s*F(\d+)\s+(.*)',line)
        if m:
            raw=re.findall(r'(\d+\.\d+)\s*±',m[2])
            assert len(raw)==4
            Y[int(m[1])]=list(map(F,raw[:3]))
    assert sorted(X)==sorted(Y)==list(range(1,20))
    return [X[i] for i in sorted(X)],[Y[i] for i in sorted(Y)]
def bounds(X,Y):
    n=len(X);columns=list(zip(*X));G=[[dot(u,v) for v in columns] for u in columns]
    def valid(k):
        shifted=[[G[i][j]-(k*k if i==j else 0) for j in range(3)] for i in range(3)]
        return all(det([row[:s] for row in shifted[:s]])>0 for s in (1,2,3))
    k=1
    while valid(k+1):k+=1
    assert valid(k)
    # ||E||_2 <= ||E||_F <= sqrt(2n)*.005 < .031. Each row sums to zero.
    h=F(1,200);epsilon=F(31,1000);assert 2*n*h*h<epsilon**2
    smin=k-epsilon;ratios={};details={}
    cs=[F('24.50'),F('41.83'),F('33.65')]
    centers=[[v+(F('.02') if i==j else 0) for i,v in enumerate(cs)] for j in range(3)]
    for label,y,t in zip(['iron','calcium','zinc'],zip(*Y),map(F,['3','160','2.2'])):
        rhs=[dot(u,y) for u in columns]
        beta=[det([[rhs[i] if j==a else G[i][j] for j in range(3)] for i in range(3)])/det(G) for a in range(3)]
        residual=[yy-dot(xx,beta) for xx,yy in zip(X,y)]
        assert all(dot(residual,u)==0 for u in columns)
        # A' = X+E; solving perturbed normal equations at beta yields two terms.
        delta=norm_upper([h*(1+max(beta)-min(beta))]*n)/smin+epsilon*norm_upper(residual)/smin**2
        minimum_domain=10*sum(beta)+70*min(beta)-norm_upper([80,10,10])*delta
        details[label]=dict(delta=str(delta),minimum_domain=str(minimum_domain),coef=list(map(str,beta)))
        if minimum_domain>t:ratios[label]=None;continue
        maximum=max(beta)-min(beta)
        assert maximum>2*delta
        lo=min(dot(c,beta)-norm_upper(c)*delta for c in centers)-t
        hi=max(dot(c,beta)+norm_upper(c)*delta for c in centers)-t
        lb=lo/(maximum+2*delta);ub=hi/(maximum-2*delta)
        donor=beta.index(max(beta));receiver=beta.index(min(beta))
        assert all(beta[donor]-beta[i]>2*delta for i in range(3) if i!=donor)
        assert all(beta[i]-beta[receiver]>2*delta for i in range(3) if i!=receiver)
        assert lb>0 and all(c[donor]-ub>=10 and c[receiver]+ub<=80 for c in centers)
        ratios[label]=dict(lower=str(lb),upper=str(ub),lower_display=(lb*1000).__floor__()/1000,upper_display=(ub*1000).__ceil__()/1000,donor=donor,receiver=receiver)
    assert ratios['iron'] is None and F(ratios['calcium']['upper'])<F(ratios['zinc']['lower'])
    return dict(row_count=n,singular_value_lower=k,details=details,distance_bounds=ratios,scope='Component coordinates at most .005 g in each closed 100 g row. Response means at most .005 on the reported analytical scale. Selected recipe assigned a nonnegative .02 g completion. OLS fitted anew for each admissible data set.')
if __name__=='__main__':
    with open(sys.argv[1] if len(sys.argv)>1 else 'source.pdf','rb') as f:print(json.dumps(bounds(*dataset(f.read()))))