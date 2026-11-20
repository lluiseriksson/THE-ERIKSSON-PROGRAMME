"""Identify integer confusion matrices from the two rounded Table 4 reports."""
from collections import defaultdict
from fractions import Fraction as F
from itertools import combinations, product
from math import comb
from pathlib import Path
import numpy as np
import json, hashlib
from zipfile import ZipFile, ZIP_DEFLATED

N=122

def matrices(hits,f1,mcc):
    num,scale=int(f1.replace('.','')),10**len(f1.split('.')[1])
    mid=F(mcc)
    half=F(1,2*10**len(mcc.split('.')[1]))
    p,q,r=np.array([(i,j,hits-i-j) for i in range(hits+1) for j in range(hits-i+1)],dtype=np.int64).T
    errs=N-hits
    result=[]
    processed=0
    for cut in combinations(range(errs+5),5):
        edges=(-1,)+cut+(errs+5,)
        a,b,c,d,e,f=(v-u-1 for u,v in zip(edges,edges[1:]))
        processed+=1
        rows=(p+a+b,q+c+d,r+e+f)
        cols=(p+c+e,q+a+f,r+b+d)
        u,v,w=(x+y for x,y in zip(rows,cols))
        # The largest denominator is N*(2*N)^3; both integer cross-products
        # with a nine-decimal rounding endpoint fit in signed 64-bit integers.
        assert 2*scale*N*(2*N)**3 < 2**63-1
        numerator=2*(rows[0]*p*v*w+rows[1]*q*u*w+rows[2]*r*u*v)
        denom=N*u*v*w
        mask=(rows[0]>0)&(rows[0]<=rows[1])&(rows[1]<=rows[2])&(abs(2*scale*numerator-2*num*denom)<=denom)
        for i in np.flatnonzero(mask):
            R=[int(x[i]) for x in rows]; C=[int(x[i]) for x in cols]
            t=N*hits-sum(x*y for x,y in zip(R,C))
            z=(N*N-sum(x*x for x in R))*(N*N-sum(y*y for y in C))
            if t<=0 or z<=0 or not (mid-half)**2 <= F(t*t,z) <= (mid+half)**2:
                continue
            D=[int(x[i]) for x in (p,q,r)]
            exact=sum(F(2*h*x,x+y) for h,x,y in zip(D,R,C))/N
            assert abs(exact-F(f1))<=F(1,2*scale)
            result.append(dict(rows=R,cols=C,diagonal=D,table=[[D[0],a,b],[c,D[1],d],[e,f,D[2]]]))
    assert processed==comb(errs+5,5)
    return result

def main():
    x=matrices(112,'0.91079235','0.842682')
    y=matrices(111,'0.906464389','0.827407')
    pairs=[]
    for i,a in enumerate(x):
        for j,b in enumerate(y):
            if a['rows']!=b['rows']:continue
            deltas=[str(F(h-k,n)) for h,k,n in zip(a['diagonal'],b['diagonal'],a['rows']) if n==a['rows'][0]]
            pairs.append(dict(first=i,second=j,minority_deltas=deltas))
    data=dict(assumptions='Three nonempty actual classes, sorted actual supports, shared unweighted 122 cases. Rows are truth, columns prediction. Rounding intervals conservatively include both endpoints.',smote=x,borderline=y,pairs=pairs)
    p=Path('/content/archive.zip')
    with ZipFile(p,'w',ZIP_DEFLATED) as z:z.writestr('matrices.json',json.dumps(data,indent=2))
    print('archive_sha256',hashlib.sha256(p.read_bytes()).hexdigest())

if __name__=='__main__':main()
