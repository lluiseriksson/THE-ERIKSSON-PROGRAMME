from fractions import Fraction as F
from pathlib import Path
from zipfile import ZipFile, ZIP_DEFLATED
from itertools import combinations_with_replacement
import json,hashlib
import numpy as np
from sklearn.metrics import f1_score,matthews_corrcoef

def triples(n):
    return [(a,b,n-a-b) for a in range(n+1) for b in range(n-a+1)]

def solve(hits,fstr,mstr):
    # Parameterize by diagonal, false negative counts and false positive counts.
    # Complete margins by an independent one-dimensional integer interval.
    n=122
    correct=np.array(triples(hits),dtype=np.int64)
    error=n-hits
    num=int(fstr.replace('.','')); scale=10**len(fstr.split('.')[1])
    mf=F(mstr); mh=F(1,2*10**len(mstr.split('.')[1]))
    out=[]
    for lost in triples(error):
        for extra in triples(error):
            if any(x+y>error for x,y in zip(lost,extra)):continue
            rows=correct+lost; cols=correct+extra
            den=rows+cols
            h0,h1,h2=den.T
            exact_den=n*h0*h1*h2
            parts=(2*rows*correct).T
            exact_num=parts[0]*h1*h2+parts[1]*h0*h2+parts[2]*h0*h1
            mask=(rows[:,0]>0)&(rows[:,0]<=rows[:,1])&(rows[:,1]<=rows[:,2])&(abs(2*scale*exact_num-2*num*exact_den)<=exact_den)
            for idx in np.flatnonzero(mask):
                R=rows[idx].tolist();C=cols[idx].tolist()
                top=n*hits-sum(x*y for x,y in zip(R,C));bot=(n*n-sum(x*x for x in R))*(n*n-sum(x*x for x in C))
                if top<=0 or bot<=0 or not (mf-mh)**2<=F(top*top,bot)<=(mf+mh)**2:continue
                t=correct[idx].tolist()
                for m01 in range(lost[0]+1):
                    m02=lost[0]-m01
                    m21=extra[1]-m01; m20=lost[2]-m21
                    m10=extra[0]-m20; m12=lost[1]-m10
                    if min(m21,m20,m10,m12)<0 or m02+m12!=extra[2]:continue
                    a=[[t[0],m01,m02],[m10,t[1],m12],[m20,m21,t[2]]]
                    yy=[i for i in range(3) for j in range(3) for _ in range(a[i][j])]
                    pp=[j for i in range(3) for j in range(3) for _ in range(a[i][j])]
                    assert format(f1_score(yy,pp,average='weighted'),'.'+str(len(fstr.split('.')[1]))+'f')==fstr
                    assert format(matthews_corrcoef(yy,pp),'.'+str(len(mstr.split('.')[1]))+'f')==mstr
                    out.append(a)
    return out

x=solve(112,'0.91079235','0.842682')
y=solve(111,'0.906464389','0.827407')
assert x==[[[0,3,0],[1,55,2],[0,4,57]]]
assert y==[[[0,3,0],[2,54,2],[0,4,57]]]
p=Path('/content/archive.zip')
with ZipFile(p,'w',ZIP_DEFLATED) as z:z.writestr('crosscheck.json',json.dumps(dict(first=x,second=y)))
print('archive_sha256',hashlib.sha256(p.read_bytes()).hexdigest())
