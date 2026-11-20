"""Certify or refute monotonicity of work times variance for finite Bernoulli budgets."""
from fractions import Fraction as F
from math import comb
from itertools import combinations
from pathlib import Path
import json,hashlib
from zipfile import ZipFile,ZIP_DEFLATED

def parts(t,m,lo=1):
    if m==1:
        if t>=lo:yield (t,)
    else:
        for k in range(lo,t//m+1):
            for y in parts(t-k,m-1,k):yield (k,)+y

def coefficients(a):
    v=[1]
    for n in a:
        w=[0]*(len(v)+n-1)
        for j,k in enumerate(v):
            for i in range(n):w[i+j]+=k
        v=w
    return v

def metrics(a,p):
    q=1-p;m=len(a)
    count=coefficients(a)
    C=[comb(j+m-1,m-1) for j in range(len(count))]
    target=p**m*sum(k*q**j for j,k in enumerate(C))
    V=p**m*sum(F(k*k,h)*q**j for j,(k,h) in enumerate(zip(C,count))) - target**2
    W=sum((1-q**n)/p for n in a)
    return W,V,W*V

def main():
    certified=[];global_counter=None;local_counter=None
    for T in range(3,20):
        for m in range(2,T):
            a=list(parts(T,m));bal=a[-1]
            for p in [F(1,8),F(1,2),F(7,8)]:
                table={x:metrics(x,p) for x in a}
                y=min(a,key=lambda x:table[x][2])
                if table[y][2]<table[bal][2] and global_counter is None:global_counter=[T,m,str(p),y,bal,[str(x) for x in table[y]],[str(x) for x in table[bal]]]
                for x in a:
                    for i,j in combinations(range(m),2):
                        if x[j]-x[i]<2:continue
                        z=list(x);z[i]+=1;z[j]-=1;z=tuple(sorted(z))
                        if table[x][2]<table[z][2] and local_counter is None:local_counter=[T,m,str(p),x,z,[str(v) for v in table[x]],[str(v) for v in table[z]]]
                certified.append([T,m,str(p),len(a),str(table[y][2]),list(y)])
    p=Path('/content/archive.zip')
    with ZipFile(p,'w',ZIP_DEFLATED) as z:z.writestr('work.json',json.dumps(dict(global_counter=global_counter,local_counter=local_counter,grid=certified)))
    print('archive_sha256',hashlib.sha256(p.read_bytes()).hexdigest())
if __name__=='__main__':main()
