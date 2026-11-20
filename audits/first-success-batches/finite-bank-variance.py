"""Exact variance of the two-attempt signed correction on the released task counts."""
from fractions import Fraction
from itertools import product
from math import prod
from pathlib import Path
from zipfile import ZipFile, ZIP_DEFLATED
import json
import hashlib

COUNTS = [80, 97, 66, 19, 33, 84, 93, 88, 95, 26, 95, 82, 99, 97, 92, 92, 33, 100, 69, 100, 76, 59, 88, 70, 51, 80, 71, 78, 71, 97, 86, 61, 70, 96, 15, 100, 45, 82, 8, 98, 65, 1, 77, 83, 97, 88, 99, 23, 93, 80, 66, 51, 100, 94, 71, 80, 63, 99, 78, 99, 100, 98, 94, 100, 97, 24, 29, 26, 44, 71, 100, 100, 100, 100, 100, 47, 2, 94, 73, 95, 100, 9, 7, 57, 45, 87, 100, 7, 93, 82, 66, 98, 57, 88, 98, 100, 100, 94, 93, 30, 27, 67, 89, 59, 100, 99, 96, 4, 92, 78, 97, 97, 100, 4, 100, 86, 99, 97]

def check(test, reason):
    if not test:
        raise ValueError(reason)

def low_coefficients(a,b,cap):
    result=[0]*cap
    for i,c in enumerate(a):
        for j,d in enumerate(b[:cap-i]):
            result[i+j]+=c*d
    return result

def moments(counts,d,replace):
    # Hit-variable polynomials z^2 H(1/z) for 0, 1 or 2 initial failures.
    basis=((0,0,1),(0,2,-1),(1,0,0))
    m=len(counts)
    cov=[[1]]
    full=weighted=[1]
    denom=d*d if replace else d*(d-1)
    for c in counts:
        q=d-c
        waits=(c*(d if replace else d-1),q*c,q*(q if replace else q-1))
        hits=(waits[2],2*q*c,c*(c if replace else c-1))
        check(sum(hits)==sum(waits)==denom,"mass")
        full=low_coefficients(full,hits,m)
        weighted=low_coefficients(weighted,[hits[0],2*hits[1],hits[2]],m)
        kernel=[(j,k,sum(weight*v[j]*v[k] for weight,v in zip(waits,basis)))
                for j,k in product(range(3),repeat=2)]
        size=min(m,len(cov)+2)
        nxt=[[0]*size for _ in range(size)]
        for j,k,w in kernel:
            if w==0:continue
            for i,row in enumerate(cov[:size-j] if j<size else []):
                target=nxt[i+j]
                for h,x in enumerate(row[:size-k] if k<size else []):
                    target[h+k]+=w*x
        cov=nxt
    den=denom**m
    miss=Fraction(sum(full),den)
    e2=Fraction(sum(map(sum,cov)),den)
    variance=e2-miss*miss
    boundary=Fraction(weighted[-1]-full[-1],den)
    check(variance >= miss*(1-miss)+boundary,"conditional variance decomposition")
    return 1-miss,variance,boundary

def brute_strata(counts,d,replace):
    m=len(counts)
    expected=square=cases=0
    for draws in product(range(d),repeat=2*m):
        if not replace and any(draws[2*i]==draws[2*i+1] for i in range(m)):continue
        polynomial=[1]
        for i,c in enumerate(counts):
            a,b=draws[2*i:2*i+2]
            h=(0,0,1) if a<c else ((0,2,-1) if b<c else (1,0,0))
            polynomial=low_coefficients(polynomial,h,m)
        score=1-sum(polynomial)
        expected+=score
        square+=score*score
        cases+=1
    mean=Fraction(expected,cases)
    return mean,Fraction(square,cases)-mean*mean

def output(x):
    return {"numerator":str(x.numerator),"denominator":str(x.denominator),"approx":float(x)}

def main():
    tiny=0
    for counts in ([0],[1],[3],[0,2],[1,2],[2,1],[1,2,3],[2,2,2]):
        for replace in [True,False]:
            check(moments(counts,3,replace)[:2]==brute_strata(counts,3,replace),"labelled small bank")
            tiny+=1
    cases=[]
    for panel,counts in [('all',COUNTS),('mixed',[v for v in COUNTS if 0<v<100])]:
        for replace in (True,False):
            mean,var,bound=moments(counts,100,replace)
            cases.append(dict(panel=panel,replacement=replace,miss=output(1-mean),variance=output(var),
                              boundary_conditional_variance_contribution=output(bound),
                              variance_relative_to_full_indicator=output(var/(mean*(1-mean)))))
    archive=Path('/content/archive.zip')
    with ZipFile(archive,'w',ZIP_DEFLATED) as z:
        z.writestr('variance.json',json.dumps(dict(small_labelled_checks=tiny,cases=cases),sort_keys=True))
    print('archive_sha256',hashlib.sha256(archive.read_bytes()).hexdigest())
if __name__=="__main__":
    main()

