"""Evaluate two specified retrospective retry protocols from published per-task counts."""
from fractions import Fraction
from hashlib import sha256
from itertools import product
from math import comb, prod, perm
from pathlib import Path
from urllib.request import urlopen
from zipfile import ZipFile, ZIP_DEFLATED
import json

URL = ('https://raw.githubusercontent.com/evalplus/evalplus.github.io/'
       '87418456d3a8c2bc6265f24ff91d2dd0e7993f4b/results/evalperf/'
       'Qwen--CodeQwen1.5-7B-Chat_vllm_temp_1.0_evalperf_results.brief.json')

def convolve(a,b):
    result=[0]*(len(a)+len(b)-1)
    for i,c in enumerate(a):
        for j,v in enumerate(b):
            result[i+j]+=c*v
    return result

def scores(counts,D,n,replace):
    m=len(counts)
    power=(lambda x,k:x**k) if replace else perm
    den=power(D,n)
    full,waits,cap=[1],[1],[1]
    for c in counts:
        q=D-c
        full=convolve(full,[comb(n,j)*power(c,j)*power(q,n-j) for j in range(n+1)])
        if replace:
            hit=[q**j*c*D**(n-1-j) for j in range(n)]
        else:
            hit=[perm(q,j)*c*perm(D-j-1,n-j-1) for j in range(n)]
        assert sum(hit)+power(q,n)==den
        waits=convolve(waits,hit)
        cap=convolve(cap,[1]*n)
    assert sum(full)==den**m
    tail=Fraction(sum(full[m:]),den**m)
    score=sum(Fraction(v*comb(m+j-1,j),cap[j]*den**m) for j,v in enumerate(waits))
    return tail,score

def brute(counts,D,n,replace):
    m=len(counts)
    cap=[1]
    for _ in counts: cap=convolve(cap,[1]*n)
    full=score=0
    for seq in product(range(D),repeat=m*n):
        blocks=[seq[i*n:(i+1)*n] for i in range(m)]
        if not replace and any(len(set(b))<n for b in blocks):continue
        hits=[[x<c for x in b] for c,b in zip(counts,blocks)]
        full+=sum(map(sum,hits))>=m
        if all(map(any,hits)):
            j=sum(v.index(True) for v in hits)
            score+=Fraction(comb(m+j-1,j),cap[j])
    den=(D**n if replace else perm(D,n))**m
    return Fraction(full,den),Fraction(score,den)

def bound(v):
    if v==0:return dict(lower=0,upper=0,places=0)
    extra_bits=max(0,v.denominator.bit_length()-v.numerator.bit_length())
    digits=16+(extra_bits*30103+99999)//100000
    scaled=v*10**digits
    return dict(lower=scaled.numerator//scaled.denominator,upper=-(-scaled.numerator//scaled.denominator),places=digits)

def main():
    with urlopen(URL,timeout=25) as reply:raw=reply.read(2_000_001)
    assert len(raw)<2_000_001
    x=json.loads(raw,parse_float=Fraction)
    D=x['config']['n_samples']
    assert D==100 and len(x['eval'])==118
    input_counts={}
    for task,row in x['eval'].items():
        pct=row['pass@1']
        assert pct is not None
        c=Fraction(pct)*D/100
        assert c.denominator==1 and 0<=c<=D
        input_counts[task]=int(c)
    tests=0
    for cs in ([0,3],[1,2],[3,1],[2,2]):
        for replace in (True,False):
            assert scores(cs,3,2,replace)==brute(cs,3,2,replace)
            tests+=1
    panels={'all':list(input_counts.values()),
            'interior':[c for c in input_counts.values() if 0<c<D]}
    results=[]
    for label,counts in panels.items():
        for n in (2,3):
            for replace in (True,False):
                tail,score=scores(counts,D,n,replace)
                assert tail>0
                results.append(dict(panel=label,tasks=len(counts),cap=n,replacement=replace,
                                    full=bound(tail),stopped=bound(score),ratio=bound(score/tail),
                                    full_miss=bound(1-tail)))
    evidence=dict(url=URL,sha256=sha256(raw).hexdigest(),model='CodeQwen1.5-7B-Chat',
                  n_samples=D,temperature=float(x['config']['temperature']),
                  inputs=input_counts,zero=sum(c==0 for c in input_counts.values()),
                  perfect=sum(c==D for c in input_counts.values()),tests=tests,results=results)
    dest=Path('/content/archive.zip')
    with ZipFile(dest,'w',ZIP_DEFLATED) as z:z.writestr('retrospective.json',json.dumps(evidence,sort_keys=True))
    print('archive_sha256',sha256(dest.read_bytes()).hexdigest())

if __name__=='__main__':main()
