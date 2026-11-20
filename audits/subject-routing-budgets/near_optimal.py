"""Find the smallest loss of pooled accuracy that permits any subject to fail."""
from collections import Counter
import csv
import hashlib
import io
import itertools
import json
from pathlib import Path
import sys
from urllib.request import urlopen
import zipfile

import numpy as np


def top(n,u,h,j):
    return np.minimum(j,u)-np.maximum(0,j-(n-h))


def capped_gain(n,u,h,j,ceiling):
    hi=min(j,u)-max(0,j-(n-h))
    lo=max(0,j-(n-u))-min(j,h)
    best=min(hi,ceiling)
    if n==u+h and (best-j)%2:
        best-=1
    return best if best>=lo else None


def envelope(groups):
    n,u,h=map(sum,zip(*groups))
    missing=-2*n-5
    subject_curves=[]
    choices=[]
    for ng,ug,hg in groups:
        outside=n-ng
        other=top(outside,u-ug,h-hg,np.arange(outside+1))
        curve=np.full(n+1,missing)
        choice=np.full(n+1,-1)
        for j in range(ng+1):
            y=capped_gain(ng,ug,hg,j,max(0,ug-hg)-1)
            if y is None:
                continue
            sub=curve[j:j+outside+1]
            better=y+other>sub
            np.copyto(sub,y+other,where=better)
            np.copyto(choice[j:j+outside+1],j,where=better)
        subject_curves.append(curve)
        choices.append(choice)
    best=np.max(subject_curves,axis=0)
    optimal=top(n,u,h,np.arange(n+1))
    margins=[None if b==missing else int(o-b) for o,b in zip(optimal,best)]
    return margins,subject_curves,choices


def counts(v):
    return len(v),v.count(1),v.count(-1)


def selftest():
    for seq in itertools.product((-1,0,1),repeat=6):
        gr=[seq[:3],seq[3:]]
        floors=[max(0,sum(part)) for part in gr]
        opt=[-8]*7
        fail=[-8]*7
        for bits in itertools.product((0,1),repeat=6):
            k=sum(bits)
            gains=[x*b for x,b in zip(seq,bits)]
            s=sum(gains)
            opt[k]=max(opt[k],s)
            if sum(gains[:3])<floors[0] or sum(gains[3:])<floors[1]:
                fail[k]=max(fail[k],s)
        margins,_,_=envelope([counts(part) for part in gr])
        assert margins==[None if f==-8 else o-f for o,f in zip(opt,fail)]


def runs(values):
    start=0
    out=[]
    for val,it in itertools.groupby(values):
        end=start+sum(1 for _ in it)-1
        out.append([start,end,val])
        start=end+1
    return out


def evaluate():
    from mmlu import load_panel
    selftest()
    domains,_,items,_,manifest=load_panel()
    gains=[b-a for _,a,b in items]
    base=sum(a for _,a,_ in items)
    buckets={g:{v:[] for v in (-1,0,1)} for g in domains}
    for i,(g,a,b) in enumerate(items):
        buckets[g][b-a].append(i)
    stats=[(sum(map(len,buckets[g].values())),len(buckets[g][1]),len(buckets[g][-1])) for g in domains]
    n,u,h=map(sum,zip(*stats))
    margins,curves,choices=envelope(stats)
    intervals=runs(margins)
    safe={str(t):[[a,b] for a,b,v in runs([m is None or m>t for m in margins]) if v]
          for t in (0,1,2,3)}
    assert safe["0"]==[[2495,13300]]
    witnesses=[]
    for k in sorted({i for a,b,m in intervals if m is not None for i in (a,b)}):
        idx=max(range(len(domains)),key=lambda i:int(curves[i][k]))
        g=domains[idx]
        j=int(choices[idx][k])
        ng,ug,hg=stats[idx]
        floor=max(0,ug-hg)
        y=capped_gain(ng,ug,hg,j,floor-1)
        local=buckets[g]
        # Choose x negatives and x+y positives; fill the rest with neutrals.
        for neg in range(hg+1):
            pos=neg+y
            neutral=j-neg-pos
            if 0<=pos<=ug and 0<=neutral<=len(local[0]):
                break
        else:raise ValueError("No row witness")
        inside=local[-1][:neg]+local[0][:neutral]+local[1][:pos]
        other=[i for v in (1,0,-1) for name in domains if name!=g for i in buckets[name][v]]
        chosen=sorted(inside+other[:k-j])
        assert len(set(chosen))==len(chosen)==k
        score=base+sum(gains[i] for i in chosen)
        chosen_set=set(chosen)
        group_score=sum((b if i in chosen_set else a) for i,(name,a,b) in enumerate(items) if name==g)
        group_floor=max(sum(row[t] for row in items if row[0]==g) for t in (1,2))
        assert group_score<group_floor and score==base+int(top(n,u,h,k))-margins[k]
        witnesses.append(dict(k=k,loss=margins[k],subject=g,subject_floor=group_floor,
                              subject_correct=group_score,pooled_score=score,indices=chosen))
    return dict(n=n,weak_correct=base,positive=u,negative=h,small_panels=729,
                margin_intervals=intervals,robust_budgets=safe,witnesses=witnesses,
                subjects=domains,source_sha256=manifest)


if __name__=="__main__":
    target=Path(sys.argv[1] if len(sys.argv)==2 and sys.argv[1].endswith(".zip") else "/content/archive.zip")
    with zipfile.ZipFile(target,"w",zipfile.ZIP_DEFLATED) as out:
        out.writestr("margin.json",json.dumps(evaluate(),sort_keys=True,separators=(",",":"))+"\n")
    print("archive_sha256",hashlib.sha256(target.read_bytes()).hexdigest())
