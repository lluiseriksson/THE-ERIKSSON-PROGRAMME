"""Rank stability under bounded structure-energy and shared reference-energy errors."""
from decimal import Decimal as D, getcontext
from itertools import combinations
import json
getcontext().prec = 48
kb = D('1.380649e-23') / D('1.602176634e-19')
def entropy(x):
    return -kb * sum(f*f.ln() for f in x if f)/2
def values(row):
    return tuple(map(D,row['fractions']))
def strict(x):
    return len(set(v for v in x if v)) > 1
def grid():
    for splits in combinations(range(13),5):
        ends=(-1,*splits,13)
        yield tuple(D(b-a-1)/8 for a,b in zip(ends,ends[1:]))
rows=json.load(open('table-s1.json',encoding='utf8'))['rows']
assert len(rows)==100 and [int(r['rank']) for r in rows]==list(range(1,101))
table={values(r):r for r in rows}
assert len(table)==100 and all(D(a['T'])<=D(b['T']) for a,b in zip(rows,rows[1:]))
winner=next(r for r in rows if strict(values(r)))
w=values(winner); sw=entropy(w); tw=D(winner['T'])
seen=0; hidden=0
bounds={m:[] for m in ('independent','shared','common_offset')}
for x in grid():
    if not strict(x): continue
    seen+=1
    if x==w: continue
    r=table.get(x); hidden+=int(r is None); rank=int(r['rank']) if r else 0
    gap=D((r or rows[-1])['T'])-tw
    sj=entropy(x)
    A=1/sw+1/sj
    B=sum(abs(a/sw-b/sj) for a,b in zip(w,x))
    C=abs(1/sw-1/sj)
    for m,coef in zip(bounds,(A,B,C)):
        if coef:
            lo=1000*(gap-D('.001'))/coef
            hi=1000*(gap+D('.001'))/coef if r else None
            bounds[m].append((lo,hi,rank,tuple(map(str,x))))
assert seen==1251 and hidden==1156
summary={}
for m,items in bounds.items():
    known=sorted(t for t in items if t[2]); unpublished=min(t[0] for t in items if not t[2])
    best=known[0]
    summary[m]=dict(best_listed=best[2],interval_meV=[str(best[0]),str(best[1])],next_listed_lower=str(known[1][0]),hidden_lower=str(unpublished),globally_certified=best[1]<min(known[1][0],unpublished))
i,s=summary['independent'],summary['shared']
same=i['globally_certified'] and s['globally_certified'] and i['best_listed']==s['best_listed']
result=dict(winner=int(winner['rank']),strict_candidates=seen,unlisted=hidden,models=summary,mixed_one_face=same)
if same:
    rival=next(r for r in rows if int(r['rank'])==s['best_listed'])
    y=values(rival); sy=entropy(y); A=1/sw+1/sy; B=sum(abs(a/sw-b/sy) for a,b in zip(w,y))
    result['limiting_face']=dict(rank=int(rival['rank']),shared_to_independent=str(B/A),gap_K=str(D(rival['T'])-tw),units='independent + (B/A)*shared in meV/atom',radius_meV=i['interval_meV'])
print(json.dumps(result,indent=2,sort_keys=True))