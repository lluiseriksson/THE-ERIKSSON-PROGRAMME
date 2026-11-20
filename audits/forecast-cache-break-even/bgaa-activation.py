"""Determine whether deferring the first cold batch can lower total service time."""
from pathlib import Path
from fractions import Fraction as F
import json
def interval(text):
    d=F(1,2*10**len(text.partition('.')[2]))
    return F(text)-d,F(text)+d
r=json.loads(Path('primary.json').read_bytes())['rows']
ref={int(x[0].replace(',','')):interval(x[1]) for x in r if len(x)==3 and x[0].replace(',','').isdigit()}
data={};sizes={}
for z in r:
    if len(z)!=10 or not z[1].replace(',','').isdigit():continue
    if z[0]:model=z[0]
    n=int(z[1].replace(',',''));b=interval(z[2]);cold=interval(z[3]);ratio=interval(z[4]);wm=interval(z[7])
    low=max(b[0],cold[0]/ratio[1]);high=min(b[1],cold[1]/ratio[0])
    vertices=set([low,high]+[v/a for v in cold for a in ratio if low<=v/a<=high])
    candidates=[]
    for v in vertices:
        for c in [max(cold[0],v*ratio[0]),min(cold[1],v*ratio[1])]:
            assert cold[0]<=c<=cold[1] and ratio[0]<=c/v<=ratio[1]
            for w in wm:
                t=ref[n][0];candidates.append((c-v*w,c-t,t-v*w,v,c,w))
    sizes.setdefault(model,{})[n]={'min_setup':str(min(z[0] for z in candidates)),'max_premium':str(max(z[1] for z in candidates)),'min_saving':str(min(z[2] for z in candidates))}
for m,ds in sizes.items():
    b=min(F(z['min_setup']) for z in ds.values());a=max(F(z['max_premium']) for z in ds.values());sv=min(F(z['min_saving']) for z in ds.values())
    data[m]=dict(sizes=ds,min_setup=str(b),max_premium=str(a),min_saving=str(sv),adjacent_margin=str(b-a),immediate_dominates_all_paid=sv>=0 and b>=a)
print(json.dumps(data,indent=2))