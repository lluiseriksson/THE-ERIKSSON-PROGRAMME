"""Sharp latency thresholds for mixtures of the seven reported forecast batch sizes."""
from pathlib import Path
from fractions import Fraction as F
import json
def band(s):
    step=F(1,10**len(s.partition('.')[2]))
    return F(s)-step/2,F(s),F(s)+step/2
def rows():
    data=json.loads(Path('primary.json').read_bytes())['rows'];m={};large={}
    for z in data:
        if len(z)==10 and z[1].replace(',','').isdigit():
            if z[0]:model=z[0]
            m.setdefault(model,{})[int(z[1].replace(',',''))]=[band(z[i]) for i in [2,3,7,4]]
        elif len(z)==3 and z[0].replace(',','').isdigit():large[int(z[0].replace(',',''))]=band(z[1])
    if len(m)!=2 or len(large)!=7 or not all(x.keys()==large.keys() for x in m.values()):raise ValueError('Table 8 extraction')
    return m,large
def linked_times(base,cold,multiplier):
    # Project the feasible set base*multiplier == cold onto both time axes.
    base_min=max(base[0],cold[0]/multiplier[2])
    base_max=min(base[2],cold[2]/multiplier[0])
    cold_min=max(cold[0],base[0]*multiplier[0])
    cold_max=min(cold[2],base[2]*multiplier[2])
    if base_min>base_max or cold_min>cold_max:
        raise ValueError('Linked printed columns admit no common unrounded times')
    for b,c in [(base_min,cold_min),(base_max,cold_max)]:
        if not multiplier[0]<=c/b<=multiplier[2]:
            raise ValueError('Marginal endpoint pair is not attainable')
    return (base_min,base[1],base_max),(cold_min,cold[1],cold_max)


def bound(cold,saving):
    # One first-use cold batch followed by N-1 reuses. Strict total improvement.
    worst=max(cold.values());least=min(saving.values())
    if worst<0 and least>=0:return 1
    if least<=0:return None
    return max(1,2+int(worst//least))
out={}
models,large=rows()
for model,r in models.items():
    bands={}
    for fi,(bs,cs,wm,cm) in r.items():
        bs,cs=linked_times(bs,cs,cm)
        t=large[fi]
        bands[fi]=dict(cold_premium=[cs[0]-t[2],cs[1]-t[1],cs[2]-t[0]],warm_saving=[t[0]-bs[2]*wm[2],t[1]-bs[1]*wm[1],t[2]-bs[0]*wm[0]])
    scenarios={}
    for name,vols in [('all',list(r)),('small',[1,10,100]),('tiny',[1,10])]:
        each={}
        for label,cidx,widx in [('printed',1,1),('pessimistic',2,0),('optimistic',0,2)]:
            cold={f:bands[f]['cold_premium'][cidx] for f in vols};saving={f:bands[f]['warm_saving'][widx] for f in vols}
            n=bound(cold,saving);D=max(cold.values());S=min(saving.values())
            cf=max(cold,key=cold.get);wf=min(saving,key=saving.get)
            if n is not None and n>1:assert D-(n-1)*S<0<=D-(n-2)*S
            each[label]=dict(batches=n,cold_size=cf,reuse_size=wf,worst_startup=str(D),least_saving=str(S),at_previous=str(D-(n-2)*S) if n and n>1 else None)
        scenarios[name]=each
    out[model]=dict(bands={f:{k:list(map(str,a)) for k,a in v.items()} for f,v in bands.items()},scenarios=scenarios)
print(json.dumps(out,indent=2))