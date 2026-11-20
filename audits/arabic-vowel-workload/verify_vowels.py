"""Check saved aggregate counts and finite-population risks using integer arithmetic."""
from fractions import Fraction as F
from math import comb
import json
from pathlib import Path

def read(name):
    return json.loads(Path(name).read_bytes())

def need(ok):
    if not ok:
        raise ValueError('Inconsistent published certificate')

def swap(k,original,n,errors):
    ways=comb(n,k)
    counts={x:comb(errors,x)*comb(n-errors,k-x)
            for x in range(max(0,k-n+errors),min(k,errors)+1)}
    need(sum(counts.values())==ways)
    mean=F(sum(x*t for x,t in counts.items()),ways)
    need(mean==F(k*errors,n))
    return dict(gain=str(original-mean),win=str(F(sum(t for x,t in counts.items() if x<original),ways)),tie=str(F(counts.get(original,0),ways)),loss=str(F(sum(t for x,t in counts.items() if x>original),ways)))

p=read('transfer.json');s=read('external.json');fr=read('frontier.json')
need(p['chosen_on_development']==77 and p['gain']=='0' and p['revision']==s['padt_pin'])
b=p['bands_test']
need(b['77']==[24,8] and b['60']==[422,121] and sum(x[0] for x in b.values())==4327)
a=s['analysis'];c=a['cells'];flow=s['flow']
need(flow['input']==1200 and flow['input']==sum(flow.get(k,0) for k in ('used','unaligned','duplicate','padt_overlap')))
need(a['original_fills']==c['base']+c['77'] and a['original_errors']==c.get('base_err',0)+c.get('77_err',0))
res={'padt':swap(24,8,422,121),'external':swap(c['77'],c.get('77_err',0),c['60'],c.get('60_err',0))}
need(F(fr['comparisons']['0.77']['optimum']['errors'])==31-F(res['padt']['gain']))
need(res['external']['gain']==a['gain'] and F(a['original_errors'])-F(a['gain'])==F(a['alternative_errors']))
for arm in res.values():
    need(sum(F(arm[k]) for k in ['win','tie','loss'])==1)
print(json.dumps(res,sort_keys=True))
