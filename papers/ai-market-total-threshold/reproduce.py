"""Exact rational witnesses for common log1p shifts in a category event study."""
from fractions import Fraction as F
from pathlib import Path
from itertools import product
import json, hashlib, zipfile
pre = (119,59)
observed = (119,119)
relative = (1,2)
weights = [F(1+y,sum(1+z for z in observed)) for y in observed]
threshold = sum(w/d for w,d in zip(weights,relative))
cap = min(F(1+y,d) for y,d in zip(observed,relative))
cases = []
for anchor in [F(1,2),F(3,4),F(1)]:
    counter = [F(1+y)/(anchor*d)-1 for y,d in zip(observed,relative)]
    untreated_trends = [F(1+y,1+x) for y,x in zip(counter,pre)]
    assert len(set(untreated_trends))==1 and min(counter)>=0
    effect=sum(observed)-sum(counter)
    assert effect==sum(1+y for y in observed)*(1-threshold/anchor)
    cases.append(dict(anchor=str(anchor),counter=[int(y) for y in counter],common_untreated_multiplier=str(untreated_trends[0]),total_effect=int(effect)))
assert [item['total_effect'] for item in cases]==[-120,0,60] and threshold==F(3,4)
# Check the endpoint cap with a zero-sale cell at the largest relative effect.
obs2=(119,0)
h2=sum(F(1+y,d) for y,d in zip(obs2,relative))/sum(1+y for y in obs2)
cap2=min(F(1+y,d) for y,d in zip(obs2,relative))
assert cap2<h2 and (1+obs2[1])/(cap2*2)-1==0
out=dict(observed=observed,pre=pre,cases=cases,exp_threshold=str(threshold),max_exp_anchor=str(cap),
         zero_at_high_exposure=dict(observed=obs2,exp_threshold=str(h2),max_exp_anchor=str(cap2)),
         scope='Constructed examples, not the platform microdata.')
with zipfile.ZipFile('/content/archive.zip','w',zipfile.ZIP_DEFLATED) as z:z.writestr('certificate.json',json.dumps(out,indent=2))
print('archive_sha256',hashlib.sha256(Path('/content/archive.zip').read_bytes()).hexdigest())
