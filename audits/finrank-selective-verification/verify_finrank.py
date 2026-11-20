"""Cross-check retained finite certificates during typesetting without downloading upstream text."""
import json
from pathlib import Path
def read(name):return json.loads(Path(name).read_bytes())
def need(x): 
    if not x:raise ValueError('Inconsistent paper inputs')
g=read('geometry.json');flags=read('flags.json');f=read('fidelity.json');sel=read('selection.json')
need(g['valid_seeded']==f['counts']['prepared']==411)
need(g['all_rows']['rows_with_some_alias']==0 and g['all_factors']['valid_item_factors']==1644)
need(f['counts']['all']==1185 and f['model_calls']==0 and g['all_factors']['alias']==0)
for n,extra,lo,hi,plainlo in [('60',25,5,14,7),('40',9,0,4,1)]:
    row=flags[n]
    for key,lower in [('full',lo),('canonical_witnesses',plainlo)]:
        need(row[key]['gain']==[extra] and row[key]['silent_C']==list(range(lower,hi+1)) and row[key]['silent_B']==list(range(lower+extra,hi+extra+1)))
need(sel['mistral_guaranteed_gain']==36 and sel['mistral_strict_below_clean']==45)
print(json.dumps(dict(templates=1644,eligible=411,panels=[60,40],gains=[25,9],thresholds=[36,45]),sort_keys=True))