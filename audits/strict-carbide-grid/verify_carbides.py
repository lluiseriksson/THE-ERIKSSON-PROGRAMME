from decimal import Decimal as D
from pathlib import Path
import json
r=json.loads(Path('reference-errors.json').read_bytes())
g=json.loads(Path('grid.json').read_bytes())
if [g['strict_unique'],r['strict_candidates'],r['unlisted'],r['winner']]!=[1251,1251,1156,2]:
    raise ValueError('Population')
for k,rank in [('independent',3),('shared',3),('common_offset',4)]:
    v=r['models'][k]
    lo,hi=map(D,v['interval_meV'])
    if not (v['best_listed']==rank and 0<lo<hi<min(D(v['next_listed_lower']),D(v['hidden_lower']))):
        raise ValueError(k)
if not r['mixed_one_face'] or D(r['limiting_face']['shared_to_independent'])!=D('0.25'):
    raise ValueError('Mixed certificate')
print('Population, sensitivity bounds and mixed face consistent.')