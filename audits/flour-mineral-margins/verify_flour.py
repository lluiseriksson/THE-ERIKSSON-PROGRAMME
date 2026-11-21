"""Cross-check the public numerical certificates and regenerate the outlet constructions."""
import json,subprocess,sys
from fractions import Fraction as F
from pathlib import Path
def load(name):return json.loads(Path(name).read_bytes())
a=load('design.json');p=load('precision.json');out=load('outlets.json')
if json.loads(subprocess.check_output([sys.executable,'pooled-outlets.py']))!=out:raise ValueError('Outlet construction changed')
if a['singular_value_lower']!=105 or a['distance_bounds']['iron'] is not None or not p['rounding_witness']:raise ValueError('Inputs')
for key in ('calcium','zinc'):
    e=a['distance_bounds'][key];v=p['margins'][key]
    if not (0<F(e['lower'])<=F(str(v['minimum']))<=F(str(v['maximum']))<=F(e['upper'])):raise ValueError(key)
if out['checks']!=60 or any({r['passing'] for r in out['cases'] if r['closure']==c and r['basis']==s}!=set(range(10)) for c in range(3) for s in ('dry','as_weighed')):raise ValueError('Outlet cases')
print('Nested uncertainty bounds and 60 finite-population certificates checked.')