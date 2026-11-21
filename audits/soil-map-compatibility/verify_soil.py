import json,runpy
from pathlib import Path
v=runpy.run_path('soil-compatibility.py')['run']()
if v!=json.loads(Path('compatibility.json').read_bytes()):
    raise ValueError('Recomputed certificate differs')
for name,record in v['results'].items():
    from fractions import Fraction as F
    for triplet in record['vertices']:
        a,b,i=map(F,triplet);u=a+b-i
        # Evaluate inequalities through the distinct construction x = s*u-i, y=b-i.
        for s,accept in [(F(record['min_optimum_millionths'][0],10**6),True),(F(record['max_optimum_millionths'][1],10**6),False)]:
            x=max(0,s*u-i)
            if (x<=a-i and b>=s*(b+x)) != accept:raise ValueError((name,triplet,s))
print(json.dumps({k:[a['min_optimum_millionths'],a['max_optimum_millionths']] for k,a in v['results'].items()},sort_keys=True))
