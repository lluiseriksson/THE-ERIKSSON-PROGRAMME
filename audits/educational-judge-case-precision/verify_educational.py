from pathlib import Path
import json
from dual_audit import frontier
def need(ok):
    if not ok:raise ValueError('Certificate mismatch')
witnesses=json.loads(Path('overlap.json').read_bytes())
for label,pair in witnesses['ranges'].items():
    for w in pair:
        rows=[(x['pattern'],x['cases']) for x in w['matrix']]
        need(all(len(p)==6 and n>0 and isinstance(n,int) and any(p) and p[2] in (0,1) and all(e in (0,2) for e in p[3:5]) and all(e in (0,1,2) for e in p) for p,n in rows))
        def total(f):return sum(n*f(p) for p,n in rows)
        need([total(lambda p:1),total(lambda p:any(p[:5])),total(lambda p:bool(p[5])),*[total(lambda p:bool(p[i])) for i in range(5)],total(lambda p:p.count(2))]==[72,50,23,10,5,20,16,14,43])
        if label.startswith('5:'):need(total(lambda p:p[0]==2)==5)
        need(w['value']==total(lambda p:2 in p and (label.endswith(':any') or 1 not in p)))
d=json.loads(Path('dual.json').read_bytes())
for k,expected in d['designs'].items():
    end,tol=k.split('-')
    need(frontier(end,int(tol))==expected)
print(json.dumps({k:[r['total'] for r in x['optima']] for k,x in d['designs'].items()},sort_keys=True))