"""Reproduce the retained tables and verify the symbolic minimax envelopes."""
from pathlib import Path
import json,runpy
from fractions import Fraction
root=Path(__file__).parent
def verify():
    extremal=runpy.run_path(str(root/'season-precision.py'))['solve']()
    robust=runpy.run_path(str(root/'season-robust.py'))['run']()
    for filename,computed in [('unequal-precision.json',extremal),('robust-anchors.json',robust)]:
        if json.loads((root/filename).read_bytes())!=computed:raise ArithmeticError(filename)
    if len(robust['1'])!=57 or len(extremal)!=7:raise ArithmeticError('enumeration')
    for k,record in extremal.items():
        n=len(k.split(','))
        expected=[{'line':['9','2'],'start':'0'}] if n==5 else [{'line':['3','2'],'start':'0'},{'line':['6','1'],'start':'1/3'}]
        if record['segments']!=expected:raise ArithmeticError(('formula',k))
        for ratio,w in record['witnesses'].items():
            x=Fraction(ratio);h=list(map(Fraction,w['h']));j=w['j']-1
            seasonal=[sum(h[i:i+3])/3 for i in range(4)]
            if max(map(abs,seasonal))>x or any(abs(h[i-1])>1 for i in w['survivors']):raise ArithmeticError('lower witness')
            if h[j]!=(9*x+2 if n==5 else max(3*x+2,6*x+1)):raise ArithmeticError('endpoint')
    for k,r in robust['1'].items():
        n=len(k.split(','))
        if r!=({5:'11',6:'7'}.get(n)):raise ArithmeticError('equal-noise design')
    return {'seasonal_means':4,'coordinates':6,'designs_with_at_least_two_months':57,'unequal_error_designs':7,'witness_ratios':['0','1/4','1','4']}
if __name__=='__main__':print(json.dumps(verify(),sort_keys=True))
