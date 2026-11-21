"""Check archive identities and classification with an independent sum-counting algorithm."""
from pathlib import Path
from fractions import Fraction
from itertools import combinations
from bisect import bisect_left
from math import comb
import json
root=Path(__file__).parent
def read(n):return json.loads((root/n).read_bytes())
def below(values,t):
    v=sorted(values);total=0
    for i,j,k in combinations(range(len(v)),3):
        total+=bisect_left(v,t-v[i]-v[j]-v[k],lo=k+1)-k-1
    return total
def check():
    a=read('frame.json');obs=read('gate.json');summary=a['summary'];rows=a['rows']
    if len(rows)!=64 or len({x['parts'][0]['url'] for x in rows.values()})!=64:raise ValueError('Speaker coverage')
    valid=[(x,y) for x in range(3100,3300) for y in range(3700,3900) if abs(Fraction(x,7515)-Fraction(426,1000))<Fraction(1,2000) and abs(Fraction(y,10910)-Fraction(351,1000))<Fraction(1,2000) and abs(Fraction(x+y,18425)-Fraction(381,1000))<Fraction(1,2000)]
    if list(map(list,valid))!=obs['pairs']:raise ValueError('Rounded edit counts')
    totals=[x+y for x,y in valid];limits=[(20*t+2)//3-18425 for t in (min(totals),max(totals))]
    if limits!=[28389,28435]:raise ValueError('Gate cutoffs')
    tests={}
    for r,rule in enumerate(summary['rule_order']):
        vals=[p['counts'][rule] for k,p in rows.items() if k not in ('025','027')]
        lo,high=[below(vals,t) for t in limits];marginal=[lo,high-lo,comb(len(vals),4)-high];counts=[sum(v for key,v in summary['classes'].items() if key.split('/')[r]==cls) for cls in ['impossible','rounding_sensitive','possible_all_roundings']]
        if marginal!=counts:raise ArithmeticError((rule,marginal,counts))
        tests[rule]=counts
    return dict(frames=summary['designs'],observed=sorted(set(totals)),thresholds=limits,marginal_verification=tests)
if __name__=='__main__':print(json.dumps(check(),sort_keys=True))
