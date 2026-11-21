"""Check endpoint witnesses with exact arithmetic and an independent cost test."""
from collections import Counter
from fractions import Fraction
import json
from pathlib import Path

def require(ok, why):
    if not ok: raise ValueError(why)
d=json.loads(Path('deletion.json').read_bytes())
base=json.loads(Path('baseline-frontier.json').read_bytes())['tab']
names=d['methods']; expected={(g,n):count for g,n,count in d['blocks']}
groups={'standard':[14,15,19,21,19,21,22], 'typo':[0,1,2,3,6,7,7],
    'truncated':[4,4,4,5,4,5,6], 'dialect_phrase':[0,0,0,4,0,4,4],
    'dialect_word':[1,1,2,4,2,4,4], 'spelling_variant':[1,2,2,4,2,4,2],
    'loanword':[2,2,3,3,3,3,3], 'brand':[2]*7, 'ambiguous':[1]*7}
def exposed(points):
    slopes=sorted({Fraction(0)}|{Fraction(a[1]-b[1],a[0]-b[0]) for a in points for b in points if a[0]!=b[0] and (a[0]-b[0])*(a[1]-b[1])>0})
    for lo,hi in zip(slopes,slopes[1:]+[slopes[-1]+2]):
        rate=(lo+hi)/2
        vals=[y-rate*x for x,y in points]
        if all(vals[5]>v for j,v in enumerate(vals) if j!=5):return True
    return False
summary={}
for k,r in d['extrema'].items():
    totals=Counter(); blocks=Counter(); gains=losses=restores=0
    for g,n,bits,count in r['witness']:
        p=list(map(int,bits));inside=g!='gap';blocks[g,n]+=count
        require(len(p)==7 and count>0 and n>0,'Malformed row')
        points=[]
        for j,name in enumerate(names):
            u,y,v,x=base[name];totals[g,j]+=p[j]*count
            totals[inside,j,'events']+=n*p[j]*count
            totals[inside,j,'queries']+=p[j]*count
            points.append((x if inside else x-n*p[j],y-n*p[j] if inside else y))
        restores+=count*exposed(points)
        if inside:
            require(p[0]<=p[1]<=p[2] and all(p[2]<=p[j] for j in (3,4,5)),'Paired comparisons')
            gains+=count*(p[6]>p[5]);losses+=count*(p[6]<p[5])
        else:require(p[2]<=p[5],'Gap comparison')
    require(blocks==expected and (gains,losses)==(2,2),'Block frequency or switches')
    for j,name in enumerate(names):
        require(list(base[name])==[totals[True,j,'queries'],totals[True,j,'events'],totals[False,j,'queries'],totals[False,j,'events']],'Marginal overall counts')
        for g,v in groups.items():require(totals[g,j]==v[j],'Phenomenon counts')
    require(restores==r['count'],'Endpoint')
    summary[k]=restores
print(json.dumps(summary,sort_keys=True))
