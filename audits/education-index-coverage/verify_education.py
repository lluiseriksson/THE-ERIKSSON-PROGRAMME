"""Enumerate portfolios and verify single-failure coverage against the saved certificates."""
from pathlib import Path
from itertools import combinations
import json
def read(n):return json.loads(Path(n).read_bytes())
def need(test):
    if not test:raise ValueError('Source incidence certificate does not reproduce')
def main():
    second=read('replication.json')['groups'];original=read('index.json')['comparisons']['tokens'];r=read('certificates.json')
    panels=[('first',original['table'],original['including_duplicates']['sources'],'sources')]
    panels.extend((n,second[n]['rows'],sorted(second[n]['six']['loss']),'matches') for n in ('initial','preliminary'))
    out={}
    for n,rows,sources,field in panels:
        masks=[set(x[field]) for x in rows];need(all(masks))
        def coverage(p):return sum(not m.isdisjoint(p) for m in masks)
        full=[];worst={}
        for k in range(1,len(sources)+1):
            levels=[]
            for tup in combinations(sources,k):
                p=set(tup)
                if coverage(p)==len(masks):full.append(tup)
                levels.append(min(coverage(p-{s}) for s in p))
            worst[k]=max(levels);need(worst[k]==r['robustness'][n][str(k)]['best'])
        m=min(map(len,full));out[n]=dict(size=len(rows),minimum=[p for p in full if len(p)==m],at_full_budget=worst[len(sources)])
    need(out['initial']['minimum']==[('acm',)] and out['preliminary']['minimum']==[('ScienceDirect','acm')])
    ids=second['initial']['rows'];need({x['doi'].lower() for x in read('publisher-identities.json')}=={x['doi'] for x in ids})
    need(second['backward']['rows'][0]['doi'] in {x['doi'] for x in ids})
    print(json.dumps(out,sort_keys=True))
if __name__=='__main__':main()