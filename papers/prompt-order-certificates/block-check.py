from datetime import datetime, timezone
from itertools import combinations, product
from pathlib import Path
import hashlib, json, zipfile

def outcome_vectors(n,total):
    return [set(idx) for idx in combinations(range(n),total)]

def feasible(weights,a,b):
    return {sum(weights[i] for i in B)-sum(weights[i] for i in A)
            for A in outcome_vectors(len(weights),a) for B in outcome_vectors(len(weights),b)}

def prediction(weights,a,b):
    w=sorted(weights)
    return sum(w[:b])-sum(w[len(w)-a:]),sum(w[len(w)-b:])-sum(w[:a])

profiles=[[1],[2,7],[4,4,4],[1,2,5,9],[1,1,3,7,8],[2,3,5,7,11,13]]
checked=0
for weights in profiles:
    for a,b in product(range(len(weights)+1),repeat=2):
        scores=feasible(weights,a,b)
        assert (min(scores),max(scores))==prediction(weights,a,b)
        checked+=1
blocks=[([1,4,11],2,2),([2,3,9,10],1,3),([1,8],2,1)]
ranges=[feasible(*block) for block in blocks]
extremes=[prediction(*block)[0] for block in blocks]
for drop in range(3):
    ks=list(combinations(range(3),drop))
    sets=[set(range(3))-set(k) for k in ks]
    lower=min(min(sum(x[i] for i in keep) for keep in sets) for x in product(*ranges))
    assert lower==sum(extremes)-sum(sorted(extremes,reverse=True)[:drop])
    assert tuple(extremes) in product(*ranges)
# Published confirmatory margins: every feasible binary overlap.
n,a,b=36,16,33
tables=[]
for overlap in range(max(0,a+b-n),min(a,b)+1):
    g,l=b-overlap,a-overlap
    tables.append([g,l,overlap,n-overlap-g-l])
for R in [1,2,5,6,7,10]:
    for m in range(18):
        exact=min(g-R*l-min(g,m) for g,l,_,_ in tables)
        assert exact==20-m-3*R
examples={'possible_reversal':[[18,16,15],[18,0,18]],'robust_in_both_blocks':[[18,8,16],[18,8,17]]}
assert all(sum(z[j] for z in x)==v for x in examples.values() for j,v in enumerate([n,a,b]))
assert [(min(r[2]-r[1] for r in x)) for x in examples.values()]==[-1,8]
report={'status':'passed','block_margin_scenarios':checked,'weights':profiles,'simultaneous_example':blocks,'worst_blocks':extremes,'paired_tables':tables,'examples':examples,'published_margins':[36,16,33],'classification':'synthetic feasibility checks, not the observed replication data','finished_at':datetime.now(timezone.utc).isoformat()}
zpath=Path('/content/block-margins.zip')
with zipfile.ZipFile(zpath,'x',zipfile.ZIP_DEFLATED) as z:z.writestr('verification.json',json.dumps(report,sort_keys=True))
print('archive_sha256 '+hashlib.sha256(zpath.read_bytes()).hexdigest())
