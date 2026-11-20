"""Recover attainable third retry scores from two rounded scores per task block."""
import hashlib
import io
import json
from collections import defaultdict
from fractions import Fraction
from itertools import combinations_with_replacement
from math import comb, isqrt
from urllib.request import urlopen

REVISION = '999e282fd3cad526dfe850e093ca671ed3dc5b43'
FILE = 'data/humaneval.cpp.StarCoder2_15b_16k.0.2.reworded-00000-of-00001.parquet'
URL = 'https://huggingface.co/datasets/bigcode/MultiPL-E-completions/resolve/' + REVISION + '/' + FILE
DIGEST = 'a9e40e12d6454d9f6bbaced4f453c3139e71fc8c745535f5f7c2d29616a8e395'

def display(failed, total):
    """Decimal percentage, in tenths, round-half-up (integer arithmetic)."""
    return (2000*(total-failed)+total)//(2*total)

def counts_in_bin(label, total):
    return [i for i in range(total+1) if display(i,total)==label]

def inverse(n, tasks, labels):
    first,second = (counts_in_bin(label,tasks*comb(n,k)) for k,label in enumerate(labels,1))
    candidates=set()
    for s in first:
        for pairs in second:
            squares=s+2*pairs
            # With one or two tasks, pad with leading zero failure counts.
            for x in (range(min(n,s//3)+1) if tasks==3 else (0,)):
                residual=s-x
                delta=2*(squares-x*x)-residual*residual
                if delta<0:continue
                root=isqrt(delta)
                if root*root!=delta or (residual-root)%2:continue
                y,z=(residual-root)//2,(residual+root)//2
                if x<=y<=z<=n and (tasks>1 or y==0):
                    candidates.add((x,y,z)[3-tasks:])
    return sorted(candidates)

def summarize(records):
    if not records or len({r[0] for r in records})!=len(records):
        raise ValueError('Missing or duplicate problem identifiers')
    ns={n for _,n,_ in records}
    if len(ns)!=1:raise ValueError('Mixed sample sizes')
    n,=ns
    if n<3:raise ValueError('Too few attempts')
    groups=[];lookups={};reachable=1
    for i in range(0,len(records),3):
        block=records[i:i+3];t=len(block);observed=tuple(sorted(loss for _,_,loss in block))
        numerators=[sum(comb(x,k) for x in observed) for k in (1,2,3)]
        labels=tuple(display(numerators[k-1],t*comb(n,k)) for k in (1,2))
        if t not in lookups:
            lookup=defaultdict(list)
            for a in combinations_with_replacement(range(n+1),t):
                key=tuple(display(sum(comb(x,k) for x in a),t*comb(n,k)) for k in (1,2))
                lookup[key].append(a)
            lookups[t]=lookup
        possible=inverse(n,t,labels)
        assert possible==lookups[t][labels] and observed in possible
        loss3=sorted({sum(comb(x,3) for x in a) for a in possible})
        result=0
        for s in loss3:result|=reachable<<s
        reachable=result
        groups.append(dict(tasks=[r[0] for r in block],failures_sorted=observed,
                           input_tenths_percent=labels,possible_histograms=possible,possible_third_counts=loss3))
    total=len(records)*comb(n,3)
    smallest=(reachable & -reachable).bit_length()-1
    largest=reachable.bit_length()-1
    third=sum(comb(x,3) for _,_,x in records)
    assert (reachable>>third)&1
    observed_pct=100*Fraction(total-third,total)
    return dict(n=n,tasks=len(records),block_count=len(groups),unique_histogram_blocks=sum(len(g['possible_histograms'])==1 for g in groups),
                unique_third_blocks=sum(len(g['possible_third_counts'])==1 for g in groups),
                total_triples=total,observed_failing_triples=third,observed_pass3_percent=str(observed_pct),
                minimum_pass3_percent=str(100*Fraction(total-largest,total)),
                maximum_pass3_percent=str(100*Fraction(total-smallest,total)),
                distinct_global_counts=reachable.bit_count(),holes_within_global_interval=largest-smallest+1-reachable.bit_count(),
                attainable_failures_bitmap_hex=hex(reachable>>smallest),bitmap_origin=smallest,
                groups=groups)

def sliding_audit(losses,n):
    """Invert labelled rolling triples, given only their displayed pass@1 scores."""
    labels=[display(sum(losses[i:i+3]),3*n) for i in range(len(losses)-2)]
    bins=[counts_in_bin(label,3*n) for label in labels]
    if any(len(b)!=1 for b in bins):
        return dict(identified_single_window_sums=False)
    sums=[b[0] for b in bins]
    offsets=[0,0,0]
    for i in range(len(sums)-1):
        offsets.append(offsets[i]+sums[i+1]-sums[i])
    bounds=[(-min(offsets[r::3]),n-max(offsets[r::3])) for r in range(3)]
    starts=[]
    bounds0,bounds1,bounds2=bounds
    for x in range(bounds0[0],bounds0[1]+1):
        for y in range(bounds1[0],bounds1[1]+1):
            z=sums[0]-x-y
            if bounds2[0]<=z<=bounds2[1]:starts.append((x,y,z))
    assert tuple(losses[:3]) in starts
    fixed=sum(len({s[i%3] for s in starts})==1 for i in range(len(losses)))
    for start in starts:
        counts=[start[i%3]+delta for i,delta in enumerate(offsets)]
        assert labels==[display(sum(counts[i:i+3]),3*n) for i in range(len(counts)-2)]
    return dict(identified_single_window_sums=True,compatible_labelled_vectors=len(starts),
                uniquely_identified_tasks=fixed,residue_start_bounds=bounds,starts=starts)

def audit():
    import pyarrow.parquet as pq
    with urlopen(URL,timeout=90) as response:raw=response.read()
    assert hashlib.sha256(raw).hexdigest()==DIGEST
    table=pq.read_table(io.BytesIO(raw),columns=['experiment','problem','top_p','max_tokens','statuses','exit_codes','language'])
    settings=set();records=[]
    for row in table.to_pylist():
        settings.add((row['experiment'],row['top_p'],row['max_tokens'],row['language']))
        status,exits=row['statuses'],row['exit_codes']
        assert len(status)==len(exits)>0 and all(x is not None for x in status+exits)
        failures=sum(not (condition=='OK' and code==0) for condition,code in zip(status,exits))
        records.append((row['problem'],len(status),failures))
    assert len(settings)==1
    experiment,top_p,max_tokens,language=settings.pop()
    records.sort()
    result=summarize(records)
    result["rolling"]=sliding_audit([losses for _,_,losses in records],result["n"])
    result.update(source_sha256=DIGEST,url=URL,experiment=experiment,temperature_in_filename=0.2,top_p=top_p,max_tokens=max_tokens,language=language,
                  rounding='nearest 0.1 percentage point with half ties rounded upward',grouping='lexicographic problem ID, consecutive triples, all rows included')
    return result

if __name__=='__main__':
    print(json.dumps(audit(),indent=2))
