"""Check exact one-cost budgets against an exported two-objective design library."""
from decimal import Decimal as D
from hashlib import sha256
from pathlib import Path
from urllib.request import urlopen
import json

URL = 'https://raw.githubusercontent.com/ElhadiMohsenAbdalla/SWMMLIDOPT/a824c03d1864b02d153c81679b61e2d9125d090a/Example/MultiOpt.json'
DIGEST = '2423484a58456c597d7eea2241a650d3447e56461c1cb51e3ee77d72ea8f2321'


def solve(raw):
    if sha256(raw).hexdigest() != DIGEST:
        raise ValueError('Unexpected archived input')
    src = json.loads(raw,parse_float=D,parse_int=D)
    rows = [(cost,loss,i) for i,(cost,loss) in enumerate(src['objectives'],1)]
    if len(rows)!=len(src['parameters']) or len(rows)!=len(src['pareto']):
        raise ValueError('Misaligned design records')
    ordered=sorted(rows)
    front=[]
    for row in ordered:
        if not front or row[1]<front[-1][1]:
            front.append(row)
    # At a tied cost the least loss is first; exact ties use the smallest row id.
    distinct=set((x,y) for x,y,_ in front)
    strict_dom=[i for c,y,i in rows if any(a<=c and z<=y and (a<c or z<y) for a,z,_ in rows)]
    if set((c,y) for c,y,i in rows if i not in strict_dom)!=distinct:
        raise ValueError('Mismatch between dominance and skyline')
    y=[v[1] for v in front]
    # Prefix DP over contiguous blocks. The least-cost member of each block
    # fixes the affordable witness; its largest excess is at the final point.
    n=len(y)
    prev=[D(0)]+[D('Infinity')]*n
    options={}
    for k in range(1,min(n,10)+1):
        cur=[D(0)]+[min(max(prev[h], y[h]-y[j-1]) for h in range(j)) for j in range(1,n+1)]
        prev=cur
        if k not in (1,2,3,5,10):continue
        delta=cur[n]
        def choose(tolerance):
            indices=[]
            for i,value in enumerate(y):
                if not indices or y[indices[-1]]>value+tolerance:indices.append(i)
            return indices
        chosen=choose(delta)
        # At the exact boundary test strict comparison directly, without an epsilon.
        strict=[]
        for i,value in enumerate(y):
            if not strict or y[strict[-1]]>=value+delta:strict.append(i)
        if len(chosen)>k or (delta>0 and len(strict)<=k):
            raise ValueError('Greedy and strict lower-bound tests disagree')
        worst=max(min(front[i][1]-v for i in chosen if front[i][0]<=c) for c,v,_ in rows)
        if worst!=delta:raise ValueError('Uncovered row or unattained maximum')
        options[str(k)]=dict(excess_lps=str(delta),one_based_row_ids=[front[i][2] for i in chosen],
                             strict_witness_count=len(strict))
    return dict(input_sha256=DIGEST,rows=len(rows),unique_objective_pairs=len({v[:2] for v in rows}),
                nondominated_pairs=n,strictly_dominated_rows=strict_dom,
                flagged_dominated=[i for i in strict_dom if src['pareto'][i-1]],budgets=options)

if __name__=='__main__':
    local=Path('MultiOpt.json')
    if local.is_file():raw=local.read_bytes()
    else:
        with urlopen(URL,timeout=30) as r:raw=r.read()
    print(json.dumps(solve(raw),sort_keys=True,indent=2))

