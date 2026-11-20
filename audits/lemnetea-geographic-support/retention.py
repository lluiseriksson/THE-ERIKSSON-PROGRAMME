"""Exact deletion guarantees for fixed labels from Table 1."""
import json
from itertools import accumulate, combinations
from pathlib import Path

def deletion_bound(sizes, budget, minimum):
    # An association loses the threshold after at least n - minimum + 1 deletions.
    costs = sorted(max(0, n - minimum + 1) for n in sizes)
    return len(costs) - sum(total <= budget for total in accumulate(costs))

def verify(data):
    counts = list(data['resampled'].values())
    if sum(counts) != 5481 or len(counts) != 15 or len(data['witnesses']) != 15:
        raise ValueError('Recognized association totals differ')
    output = {}
    for cap in [40,80,120]:
        budget = data['provisional_strata'] * cap
        table = {str(t):deletion_bound(counts,budget,t) for t in [1,20,50,100]}
        # Independent subset enumeration, limited to fifteen categories.
        for t in [1,20,50,100]:
            costs = [max(0, n-t+1) for n in counts]
            max_lost = max(k for k in range(16) if any(
                sum(v) <= budget for v in combinations(costs,k)))
            if 15-max_lost != table[str(t)]: raise ValueError('Certificate differs')
        output[cap] = dict(budget=budget,retained_plots=sum(counts)-budget,retained_categories=table)
    if [output[k]['retained_categories']['1'] for k in [40,80,120]] != [10,8,5]:
        raise ValueError('Unexpected one-observation bound')
    return output

if __name__ == '__main__':
    print(json.dumps(verify(json.loads(Path(__file__).with_name('plot-support.json').read_bytes())),sort_keys=True,indent=2))

