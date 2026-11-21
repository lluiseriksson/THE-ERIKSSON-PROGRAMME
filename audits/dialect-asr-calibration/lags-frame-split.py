"""Compare all four-speaker supplements to a fixed observed pair using first reels."""
from itertools import combinations
from collections import Counter
from fractions import Fraction
from math import comb
import json,runpy
def catalogue(rows,observed):
    keys=sorted(k for k in rows if k not in observed and 'counts' in rows[k])
    if len(rows)!=64 or len(keys)<4:raise ValueError('Incomplete speaker frame')
    groups=Counter();classes={};examples={};bounds={}
    for ids in combinations(keys,4):
        counts={rule:sum(rows[k]['counts'][rule] for k in ids) for rule in rows[ids[0]]['counts']}
        if not counts['multi_letter_words']<=counts['spoken_letter_words']<=counts['all_letter_words']:raise ArithmeticError(ids)
        # Exact observed edit limits retained in gate.json for the two-speaker pooled table.
        sig=tuple('impossible' if 3*(18425+c)<20*7022 else 'possible_all_roundings' if 3*(18425+c)>=20*7029 else 'rounding_sensitive' for c in (counts['multi_letter_words'],counts['spoken_letter_words'],counts['all_letter_words']))
        classes[sig]=classes.get(sig,0)+1
        for rule,value in counts.items():
            if rule not in bounds:bounds[rule]=[value,value]
            bounds[rule]=[min(value,bounds[rule][0]),max(value,bounds[rule][1])]
        if sig not in examples:examples[sig]=dict(ids=ids,counts=counts)
    if sum(classes.values())!=comb(len(keys),4):raise ValueError('Enumeration')
    return dict(usable=len(keys),unresolved=[k for k,v in rows.items() if 'counts' not in v],designs=comb(len(keys),4),classes={'/'.join(k):v for k,v in sorted(classes.items())},examples={'/'.join(k):v for k,v in examples.items()},ranges=bounds,rule_order=['multi_letter_words','spoken_letter_words','all_letter_words'])
if __name__=='__main__':
    data=runpy.run_path('reels-frame-split.py')['main']()
    data['selection']='All 64 public DASS2019 speaker IDs, reel 1; no assertion about the original unobserved four.'
    data['summary']=catalogue(data['rows'],['025','027']);print(json.dumps(data,sort_keys=True))
