import json
from math import comb, ceil
def threshold(pop,hidden):
    def miss_num(n):
        return comb(pop-n,hidden) if pop-n>=hidden else 0
    denominator=comb(pop,hidden)
    lo,hi=0,pop
    while hi-lo>1:
        n=(lo+hi)//2
        if 20*miss_num(n)<=denominator:hi=n
        else:lo=n
    assert 20*miss_num(hi)<=denominator<20*miss_num(hi-1)
    return dict(hidden=hidden,n=hi,miss=miss_num(hi)/denominator,miss_one_fewer=miss_num(hi-1)/denominator)
rows=[]
for B in range(1,25):
    N=2086-B
    rows.append(dict(B=B,N=N,count=threshold(N,27-B),yield_rate=threshold(N,ceil(2086*27/72)-B)))
print(json.dumps(rows,indent=2))