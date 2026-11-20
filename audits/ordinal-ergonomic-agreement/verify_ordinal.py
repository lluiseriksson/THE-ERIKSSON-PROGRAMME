"""Recompute both general tests and check applications by a separate 3x3 enumeration."""
from collections import Counter
from pathlib import Path
from itertools import product
import json,subprocess,sys
def read(path):return json.loads(Path(path).read_bytes())
def check(b):
    if not b:raise ValueError('Certificate mismatch')
def independent(r,c,e):
    out=set()
    for i,j,k in product(range(e+1),repeat=3):
        # (i,j,k,l,m,n) = off-diagonal cells (01,02,10,12,20,21).
        m=i+j-k-(r[0]-c[0]); left=e-i-j-k-m
        diff=r[2]-c[2]+j-m
        if m<0 or left<abs(diff) or (left-diff)%2:continue
        l=(left-diff)//2;n=(left+diff)//2
        mat=[[r[0]-i-j,i,j],[k,r[1]-k-l,l],[m,n,r[2]-m-n]]
        if min(min(x) for x in mat)<0:continue
        check(list(map(sum,zip(*mat)))==c)
        out.add((i+j,j+l,k+m,m+n))
    return out
def verify():
    for code,data in [('reba-ordinal.py','ordinal.json'),('reba-margins.py','paired.json')]:
        check(json.loads(subprocess.check_output([sys.executable,code]))==read(data))
    cases=read('paired.json')['tables'];out={}
    for v in cases:
        p=independent(v['expert_rows'],v['system_cols'],v['discordant'])
        check(len(p)==v['possible_directed_profiles'])
        check(tuple(v['observed_up']+v['observed_down']) in p)
        check([[min(z[i] for z in p),max(z[i] for z in p)] for i in (2,3)]==v['down_ranges'])
        check(sorted({z[3] for z in p if z[2]==v['observed_down'][0]})==v['high_down_given_observed_low'])
        out[v['name']]=dict(profiles=len(p),high_down=sorted({x[3] for x in p}),given_low=v['high_down_given_observed_low'])
    print(json.dumps(out,sort_keys=True))
if __name__=='__main__':verify()
