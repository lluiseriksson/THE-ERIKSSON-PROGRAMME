"""Exact arithmetic for the published aggregate margins, without model fitting."""
from fractions import Fraction as F
from math import comb
from itertools import combinations
from pathlib import Path
from zipfile import ZipFile, ZIP_DEFLATED
import json, hashlib


def pvalue(b,d):
    if b+d==0:
        return F(1)
    return min(F(1), F(2*sum(comb(b+d,i) for i in range(min(b,d)+1)),2**(b+d)))


def matches(rate,n):
    target=F(rate)
    scale=10**len(rate.split('.')[1])
    # Only integers in the rounding interval can qualify, including ties.
    k=int(n*target)
    return [v for v in (k,k+1) if 0<=v<=n and abs(F(v,n)-target)<=F(1,2*scale)]


def limits(x,y,n):
    return [pvalue(x-a,y-a) for a in range(max(0,x+y-n),min(x,y)+1)]


def main():
    a,b='0.918032787','0.909836066'
    sols={n:[matches(a,n),matches(b,n)] for n in range(1,881) if matches(a,n) and matches(b,n)}
    assert set(sols)==set(range(122,881,122))
    assert sols[122]==[[112],[111]]
    for n,(xx,yy) in sols.items():
        m=n//122
        assert min(limits(xx[0],yy[0],n)) == F(1,2**(m-1))
    assert set(limits(112,111,122))=={1}
    rates=['0.9426','0.9344','0.9344','0.9262','0.9262','0.918','0.918','0.9098','0.9016','0.8934','0.8852','0.7787']
    names=['SVM','GB','LightGBM','DT','XGBoost','ET','RF','LogR','MLP','AdaBoost','NB','KNN']
    counts={}
    for model,rate in zip(names,rates):
        count,=matches(rate,122)
        counts[model]=count
    pairs={}
    for left,right in combinations(counts,2):
        pp=limits(counts[left],counts[right],122)
        pairs[left+' vs '+right]=dict(p_min=str(min(pp)),p_max=str(max(pp)),
            always_bonferroni_all=max(pp)<=F(1,20*66),
            always_bonferroni_top=(left=='SVM' and max(pp)<=F(1,20*11)))
    data=dict(denominators=sols,common_N=122,resampler_tables=11,resampler_exact_p=1,
              correct_counts=counts,pairs=pairs,always_bonferroni_top=[k for k,v in pairs.items() if v['always_bonferroni_top']],
              always_bonferroni_all=[k for k,v in pairs.items() if v['always_bonferroni_all']])
    path=Path('/content/archive.zip')
    with ZipFile(path,'w',ZIP_DEFLATED) as z:z.writestr('counts.json',json.dumps(data,indent=2))
    print('archive_sha256',hashlib.sha256(path.read_bytes()).hexdigest())


if __name__=='__main__':
    main()
