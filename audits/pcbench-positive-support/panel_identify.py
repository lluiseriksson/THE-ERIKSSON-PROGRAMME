"""Conditional top-k null using only published aggregate tables."""
from fractions import Fraction as F
from math import comb
from collections import Counter,defaultdict
import csv,json
from scipy.stats import hypergeom

def rows(name):return list(csv.DictReader(open(name,encoding='utf-8-sig')))
def key(r):return '|'.join(r[k] for k in ['cancer','model','protocol','config'])
def tail(N,H,K,r):
    denom=comb(N,K)
    return sum(F(comb(H,j)*comb(N-H,K-j),denom) for j in range(max(r,K-(N-H),0),min(H,K)+1))
panels=defaultdict(list)
for r in rows('bench_panel_genes.csv'):panels[key(r)].append(r)
result={}
for row in rows('bench_summary.csv'):
    k=key(row);assert k not in result
    G,H0,K,rec=[int(row[n]) for n in ['n_genes','panel_size']]+[50,int(row['recovery_top50'])]
    panel=panels[k];positive=[int(r['rank']) for r in panel if F(r['selected_frac'])>0];zero=[int(r['rank']) for r in panel if F(r['selected_frac'])==0]
    H=len(positive);assert len(panel)==len({r['gene'] for r in panel})==H0 and len(zero)==int(row['panel_never_selected'])
    assert len(set(positive+zero))==H0 and len([i for i in positive+zero if i<=K])==rec
    lo=max(positive,default=0);hi=min(zero,default=G+1)-1
    assert 0<=lo<=hi<=G
    full=tail(G,H0,K,rec)
    assert abs(float(full)-float(row['p_hyper']))<1e-10
    v={'G':G,'panel':H0,'positive_controls':H,'observed':rec,'size_lower':lo,'size_upper':hi,'p_full':float(full)}
    rpos=sum(i<=K for i in positive)
    lower=max(1,lo,H)
    # M=0 is feasible from rank information only if H=0; then the tail is one as at M=1.
    def support_tail(N):
        return tail(N,H,min(K,N),rpos)
    p1,p2=support_tail(hi),support_tail(lower)
    assert 0<=p1<=p2<=1
    for N,val in [(lower,p2),(hi,p1)]:
        assert abs(float(val)-float(hypergeom.sf(rpos-1,N,H,min(K,N))))<1e-10
    alpha=F(1,20)
    v.update(positive_hits=rpos,p_min=float(p1),p_max=float(p2),classification='always_below' if p2<alpha else 'always_at_or_above' if p1>=alpha else 'straddles',full_below=full<alpha)
    result[k]=v
assert set(result)==set(panels)
print(json.dumps({'rows':result,'counts':dict(Counter(r['classification'] for r in result.values())),'crosstab':dict(Counter(str(r.get('full_below'))+'|'+r['classification'] for r in result.values()))},sort_keys=True))
