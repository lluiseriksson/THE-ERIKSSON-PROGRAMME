"""Finite-population coding sensitivity of industrial maturity, conditional on the published rater observations."""
from pathlib import Path
from urllib.request import urlopen
from urllib.parse import quote
from io import BytesIO
from collections import Counter,defaultdict
import hashlib,json,openpyxl
m=json.loads(Path('fuente.json').read_bytes());f,=[x for x in m['files'] if x['key'].endswith('.xlsx')]
with urlopen('https://zenodo.org/api/records/24095165/files/'+quote(f['key'])+'/content',timeout=30) as r:raw=r.read(f['size']+1)
assert len(raw)==f['size'] and 'md5:'+hashlib.md5(raw).hexdigest()==f['checksum']
book=openpyxl.load_workbook(BytesIO(raw),data_only=True,read_only=True)
def data(name):
    it=iter(book[name].values);header=next(it)
    return [dict(zip(header,row)) for row in it if row[0] is not None]
def uid(x):return str(x).strip()
p=[r for r in data('Coding (188 studies)') if r['Study type']=='Primary']
a=data('Human audit (60)');pm={uid(r['ID']):r['Maturity'] for r in p};am={uid(r['ID (UID)']):r for r in a}
assert len(pm)==len(p)==160 and len(am)==len(a)==60 and set(am)<=set(pm)
levels={'Industrial pilot','Operational deployment'}
names=set(pm.values())|{r['Maturity (rater)'] for r in a}
assert None not in names
flags={k:int(v in levels) for k,v in pm.items()};rater={k:int(v['Maturity (rater)'] in levels) for k,v in am.items()}
other=sorted(set(pm)-set(am))
from fractions import Fraction
from math import comb
from itertools import product
g=defaultdict(list)
for row in a:
    g[(row['Sample'],row['Stratum (coding before the audit)'])].append(row)
hi=lambda r:r['Maturity (rater)'] in levels
table=[dict(sample=k[0],stratum=k[1],n=len(v),high=sum(map(hi,v)),weights=sorted({str(x['Sampling weight (sample A)']) for x in v})) for k,v in g.items()]
A=[v for k,v in sorted(g.items(),key=lambda zz:zz[0][1]) if k[0].startswith('A')]
def pop(v):
    wt=Fraction(str(v[0]['Sampling weight (sample A)']));n=len(v);N=round(wt*n)
    assert abs(wt-Fraction(N,n))<=Fraction(1,10000) and all(str(x['Sampling weight (sample A)'])==str(v[0]['Sampling weight (sample A)']) for x in v)
    return N,n
N1,n1=pop(A[0]);N2,n2=pop(A[1]);obs=[sum(map(hi,v)) for v in A]
w1,w2=N1*n2,N2*n1
observed=w1*obs[0]+w2*obs[1]
den=comb(N1,n1)*comb(N2,n2)
def masses(N,n,M):
    return [(x,comb(M,x)*comb(N-M,n-x)) for x in range(max(0,n-(N-M)),min(n,M)+1)]
m1=[masses(N1,n1,M) for M in range(N1+1)];m2=[masses(N2,n2,M) for M in range(N2+1)]
tails={};last={}
for i in range(N1+1):
    for j in range(N2+1):
        val=sum(v*u for x,v in m1[i] for y,u in m2[j] if w1*x+w2*y<=observed)
        if val>tails.get(i+j,-1):
            tails[i+j]=val;last[i+j]=(i,j)
assert all(tails[s]>=tails[s+1] for s in range(N1+N2))
upper=max(s for s,v in tails.items() if 20*v>den)
def pdetail(s):return dict(total=s,strata=last[s],tail=str(Fraction(tails[s],den)),decimal=tails[s]/den)
B0=[row for row in a if row['Stratum (coding before the audit)'] not in {v[0]['Stratum (coding before the audit)'] for v in A}]
# Incorporate observed labels only in strata known to have zero A inclusion.
rest=160-N1-N2
assert len(B0)<=rest
extra=sum(map(hi,B0))+rest-len(B0)
finite=dict(eligible=N1+N2,upper95_eligible=upper,upper95_all_without_using_B=upper+rest,upper95_all_if_known_outside=upper+extra,unsupported_size=rest,other_strata_observed=len(B0),positive_in_other_strata=sum(map(hi,B0)),threshold=[pdetail(upper),pdetail(upper+1)],observed=obs,design=[[N1,n1],[N2,n2]],ht=str(Fraction(N1*obs[0],n1)+Fraction(N2*obs[1],n2)))
print(json.dumps(dict(notes=data('Human audit notes'),strata=table,finite=finite),indent=2,ensure_ascii=False))
