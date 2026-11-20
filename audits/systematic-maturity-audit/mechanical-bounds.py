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
adj=sum(rater.values())+sum(flags[k] for k in other)
fixed=sum(rater.values());h=sum(flags[k] for k in other);l=len(other)-h
out=dict(n=len(pm),audited=len(am),code_hist=dict(Counter(pm.values())),audited_samples=dict(Counter(r['Sample'] for r in a)),rater_hist=dict(Counter(r['Maturity (rater)'] for r in a)),diff_final_prior=sum(pm[k]!=r['Maturity (coding)'] for k,r in am.items()),unrated_labeled_high=h,unrated_labeled_other=l,baseline=adj,original=sum(flags.values()),fixed_positive=fixed,unrestricted=[fixed,fixed+len(other)],strict_majority_target=81,minimum_flips_for_majority=max(0,81-adj) if 81<=fixed+len(other) else None)
out['budget_intervals']=[[adj-min(k,h),adj+min(k,l)] for k in range(101)]
# Generate feasible counts independently, preserving the total number of original high plus other labels.
dp={(0,0)}
for i in other:dp={(k+int(c!=flags[i]),s+c) for k,s in dp for c in (0,1)}
for k,interval in enumerate(out['budget_intervals']):
    feasible={s+fixed for cost,s in dp if cost<=k};assert feasible==set(range(interval[0],interval[1]+1))
print(json.dumps(out,indent=2))
