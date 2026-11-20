"""Certify EPI dispersion signs using rational interval bounds for rounded Table 6."""
from fractions import Fraction as F
from itertools import combinations
from hashlib import sha256
from pathlib import Path
from urllib.request import urlopen
from bs4 import BeautifulSoup
import json
import zipfile

url="https://arxiv.org/html/2611.23798v1"
with urlopen(url,timeout=45) as source:
    html=source.read()
doc=BeautifulSoup(html,"html.parser")
names=["Konkan","Pune","Nashik","Nagpur","Aurangabad","Amravati"]
tables=[]
for table in doc.find_all("table"):
    rows={}
    for tr in table.find_all("tr"):
        cells=[td.get_text(" ",strip=True) for td in tr.find_all(["td","th"],recursive=False)]
        if len(cells)==7 and cells[0] in names:
            rows[cells[0]]=cells[1:]
    if set(rows)==set(names):
        tables.append(rows)
rows,=tables
eps=F(1,20000)
def stats(vals):
    n=len(vals)
    # Unbiased sample variance is the sum of pairwise squared differences / n(n-1).
    diffs=[abs(a-b) for a,b in combinations(vals,2)]
    v0=sum(max(F(0),x-2*eps)**2 for x in diffs)/ (n*(n-1))
    v1=sum((x+2*eps)**2 for x in diffs)/ (n*(n-1))
    mu=sum(vals)/n
    return (mu-eps,mu+eps),(v0,v1),(max(vals)-eps,max(vals)+eps),(min(vals)-eps,min(vals)+eps)
def bounds(stats,c,kind):
    (m,M),(v,V),(a,A),(b,B)=stats
    if kind=="CV":
        return v/(M+c)**2,V/(m+c)**2
    return (a+c)/(B+c),(A+c)/(b+c)
def sign(old,new,c,kind):
    l,h=bounds(old,c,kind)
    L,H=bounds(new,c,kind)
    return 1 if L>h else (-1 if H<l else 0)
out={}
for model,col in [("nonnegative",0),("standard",3)]:
    cols=[[rows[name][col+i] for name in names] for i in (0,1)]
    assert all(len(item.split(".")[1])==4 for column in cols for item in column)
    old,new=[stats(list(map(F,vals))) for vals in cols]
    # Guarantees a strictly increasing signed linear numerator for each metric
    # after positive denominators are cleared (CV uses standard deviations).
    assert new[1][0]>old[1][1]
    assert new[2][0]-new[3][1]>old[2][1]-old[3][0]
    summary={}
    for kind in ("CV","ratio"):
        signs=[sign(old,new,F(i,1000),kind) for i in range(1001)]
        assert signs[0]==-1 and signs[-1]==1
        before=max(i for i,v in enumerate(signs) if v==-1)
        after=min(i for i,v in enumerate(signs) if v==1)
        assert before<after
        summary[kind]=dict(negative_through_thousandths=before,positive_from_thousandths=after)
    out[model]=dict(bounds=summary,at_shift_034={kind:sign(old,new,F(34,100),kind) for kind in ("CV","ratio")})
result=dict(source=url,table=6,html_sha256=sha256(html).hexdigest(),rounding="nearest to 0.0001; closed independent boxes of radius 0.00005",grid_denominator=1000,models=out)
dest=Path("/content/archive.zip")
with zipfile.ZipFile(dest,"w",zipfile.ZIP_DEFLATED) as z:
    z.writestr("origins.json",json.dumps(result,indent=2)+"\n")
print("archive_sha256",sha256(dest.read_bytes()).hexdigest())
