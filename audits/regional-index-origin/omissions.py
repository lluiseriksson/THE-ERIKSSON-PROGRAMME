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
"""Sharp bounds on shifts of Lorenz ordinates from rounded division means."""
from fractions import Fraction as F
from pathlib import Path
import hashlib
import json
import zipfile


def ordinate_bounds(values,j,eps):
    vals=sorted(values)
    assert min(vals)>eps and all(b-a>2*eps for a,b in zip(vals,vals[1:]))
    # For fixed sorting, raising a bottom value increases its group's share;
    # raising a top value decreases it. Both extrema are therefore attained.
    return [(sum(vals[:j])+s*j*eps,sum(vals)+s*(2*j-len(vals))*eps) for s in (-1,1)]


def line(later,earlier,j,n):
    a,t=later
    b,v=earlier
    return (a*v-b*t, n*(a-b)+j*(v-t))


def diagnose(early,late):
    n=len(early)
    eps=F(1,20000)
    forms={}
    for j in range(1,n):
        low,high=ordinate_bounds(late,j,eps)
        oldlow,oldhigh=ordinate_bounds(early,j,eps)
        forms[j]=(line(low,oldhigh,j,n),line(high,oldlow,j,n))
    # Independent verification through all 2^12 corners at two
    # positive evaluation points; verifies numerator signs through share differences.
    from itertools import product
    for c in (F(0),F(1,3)):
        for j in forms:
            def ratios(panel):
                for signs in product((-1,1),repeat=n):
                    shifted=sorted(x+s*eps+c for x,s in zip(panel,signs))
                    yield sum(shifted[:j])/sum(shifted)
            left=list(ratios(early));right=list(ratios(late))
            lo0,hi0=ordinate_bounds(early,j,eps)
            lo1,hi1=ordinate_bounds(late,j,eps)
            val=lambda pair:(pair[0]+j*c)/(pair[1]+n*c)
            assert min(right)-max(left)==val(lo1)-val(hi0)
            assert max(right)-min(left)==val(hi1)-val(lo0)
    edges={F(0)}
    for pair in forms.values():
        for a,b in pair:
            if b and -a/b>0:edges.add(-a/b)
    edges=sorted(edges)
    def status(c):
        pos=[];neg=[]
        for j,((a,b),(A,B)) in forms.items():
            if a+b*c>0:pos.append(j)
            if A+B*c<0:neg.append(j)
        if len(pos)==n-1:return "later_above"
        if len(neg)==n-1:return "later_below"
        if pos and neg:return "crossing"
        return "uncertified"
    pieces=[]
    for i,x in enumerate(edges):
        y=edges[i+1] if i+1<len(edges) else None
        mid=(x+y)/2 if y is not None else x+1
        pieces.append(dict(left=str(x),right=str(y) if y is not None else None,
                           at_left=status(x),interior=status(mid)))
    return dict(pieces=pieces,ordinary={str(c):status(c) for c in [F(0),F(1,4),F(1,3),F(1,2),F(1)]},
                lines={str(j):[[str(a),str(b)] for a,b in pair] for j,pair in forms.items()})

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

result={}
for model,col in [("nonnegative",0),("standard",3)]:
    values={}
    for omitted in names:
        panels=[[F(rows[g][col+i]) for g in names if g!=omitted] for i in (0,1)]
        old,new=map(stats,panels)
        model_signs={kind:sign(old,new,F(1,4),kind) for kind in ("CV","ratio")}
        model_signs["lorenz"]=diagnose(*panels)["ordinary"]["1/4"]
        values[omitted]=model_signs
    result[model]=values
dest=Path("/content/archive.zip")
with zipfile.ZipFile(dest,"w",zipfile.ZIP_DEFLATED) as z:
    z.writestr("omissions.json",json.dumps(dict(models=result,html_sha256=sha256(html).hexdigest()),indent=2)+"\n")
print("archive_sha256",sha256(dest.read_bytes()).hexdigest())
