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

from itertools import product
models={}
names=[g for g in names if g!="Amravati"]
old,new=[[F(rows[g][j]) for g in names] for j in (0,1)]
c=F(1,4)
delta=F(49999,1000000000)  # strictly less than half a last digit
def shares(vec):
    shifted=sorted(x+c for x in vec)
    return [sum(shifted[:j])/sum(shifted) for j in range(1,len(vec))]
def panel(vec):
    for s in product((-1,1),repeat=len(vec)):
        vals=[x+a*delta for x,a in zip(vec,s)]
        yield s,shares(vals)
visited=0
for (s,x),(t,y) in product(panel(old),panel(new)):
    visited+=1
    gaps=[b-a for a,b in zip(x,y)]
    if min(gaps)>0:kind="later_above"
    elif max(gaps)<0:kind="later_below"
    elif min(gaps)<0<max(gaps):kind="crossing"
    else:kind="equality_at_knot"
    if kind not in models:
        models[kind]=dict(old_signs=s,new_signs=t,gaps=[str(z) for z in gaps])
out=dict(source=url,html_sha256=sha256(html).hexdigest(),remaining=names,shift=str(c),
         perturbation=str(delta),cases_visited=visited,witnesses=models)
dest=Path("/content/archive.zip")
with zipfile.ZipFile(dest,"w",zipfile.ZIP_DEFLATED) as z:
    z.writestr("amravati.json",json.dumps(out,indent=2)+"\n")
print("archive_sha256",sha256(dest.read_bytes()).hexdigest())
