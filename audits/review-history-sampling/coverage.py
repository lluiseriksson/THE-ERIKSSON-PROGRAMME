"""Reconcile Syed's public materials; export only aggregate counts."""
from collections import Counter
from fractions import Fraction as F
from pathlib import Path
from hashlib import sha256
from urllib.request import urlopen
import csv,io,json,zipfile
sources={"raw":("pwevq","474bc23bf2ea73a6130e0f73a57459de622301ef0b4c6246f2a6f1b2de774742"),
         "working":("9gzdb","868b4d9c253c8d889c0950a33496b52a62cb4edd565a094ada3612bb5f64da52")}
def get(k):
    key,h=sources[k]
    with urlopen("https://osf.io/download/"+key+"/",timeout=45) as s:raw=s.read()
    if sha256(raw).hexdigest()!=h:raise ValueError("wrong data")
    return list(csv.DictReader(io.StringIO(raw.removeprefix(bytes.fromhex("efbbbf")).decode("latin-1"),newline="")))
from math import comb
from itertools import combinations
raw=get("raw");w={r["Key"]:r for r in get("working")}
rows=[r for r in raw if r["Review_History"]=="Y" and r["Empirical"]=="Y" and r["Preregd"]=="Y" and r["Registered_Report"]=="N"]
if len(rows)!=201 or len(w)!=len(rows) or {r["Key"] for r in rows}!=set(w):raise ValueError("population")
def u(n,y,k):
    k=min(n,k)
    return 1-F(comb(n-y,k),comb(n,k))
def policies(n,y,e,k):
    return u(n,y,k), F(1) if e else u(n-1,y,k-1)
distribution=Counter()
for row in rows:
    roles=["Ed"]+[s for s in ["R"+str(i) for i in range(1,7)] if row["Prereg_Mention_"+s] in ("Y","N")]
    hits={s for s in roles if row["Prereg_Relation_"+s]=="Y"}
    if int(w[row["Key"]]["Num_Eyes"])!=len(roles) or any((w[row["Key"]]["Prereg_Relation_"+s]=="Y")!=(s in hits) for s in roles):raise ValueError("working data")
    key=len(roles),len(hits),int("Ed" in hits)
    distribution[key]+=1
    for k in range(1,8):
        pairs=list(combinations(roles,min(len(roles),k)));fixed=[s for s in pairs if "Ed" in s]
        direct=[F(sum(bool(hits.intersection(s)) for s in sets),len(sets)) for sets in [pairs,fixed]]
        if tuple(direct)!=policies(*key,k):raise ValueError("failed enumeration")
curves={}
for k in range(1,8):
    uniform=fixed=F(0);winning=Counter()
    for g,count in distribution.items():
        a,b=policies(*g,k);uniform+=a*count;fixed+=b*count
        winning[(b>a)-(b<a)]+=count
    curves[k]=dict(uniform=uniform/201,include_editor=fixed/201,difference=(fixed-uniform)/201,articles=dict(winning))
delta=curves[2]["difference"]*201
direction=1 if delta>0 else -1
gains=[]
for (n,y,e),m in distribution.items():
    a,b=policies(n,y,e,2)
    best=max(direction*(b-a-(v-u0)) for e2 in (0,1) for z in range(n) for u0,v in [policies(n,z+e2,e2,2)])
    gains.extend([best]*m)
gains.sort(reverse=True)
rem=abs(delta);first_tie=0 if not delta else None;first_reverse=None;prefix_gains=[F(0)]
for i,v in enumerate(gains,1):
    rem-=v
    prefix_gains.append(abs(delta)-rem)
    if rem<=0 and first_tie is None:first_tie=i
    if rem<0:first_reverse=i;break
result=dict(source=sources,counts=[[n,y,e,c] for (n,y,e),c in sorted(distribution.items())],curves=curves,
            crosschecks=len(rows)*7,primary_signed_total=delta,minimum_to_erase=first_tie,minimum_to_reverse=first_reverse,largest_gains_partial=prefix_gains)
dest=Path("/content/archive.zip")
with zipfile.ZipFile(dest,"w",zipfile.ZIP_DEFLATED) as z:z.writestr("coverage.json",json.dumps(result,default=str,indent=2)+"\n")
print("archive_sha256",sha256(dest.read_bytes()).hexdigest())
