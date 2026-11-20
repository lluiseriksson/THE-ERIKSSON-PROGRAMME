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
raw=get("raw")
rows=[r for r in raw if r["Review_History"]=="Y" and r["Empirical"]=="Y" and r["Preregd"]=="Y" and r["Registered_Report"]=="N"]
working=get("working");work={r["Key"]:r for r in working}
if len(rows)!=201 or len(working)!=len(work) or {r["Key"] for r in rows}!=set(work):raise ValueError("inclusion")
pos=["Ed"]+["R"+str(i) for i in range(1,7)]
hist=Counter()
event_totals=Counter()
for r in rows:
    w=work[r["Key"]]
    present=[s for s in pos if s=="Ed" or r["Prereg_Mention_"+s] in ("Y","N")]
    hits=[s for s in pos if r["Prereg_Relation_"+s]=="Y"]
    if not set(hits)<=set(present) or len(present)!=int(w["Num_Eyes"]):raise ValueError("denominator")
    for s in pos:
        for col in ["Prereg_Mention_","Prereg_Relation_"]:
            if (r[col+s]=="Y")!=(w[col+s]=="Y"):raise ValueError("disagreement")
    event_totals.update(hits);hist[len(present),len(hits)]+=1
total=sum(n*c for (n,y),c in hist.items());events=sum(y*c for (n,y),c in hist.items())
p=F(events,total);q=sum(F(y*c,n) for (n,y),c in hist.items())/len(rows)
out=dict(sources=sources,article_count=len(rows),positions=total,events=events,by_position=event_totals,
         histogram=[[n,y,c] for (n,y),c in sorted(hist.items())],pooled=str(p),article_weighted=str(q),difference=str(q-p))
dest=Path("/content/archive.zip")
with zipfile.ZipFile(dest,"w",zipfile.ZIP_DEFLATED) as z:z.writestr("weights.json",json.dumps(out,indent=2)+"\n")
print("archive_sha256",sha256(dest.read_bytes()).hexdigest())
