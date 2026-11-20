"""Reconstruct the published FinRank sampling protocol. No model calls or filing text output."""
from hashlib import sha1,sha256
from collections import Counter
from random import Random
from urllib.request import urlopen
import json,re
commit="916dc27e77b90e294ea1b3a2cc5b0abcf07392d1"
blob="91f35ed1d19f4870771c6842f13dc944df5bd45d"
url=f"https://raw.githubusercontent.com/datanxt/FinRank/{commit}/FinRank.jsonl"
pattern=re.compile(r"\d[\d,]*\.\d+|\d[\d,]{3,}")
def figures(text):
    for raw in pattern.findall(text or ""):
        v=raw.replace(",","")
        if "." not in v and v.isdigit() and 1900<=int(v)<=2099:continue
        yield v,raw
def original(row):
    gold="\n\n".join(x["text"] for x in row["passages"])
    ng=gold.replace(",","")
    target=next((v for v,_ in figures(row["answer"]) if v in ng),None)
    if target is None:return
    raw=next((r for v,r in figures(gold) if v==target),target)
    i=gold.find(raw)
    ctx=gold[:2000] if i<0 else gold[max(0,i-1000):i+len(raw)+1000]
    if target not in ctx.replace(",","") or float(target)==0:return
    return ctx,raw,target
def possible_numeric_substrings(text):
    # Superset of normalized strings emitted by the answer's regex. Including
    # filtered years and unconstrained short integers can only enlarge it.
    for run in re.findall(r"[\d.]+",text):
        for i in range(len(run)):
            for j in range(i+1,len(run)+1):
                v=run[i:j]
                if re.fullmatch(r"\d+(?:\.\d+)?",v):yield v
def status(case,factor):
    ctx,raw,target=case
    tf=float(target);cf=round(tf*factor,2 if "." in target else 0)
    cs=f"{cf:.2f}" if "." in target else str(int(cf))
    G=ctx.replace(",","");R=ctx.replace(raw,cs,1).replace(",","")
    if cs not in R:return
    # Exhaustive for numeric correctness in a B-pass, C-flag response.
    candidates={v for v in possible_numeric_substrings(R) if v not in G and abs(float(v)-tf)<1e-6}
    return dict(alias=bool(candidates),literal_target_survives=target in R,
                literal_corrupt_in_original=cs in G,unmodified=G==R)
def allowed(case,factor):
    ctx,raw,target=case
    tf=float(target);cf=round(tf*factor,2 if "." in target else 0)
    cs=f"{cf:.2f}" if "." in target else str(int(cf))
    G=ctx.replace(",","");R=ctx.replace(raw,cs,1).replace(",","")
    if cs not in R:return
    edges={(0,0,0)} # both flagged: an answer without a figure suffices for these metrics
    canonical={(0,0,0)}
    for v in set(possible_numeric_substrings(R)):
        if v.isdigit() and 1900<=int(v)<=2099:continue
        is_error=int(abs(float(v)-tf)>=1e-6)
        edge=(0,1,is_error) if v in G else (1,0,is_error)
        edges.add(edge)
        if "." in v or len(v)>=4:canonical.add(edge)
    return edges,canonical
def identified(panels,extras,common):
    ans={}
    for mode in ('gain','silent_C','silent_B'):
        dp={(0,0):1}
        for edges in panels:
            nd={}
            for (x,y),bits in dp.items():
                for dx,dy,wrong in edges:
                    if x+dx>extras or y+dy>common:continue
                    shift={'gain':dx,'silent_C':dy,'silent_B':dx+dy}[mode]*wrong
                    key=x+dx,y+dy;nd[key]=nd.get(key,0) | bits<<shift
            dp=nd
        bits=dp.get((extras,common),0);ans[mode]=[j for j in range(len(panels)+1) if bits>>j&1]
    return ans
def analyze():
    with urlopen(url,timeout=90) as f:raw=f.read()
    if sha1(f"blob {len(raw)}\0".encode()+raw).hexdigest()!=blob:raise ValueError("FinRank blob")
    rows=[json.loads(l) for l in raw.splitlines()];rng=Random(0);rng.shuffle(rows)
    panel=[]
    for row in rows:
        if not row.get('passages'):continue
        case=original(row)
        if case is None:continue
        result=allowed(case,rng.choice((1.18,1.27,.82,.73)))
        if result:panel.append(result)
        if len(panel)==60:break
    results={}
    for N,extra,common in [(60,25,14),(40,9,4)]:
        broad,natural=zip(*panel[:N])
        r=identified(broad,extra,common);inner=identified(natural,extra,common)
        results[str(N)]=dict(full=r,canonical_witnesses=inner,any_correct_common=sum((0,1,0) in x for x in broad),
                             any_correct_exclusive=sum((1,0,0) in x for x in broad),absent_reverse_flags_assumed=True)
        if not all(r.values()):raise ValueError('No placement fits published counts')
    print(json.dumps(results,sort_keys=True))
if __name__=='__main__':analyze()