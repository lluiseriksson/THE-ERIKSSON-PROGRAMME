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
def main():
    with urlopen(url,timeout=90) as f:raw=f.read()
    if sha1(f"blob {len(raw)}\0".encode()+raw).hexdigest()!=blob:raise ValueError("FinRank blob")
    rows=[json.loads(l) for l in raw.splitlines()];rng=Random(0);rng.shuffle(rows)
    fs=(1.18,1.27,.82,.73);selected=[];whole=Counter();all_factor=Counter()
    for row in rows:
        if not row.get("passages"):continue
        case=original(row)
        if case is None:continue
        draw=rng.choice(fs);outcomes={t:status(case,t) for t in fs}
        admissible=[x for x in outcomes.values() if x is not None]
        whole['eligible_for_any_factor']+=bool(admissible)
        whole['rows_with_some_alias']+=any(x['alias'] for x in admissible)
        for a in admissible:
            all_factor.update({k:int(v) for k,v in a.items()});all_factor['valid_item_factors']+=1
        s=outcomes[draw]
        if s is not None:selected.append(s)
    def counts(panel):
        return {k:sum(r[k] for r in panel) for k in selected[0]}
    print(json.dumps(dict(dataset_commit=commit,blob=blob,sha256=sha256(raw).hexdigest(),dataset_rows=len(rows),
       valid_seeded=len(selected),all_rows=whole,all_factors=all_factor,panel60=counts(selected[:60]),
       panel40=counts(selected[:40]),seeded_full=counts(selected)),sort_keys=True))
if __name__=='__main__':main()