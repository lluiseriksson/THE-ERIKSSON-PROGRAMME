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
def crosscheck():
    import ast,random
    method_url="https://raw.githubusercontent.com/SJSU-CMPE259/AI-Stock-Research-and-Earnings-Assistant/bcd455d5f40d2117381ee6326b18a75e8466b704/ACSESS/finsight/experiments/provenance_verification/scripts/finrank_value_corruption.py"
    with urlopen(method_url,timeout=60) as f:method=f.read()
    if sha256(method).hexdigest()!="b6594aeb2d414946c533e214251c44217fc405f9f82bdb35c123d07fd21b0abf":raise ValueError("method changed")
    subset=[t for t in ast.parse(method).body if isinstance(t,ast.FunctionDef) and t.name in {"sig_pairs","norm","to_f","window","build_item"}]
    if len(subset)!=5:raise ValueError('unexpected method')
    ns={'_SIG':pattern,'random':random.Random(0)}
    exec(compile(ast.Module(body=subset,type_ignores=[]),'<pinned pure data preparation>','exec'),ns)
    with urlopen(url,timeout=90) as f:raw=f.read()
    if sha1(f"blob {len(raw)}\0".encode()+raw).hexdigest()!=blob:raise ValueError('data changed')
    rows=[json.loads(l) for l in raw.splitlines()];ours=Random(0);ours.shuffle(rows)
    native_rows=[json.loads(l) for l in raw.splitlines()];ns['random'].shuffle(native_rows)
    counts=Counter();digest=sha256()
    for row,up in zip(rows,native_rows):
        if row!=up:raise ValueError('shuffle')
        counts['all']+=1
        if not row.get('passages') or not list(figures(row.get('answer',''))):continue
        counts['with_passage_and_answer_number']+=1
        g='\n\n'.join(p['text'] for p in row['passages']).replace(',','')
        counts['answer_number_anywhere_in_gold']+=any(v in g for v,_ in figures(row['answer']))
        case=original(row);their=ns['build_item'](up)
        if case is None:
            if their is not None:raise ValueError('initial exclusion differs')
            continue
        counts['before_replacement_validation']+=1
        ctx,raw_fig,target=case;factor=ours.choice((1.18,1.27,.82,.73));value=round(float(target)*factor,2 if '.' in target else 0)
        cs=f'{value:.2f}' if '.' in target else str(int(value))
        mutated=ctx.replace(raw_fig,cs,1)
        if cs not in mutated.replace(',',''):
            if their is not None:raise ValueError('final exclusion differs')
            counts['failed_replacement_validation']+=1;continue
        if their is None:raise ValueError('final inclusion differs')
        if (ctx,target,mutated,cs)!=(their['ctx'],their['target'],their['corrupt_ctx'],their['cstr']):raise ValueError('pair differs')
        counts['prepared']+=1;digest.update(json.dumps([ctx,their['corrupt_ctx'],target],ensure_ascii=False).encode()+b'\n')
    print(json.dumps(dict(counts=counts,ordered_prepared_sha256=digest.hexdigest(),model_calls=0),sort_keys=True))
if __name__=='__main__':crosscheck()