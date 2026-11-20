"""Exact conditional inspection costs on pinned public EvalPerf correctness banks."""
import hashlib
import json
import sys
from fractions import Fraction
from itertools import permutations, product
from pathlib import Path
from urllib.request import Request, urlopen
from zipfile import ZipFile, ZIP_DEFLATED

PIN="87418456d3a8c2bc6265f24ff91d2dd0e7993f4b"
TARGET="Qwen--CodeQwen1.5-7B-Chat"
PROXY="01-ai--Yi-Coder-9B-Chat"
SUFFIX="_temp_1.0_evalperf_results.brief.json"
def get(url,limit):
    req=Request(url,headers={"User-Agent":"ErikssonProgramme-EvalPerf-audit"})
    with urlopen(req,timeout=40) as r:
        data=r.read(limit+1)
    if len(data)>limit:raise ValueError("Resource limit")
    return data

def family(model):
    s=model.lower()
    for k,f in [('llama','llama'),('qwen','qwen'),('qwq','qwen'),('deepseek','deepseek'),
                ('gpt-','openai'),('o1-','openai'),('claude','anthropic'),('gemini','gemini'),
                ('mistral','mistral'),('codestral','mistral'),('gemma','gemma')]:
        if k in s:return f
    return s.split('--')[0]

def inputs():
    root='https://api.github.com/repos/evalplus/evalplus.github.io/contents/results/evalperf?ref='+PIN
    manifest=json.loads(get(root,1000000))
    banks={};refs={};excluded={}
    for item in sorted(manifest,key=lambda it:it['name']):
        name=item['name']
        if not name.endswith(SUFFIX):
            excluded[name]='outside standard temperature-1 individual release naming rule'
            continue
        model=name[:-len(SUFFIX)].rsplit('_',1)[0]
        data=get('https://raw.githubusercontent.com/evalplus/evalplus.github.io/'+PIN+'/'+item['path'],4000000)
        digest=hashlib.sha256(data).hexdigest()
        if hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()!=item['sha']:
            raise ValueError('Git blob mismatch')
        obj=json.loads(data,parse_float=Fraction)
        if obj['config']['n_samples']!=100 or Fraction(str(obj['config']['temperature']))!=1 or len(obj['eval'])!=118:
            excluded[name]='different config or task count'
            continue
        counts={task:r.get('pass@1') for task,r in obj['eval'].items()}
        if any(v is None or Fraction(v).denominator!=1 or not 0<=v<=100 for v in counts.values()):
            excluded[name]='unavailable or incompatible correctness rate'
            continue
        if model in banks:raise ValueError("Duplicate model key "+model)
        banks[model]={k:int(v) for k,v in counts.items()}
        refs[model]=dict(path=item['path'],sha256=digest,blob=item['sha'],family=family(model))
    if refs[TARGET]['sha256']!='b42c8e5b5d5bcbd82db388653590e0376604eabf6ba36db26ad65fa96ebdf854':raise ValueError("Target digest mismatch")
    for name in list(banks):
        if banks[name].keys()!=banks[TARGET].keys():
            excluded[refs[name]['path']]='task IDs differ'
            del banks[name],refs[name]
    return banks,refs,excluded

def mass(row,lo,hi):
    return sum(row[max(lo,0):max(hi+1,0)])

def cost(counts,d):
    m=len(counts)
    block_den=d*(d-1)
    weights=[1]; den=1
    result=Fraction()
    for b,c in enumerate(counts):
        q=d-c
        # Before checking the next slot, both outcomes remain attainable.
        result+=Fraction(mass(weights,2*b-m,m-1),den)
        lower=2*b+1-m
        odd=q*mass(weights,lower,m-1)+c*mass(weights,lower-1,m-2)
        result+=Fraction(odd,den*d)
        nxt=[0]*(len(weights)+2)
        for j,v in enumerate((q*(q-1),2*q*c,c*(c-1))):
            for i,x in enumerate(weights):nxt[i+j]+=v*x
        weights=nxt
        den*=block_den
    if sum(weights)!=den:raise ValueError('mass')
    shuffled=sum(Fraction(x*(2*m+1)*(m if h>=m else m+1),h+1 if h>=m else 2*m-h+1)
                 for h,x in enumerate(weights))/den
    return result,shuffled,Fraction(sum(weights[:m]),den)

def brute(counts,d):
    total=0;m=len(counts);pairs=list(permutations(range(d),2))
    for draws in product(pairs,repeat=m):
        bits=[x<c for pair,c in zip(draws,counts) for x in pair]
        hits=0
        for k,hit in enumerate(bits,1):
            hits+=hit
            if hits==m or k-hits==m+1:break
        total+=k
    return Fraction(total,len(pairs)**m)

def compare(target,prior):
    ids=sorted(target)
    orders=dict(desc=sorted(ids,key=lambda x:(-prior[x],x)),asc=sorted(ids,key=lambda x:(prior[x],x)),lex=ids)
    output={};ref=None
    for key,order in orders.items():
        value,rand,miss=cost([target[k] for k in order],100)
        if ref is not None and (rand,miss)!=ref:raise ValueError('ordering changed full law')
        ref=rand,miss
        output[key]=str(value)
    output.update(shuffled=str(rand),miss=str(miss),desc_order=orders['desc'])
    return output

def main():
    tests=0
    for cs in product(range(4),repeat=3):
        if cost(cs,3)[0]!=brute(cs,3):raise ValueError(('small panel',cs))
        tests+=1
    banks,refs,excluded=inputs()
    primary=compare(banks[TARGET],banks[PROXY])
    allrows={}
    for name,target in banks.items():
        peers=sorted(k for k in banks if refs[k]['family']!=refs[name]['family'])
        if not peers:raise ValueError('empty proxy set')
        prior={task:sum(banks[k][task] for k in peers) for task in target}
        allrows[name]=dict(peers=peers,**compare(target,prior))
    report=dict(revision=PIN,source=refs,excluded=excluded,counts=banks,tests=tests,primary=primary,targets=allrows)
    out=Path('/content/archive.zip')
    with ZipFile(out,'w',ZIP_DEFLATED) as z:z.writestr('order.json',json.dumps(report,sort_keys=True))
    print('archive_sha256',hashlib.sha256(out.read_bytes()).hexdigest())
if __name__=='__main__':main()

