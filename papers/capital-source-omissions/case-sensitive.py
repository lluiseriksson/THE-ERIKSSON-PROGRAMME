from pathlib import Path
from collections import Counter, defaultdict
from urllib.parse import urlsplit
import hashlib,json,re,unicodedata,urllib.request,zipfile
import pyarrow.parquet as pq

pin='e737b94a38cf77b2ec3a29cb1c6bd756fb1329fb'
url='https://huggingface.co/datasets/sarahcen/ai-supply-chain/resolve/'+pin+'/data/gsearch_relationship_results.parquet'
path=Path('/content/data.parquet')
with urllib.request.urlopen(url,timeout=90) as src,path.open('xb') as out:
    while block:=src.read(1048576):out.write(block)
source_sha=hashlib.sha256(path.read_bytes()).hexdigest()
columns='document_date ai_stack_layers relationship_type relationship_status evidence_strength actor_1_type actor_2_type directionality actor_1_name actor_2_name link'.split()
modes={key:defaultdict(set) for key in ('trim','fold')}
stats=Counter()
for batch in pq.ParquetFile(path).iter_batches(columns=columns,batch_size=2048):
    for r in batch.to_pylist():
        stats['input']+=1
        date=str(r['document_date'])[:10]
        layers=r['ai_stack_layers']
        if isinstance(layers,str):
            if layers.startswith('['):layers=json.loads(layers)
            else:layers=[layers]
        if not ('2022-11-01'<=date<='2026-10-31' and 'CAPITAL' in (layers or []) and r['actor_1_type']==r['actor_2_type']=='COMPANY' and r['relationship_status']=='ESTABLISHED' and r['relationship_type']=='INVESTMENT' and r['evidence_strength']=='EXPLICIT' and r['directionality'] in ('ACTOR_1_TO_ACTOR_2','ACTOR_2_TO_ACTOR_1')):continue
        stats['eligible']+=1
        link=urlsplit(r['link'] or '')
        host=(link.hostname or '').lower().removeprefix('www.')
        if not host or link.scheme.lower() not in ('http','https'):continue
        a,b=[(r[key] or '').strip() for key in ('actor_1_name','actor_2_name')]
        if not a or not b:continue
        if r['directionality']=='ACTOR_2_TO_ACTOR_1':a,b=b,a
        for key,graph in modes.items():
            norm=lambda s:' '.join(unicodedata.normalize('NFKC',s).casefold().split()) if key=='fold' else s
            x,y=norm(a),norm(b)
            if x!=y:graph[x,y].add(host)
out={}
def leaders(degree):
    top=max(degree.values())
    return sorted(k for k,v in degree.items() if v==top)
for key,g in modes.items():
    if not g:raise ValueError('No directed documented ties in '+key+' '+str(stats))
    deg=Counter(a for a,b in g)
    hosts=sorted(set.union(*g.values()))
    baseline=leaders(deg); losses=defaultdict(Counter)
    for (a,b),sup in g.items():
        if len(sup)==1:losses[next(iter(sup))][a]+=1
    changes=[]; min_margin=None; worst=[]
    for h in hosts:
        direct=dict.fromkeys(deg,0)
        for (a,b),sup in g.items():
            if sup-{h}:direct[a]+=1
        assert direct=={a:n-losses[h][a] for a,n in deg.items()}
        win=leaders(direct)
        if win!=baseline:changes.append(dict(host=h,leaders=win))
        if len(baseline)==1 and len(deg)>1:
            lead=baseline[0]
            margin=direct[lead]-max(n for a,n in direct.items() if a!=lead)
            if min_margin is None or margin<min_margin:min_margin,worst=margin,[h]
            elif margin==min_margin:worst.append(h)
    out[key]=dict(pairs=len(g),investor_names=len(deg),hosts=len(hosts),leaders=baseline,top=deg.most_common(5),changes=changes,worst_margin=min_margin,worst_hosts=worst)
from math import lcm
for key,g in modes.items():
    by=defaultdict(list)
    for (a,b),ss in g.items():by[a].append(ss)
    order=sorted(by,key=lambda a:(-len(by[a]),a));lead=order[0]
    assert len(by[lead])>len(by[order[1]])
    den=lcm(*(len(s) for s in by[lead]))
    w=Counter()
    for s in by[lead]:
        for host in s:w[host]+=den//len(s)
    assert sum(w.values())==len(by[lead])*den
    lower=None;witness=None
    for ix,rival in enumerate(order[1:]):
        solo=Counter(next(iter(s)) for s in by[rival] if len(s)==1)
        ranked=sorted(w,key=lambda h:(-(w[h]-den*solo[h]),h))
        gap=len(by[lead])-len(by[rival]);total=0
        for k,h in enumerate(ranked,1):
            if w[h]<=den*solo[h]:break
            total+=w[h]-den*solo[h]
            if total>=gap*den:
                lower=k if lower is None else min(k,lower)
                break
        if ix<5:
            removed=set()
            for h in ranked:
                removed.add(h)
                left=sum(bool(s-removed) for s in by[lead]);right=sum(bool(s-removed) for s in by[rival])
                if right>=left:
                    if witness is None or len(removed)<len(witness['hosts']):witness=dict(hosts=sorted(removed),rival=rival,leader_degree=left,rival_degree=right)
                    break
    assert lower is not None and witness and lower<=len(witness['hosts'])
    out[key]['minimum_removals_bounds']=[lower,len(witness['hosts'])]
    out[key]['witness']=witness
from itertools import combinations
from fractions import Fraction
for key,g in modes.items():
    by=defaultdict(list)
    hosts=sorted(set.union(*g.values()))
    for (a,b),ss in g.items():by[a].append(ss)
    order=sorted(by,key=lambda a:(-len(by[a]),a));lead=order[0]
    def one_two(a):
        singles=Counter(next(iter(s)) for s in by[a] if len(s)==1)
        doubles=Counter(tuple(sorted(s)) for s in by[a] if len(s)==2)
        return singles,doubles
    def lost(parts,h,k):return parts[0][h]+parts[0][k]+parts[1][(h,k)]
    lb=one_two(lead);low=len(by[lead])-max(lost(lb,h,k) for h,k in combinations(hosts,2))
    candidates=[(a,one_two(a)) for a in order[1:] if len(by[a])>=low]
    two=None;count=0
    for h,k in combinations(hosts,2):
        l=len(by[lead])-lost(lb,h,k)
        hits=[(a,len(by[a])-lost(u,h,k)) for a,u in candidates if len(by[a])-lost(u,h,k)>=l]
        if hits:
            count+=1
            if two is None:two=dict(hosts=[h,k],leader_degree=l,rivals=hits)
    rec=out[key];old=rec['minimum_removals_bounds'];witness=rec['witness']
    def margin(a,remove):return sum(not s<=remove for s in by[lead])-sum(not s<=remove for s in by[a])
    for rival in order[1:13]:
        remove=set()
        while margin(rival,remove)>0 and len(remove)<len(witness['hosts']):
            candidates_to_add={tuple(sorted(s-remove)) for s in by[lead] if s-remove and len(s-remove)+len(remove)<=len(witness['hosts'])}
            if not candidates_to_add:break
            before=margin(rival,remove)
            def rank(add):
                gain=before-margin(rival,remove|set(add))
                return (-Fraction(gain,len(add)),len(add),add)
            remove.update(min(candidates_to_add,key=rank))
        if margin(rival,remove)<=0:
            for h in sorted(remove):
                if margin(rival,remove-{h})<=0:remove.remove(h)
            if len(remove)<len(witness['hosts']):witness=dict(hosts=sorted(remove),rival=rival,leader_degree=sum(not s<=remove for s in by[lead]),rival_degree=sum(not s<=remove for s in by[rival]))
    lower=max(old[0],2 if two else 3)
    if two is not None and len(witness['hosts'])>2:witness=dict(hosts=two['hosts'],rival=two['rivals'][0][0],leader_degree=two['leader_degree'],rival_degree=two['rivals'][0][1])
    assert margin(witness['rival'],set(witness['hosts']))==witness['leader_degree']-witness['rival_degree']<=0
    assert lower<=len(witness['hosts'])<=old[1]
    rec.update(two_host_coalitions=len(hosts)*(len(hosts)-1)//2,two_host_changes=count,two_host_witness=two,improved_bounds=[lower,len(witness['hosts'])],improved_witness=witness)
result=dict(pin=pin,input_sha256=source_sha,counts=stats,modes=out)
assert source_sha=='89752ca13ef5516cf22805616a5976b0fecc717c4fecb29e739bc7297385f56a'
target=Path('/content/capital-coalition-proof.zip')
with zipfile.ZipFile(target,'x',zipfile.ZIP_DEFLATED) as z:z.writestr('result.json',json.dumps(result,ensure_ascii=False))
print('archive_sha256 '+hashlib.sha256(target.read_bytes()).hexdigest())