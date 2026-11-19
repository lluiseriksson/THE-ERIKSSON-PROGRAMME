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

import base64,io
proof=json.loads(zipfile.ZipFile(io.BytesIO(base64.b64decode('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'))).read("result.json"))
witness={'hosts': ['aifundingtracker.com', 'cleverhack.com', 'cloverleafinfra.com', 'cnbc.com', 'edzor.com', 'en.globes.co.il', 'en.wikipedia.org', 'enkiai.com', 'exa.ai', 'extern.com', 'fervorcapital.vc', 'finance.yahoo.com', 'fnex.com', 'forbes.com', 'futuriom.com', 'futurumgroup.com', 'getaibook.com', 'getbridged.co', 'google.com', 'impekable.com', 'investor.marvell.com', 'nebius.com', 'news.crunchbase.com', 'news.synopsys.com', 'nextplatform.com', 'nvidianews.nvidia.com', 'pe150.com', 'prnewswire.com', 'sg.finance.yahoo.com', 'softwarecapitalraise.net', 'spyglass.org', 'startupfeed.in', 'stepmark.ai', 'techcrunch.com', 'technotime.net', 'theglobeandmail.com', 'tradingkey.com', 'venturebeat.com'], 'leader_after': 43, 'rival_after': 43, 'size': 38}
import base64
from io import BytesIO
assert source_sha==proof['input_hash'] and pin==proof['pin']
g=modes['fold']
by_name=defaultdict(list)
for (a,b),s in g.items():by_name[a].append(frozenset(s))
sources=sorted(set.union(set(),*by_name['nvidia']))
assert sources==proof['source_hosts']
pos={h:i for i,h in enumerate(sources)}
d=len(by_name['nvidia'])
assert d==154
high={a for a,s in by_name.items() if a!='nvidia' and len(s)>proof['cutoff']}
low={a for a in by_name if a not in high and a!='nvidia'}
assert high==set(proof['rivals']) and len(low)==proof['tail_count']
leaf_count=0
def check(rival,item,base):
    assert base==item['degree'] and item['certified']
    coeffs=Counter(tuple(sorted(s)) for s in by_name['nvidia'])
    if rival:
        coeffs.subtract(tuple(sorted(s)) for s in by_name[rival] if all(h in pos for h in s))
    columns=len(pos)
    system=[]
    target={}
    for s,n in sorted(coeffs.items()):
        if n==0:continue
        hs=[pos[h] for h in s]
        if len(hs)==1:
            target[hs[0]]=-n
            continue
        auxiliary=columns
        columns+=1
        target[auxiliary]=-n
        if n<0:
            system.append((dict([(h,1) for h in hs]+[(auxiliary,-1)]),len(s)-1))
        else:
            system.extend(({auxiliary:1,h:-1},0) for h in hs)
    target[columns]=-1
    system.append((target,base-d))
    def visit(node,fixed):
        global leaf_count
        if 'split' in node:
            j=node['split']
            assert type(j)==int and 0<=j<len(pos) and j not in fixed and len(node['nodes'])==2
            for value,child in enumerate(node['nodes']):visit(child,{**fixed,j:value})
            return
        scale=proof['certificate_scale']
        assert scale==1000000 and proof['threshold_tested']==37
        cost=[scale]*len(pos)+[0]*(columns-len(pos))+[1000*scale]
        offset=0
        for i,weight in node['dual']:
            assert type(i)==int and 0<=i<len(system) and type(weight)==int and weight>=0
            row,b=system[i]
            offset-=weight*b
            for j,element in row.items():cost[j]+=weight*element
        for j,v in enumerate(cost):
            if j in fixed:offset+=v*fixed[j]
            elif v<0:offset+=v*(d if j==columns else 1)
        assert offset>37*scale
        leaf_count+=1
    visit(item['cert'],{})
for a in sorted(high):check(a,proof['rivals'][a],len(by_name[a]))
check(None,proof['tail'],max(len(by_name[a]) for a in low))
omitted=set(witness['hosts'])
assert len(omitted)==38
degrees=Counter(a for (a,b),s in g.items() if s-omitted)
assert degrees['nvidia']==degrees['sequoia capital']==43
audit=dict(minimum=38,normalization='NFKC casefold whitespace',pin=pin,sha256=source_sha,
    individually_checked=len(high),residual_checked=len(low),verified_leaves=leaf_count,
    rows=stats['input'],eligible=stats['eligible'],investors=len(by_name),pairs=len(g),
    budget_excluded=37,witness_size=len(omitted),witness_hosts=sorted(omitted),witness_counts={a:degrees[a] for a in ['nvidia','sequoia capital']},
    leader_set_after=sorted(a for a,n in degrees.items() if n==max(degrees.values())),maximum_after=max(degrees.values()))
path=Path('/content/verified-threshold.zip')
with zipfile.ZipFile(path,'x',zipfile.ZIP_DEFLATED) as z:z.writestr('audit.json',json.dumps(audit,sort_keys=True))
print('archive_sha256 '+hashlib.sha256(path.read_bytes()).hexdigest())
