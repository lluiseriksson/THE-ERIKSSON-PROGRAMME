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
columns='relationship_pass document_date ai_stack_layers relationship_type relationship_status evidence_strength actor_1_type actor_2_type directionality actor_1_name actor_2_name link'.split()
appearances=defaultdict(set)
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
            if key=='fold' and x!=y:appearances[x,y,r['link'].strip(),host].add(r['relationship_pass'])
assert source_sha=='89752ca13ef5516cf22805616a5976b0fecc717c4fecb29e739bc7297385f56a'
graphs={k:defaultdict(set) for k in ('union','pass1','pass2','same_url_both')}
for (x,y,url,host),seen in appearances.items():
    assert seen<= {1,2} and seen
    graphs['union'][x,y].add(host)
    for k in seen:graphs['pass'+str(k)][x,y].add(host)
    if seen=={1,2}:graphs['same_url_both'][x,y].add(host)
assert graphs['union']==modes['fold']
out={}
for name,g in graphs.items():
    degree=Counter(a for a,b in g)
    top=sorted(((n,a) for a,n in degree.items()),reverse=True)
    out[name]=dict(pairs=len(g),investors=len(degree),source_hosts=len(set().union(*g.values())),top=top[:10],margin=top[0][0]-top[1][0],nvidia=degree['nvidia'],sequoia=degree['sequoia capital'])
both=set(graphs['pass1'])&set(graphs['pass2'])
same=set(graphs['same_url_both'])
assert same<=both and len(set(graphs['pass1'])|set(graphs['pass2']))==6417
report=dict(pin=pin,input_sha256=source_sha,sample=dict(stats),graphs=out,intersection_pairs=len(both),same_document_pairs=len(same),different_url_only=len(both-same),document_unit='Exact trimmed publisher URL; all other eligibility and actor normalization shared with the host analysis')
archive=Path('/content/pass-agreement.zip')
with zipfile.ZipFile(archive,'x',zipfile.ZIP_DEFLATED) as z:z.writestr('result.json',json.dumps(report,sort_keys=True))
print('archive_sha256 '+hashlib.sha256(archive.read_bytes()).hexdigest())
