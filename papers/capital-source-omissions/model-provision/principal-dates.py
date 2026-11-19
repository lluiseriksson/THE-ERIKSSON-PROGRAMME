from pathlib import Path
from collections import defaultdict,Counter
from urllib.request import urlopen,Request
from urllib.parse import urlsplit
import hashlib,unicodedata,json,zipfile,io
import pandas as pd
rev='e737b94a38cf77b2ec3a29cb1c6bd756fb1329fb'
url='https://huggingface.co/datasets/sarahcen/ai-supply-chain/resolve/'+rev+'/data/gsearch_relationship_results.parquet'
digest='89752ca13ef5516cf22805616a5976b0fecc717c4fecb29e739bc7297385f56a'
with urlopen(Request(url,headers={'User-Agent':'Programme-economic-research/1'}),timeout=45) as f:data=f.read(35815746)
if len(data)!=35815745 or hashlib.sha256(data).hexdigest()!=digest: raise ValueError('Data identity mismatch')
cols='link document_date actor_1_name actor_2_name relationship_type relationship_status directionality ai_stack_layers'.split()
import itertools
from collections import defaultdict,Counter
def require(ok,msg):
    if not ok:raise ValueError(msg)
def norm(s):return ' '.join(unicodedata.normalize('NFKC',s).casefold().split())
alphabet={'alphabet','alphabet inc','alphabet inc.','google','google llc','google cloud','deepmind','google deepmind'}
df=pd.read_parquet(io.BytesIO(data),columns=cols)
dates=pd.to_datetime(df.document_date,errors='coerce',utc=True,format='mixed')
inside=(dates>='2022-11-01') & (dates<'2026-11-01')
def ismodel(x):
    if isinstance(x,str):
        if x=='MODELS':return True
        try:x=json.loads(x)
        except ValueError:return False
    return x is not None and 'MODELS' in x
eligible=(df.relationship_type=='PROVISION') & (df.relationship_status=='ESTABLISHED') & df.ai_stack_layers.map(ismodel)
needed=set(s.strip() for s in df.loc[eligible & dates.isna(),'link'] if isinstance(s,str))
known=defaultdict(set)
for s,flag in zip(df.loc[dates.notna(),'link'],inside[dates.notna()]):
    if isinstance(s,str) and s.strip() in needed:known[s.strip()].add(bool(flag))
rows=[];counts=Counter()
for i,r in df[eligible].iterrows():
    a,b=r.actor_1_name,r.actor_2_name
    if r.directionality=='ACTOR_2_TO_ACTOR_1':a,b=b,a
    elif r.directionality!='ACTOR_1_TO_ACTOR_2':continue
    if not all(isinstance(s,str) and s.strip() for s in (a,b,r.link)):continue
    doc=r.link.strip();host=(urlsplit(doc).hostname or '').lower().removeprefix('www.')
    if not host:continue
    if pd.isna(dates[i]):
        flags=known[doc]
        require(len(flags)<=1,'Inconsistent window statuses for an undated document')
        status=('forced_in' if True in flags else 'forced_out') if flags else 'optional'
    else:status='dated_in' if inside[i] else 'dated_out'
    counts[status]+=1
    rows.append((norm(a),norm(b),doc,host,status))

fixed=set(['009af8f7d8a12d2d31aa79ba3d11682fc6effe3a930c5972b839300910331437', '099dec7e6e54a2f060bc940a4c381c869b4bfc36912ea7ad7427928c6acea044', '0c99e963f5bd835d9a6d74b3895ab386cfd57f65b6e4f131bd0ed84f6b3d34b7', '27bd63290523d3dfbc78052cf535cb1b0165dd5eed04e1a0144daca05a619d82', '49aaecedf81bf410138165d2bfdf9fcf8d156c1f261fce496c6b3b5b0695a64c', '4f60934e72557da25f0ba23cd733c283ee0c7ba83ac9468cd3324e778b829e16', '57b09e4eef515960a088dd3398f78be71b9de51256b1d1e1b3ad45294620983f', '6542423729abb404ef420173970f7ccfe8b75ee260be54a046adbc13d8d39fbc', '6ba413a3c70849168a40cc1aeefbbd42ebc0112aa887a83ed0a7689ee35b92f5', '8593db728cb2741e8e41d28fb3b3e3ea4a31d6167cb21a8a6bc96c5cde501a05', '88b85cf301fd7d18879252c36d4b293b971c0c30d6cd74ab37484553873631e0', '994677f942a8a1042c66a9c287e47a67aaa41f8e3cbeb67cd1e1eb1af05192f9', 'bc682b9a867a95ef6f59fc51c7061eb30ea86a24b275453ade00a60676a58f73', 'ce43a07820ea43d7f108c9fe821e0a1c0956703a67e752c73749d1a6d1da9112', 'd5f8809630a84cca023bcf0bcf0f63a0de2c0e9a73ec9f4981e58e100f8199ec', 'de6fb2bcd731a49fa77d913efab32119557ca215889c8e54408601f2cadb8b8f', 'ed78974fb39c971768135ca59bc55bacbf39f105782d6a19e056a26c86bc4dcb', 'fbd9377008da358e699bd1389dd71b433e029cabf222521d776fadf8ab417545'])
panels={'01': ['009af8f7d8a12d2d31aa79ba3d11682fc6effe3a930c5972b839300910331437', '0687efea7715fef0177b5dfbaec056d6f57f9123b22c907087a3696bc04e942a', '099dec7e6e54a2f060bc940a4c381c869b4bfc36912ea7ad7427928c6acea044', '4f60934e72557da25f0ba23cd733c283ee0c7ba83ac9468cd3324e778b829e16', '51540788121cfdbdb3496352073cce0623a5fe6d46ff2bbd992e70744b999221', '6542423729abb404ef420173970f7ccfe8b75ee260be54a046adbc13d8d39fbc', '6ba413a3c70849168a40cc1aeefbbd42ebc0112aa887a83ed0a7689ee35b92f5', '7c6aec0b8aa0a29ac7afdd395eb751b166504f6294ba09803c7ed8be91c75ab7', '8593db728cb2741e8e41d28fb3b3e3ea4a31d6167cb21a8a6bc96c5cde501a05', '994677f942a8a1042c66a9c287e47a67aaa41f8e3cbeb67cd1e1eb1af05192f9', 'bc682b9a867a95ef6f59fc51c7061eb30ea86a24b275453ade00a60676a58f73', 'ce43a07820ea43d7f108c9fe821e0a1c0956703a67e752c73749d1a6d1da9112', 'd5f8809630a84cca023bcf0bcf0f63a0de2c0e9a73ec9f4981e58e100f8199ec', 'de6fb2bcd731a49fa77d913efab32119557ca215889c8e54408601f2cadb8b8f', 'ed78974fb39c971768135ca59bc55bacbf39f105782d6a19e056a26c86bc4dcb'], '10': ['009af8f7d8a12d2d31aa79ba3d11682fc6effe3a930c5972b839300910331437', '099dec7e6e54a2f060bc940a4c381c869b4bfc36912ea7ad7427928c6acea044', '0c99e963f5bd835d9a6d74b3895ab386cfd57f65b6e4f131bd0ed84f6b3d34b7', '27bd63290523d3dfbc78052cf535cb1b0165dd5eed04e1a0144daca05a619d82', '49aaecedf81bf410138165d2bfdf9fcf8d156c1f261fce496c6b3b5b0695a64c', '51540788121cfdbdb3496352073cce0623a5fe6d46ff2bbd992e70744b999221', '57b09e4eef515960a088dd3398f78be71b9de51256b1d1e1b3ad45294620983f', '6ba413a3c70849168a40cc1aeefbbd42ebc0112aa887a83ed0a7689ee35b92f5', '7c6aec0b8aa0a29ac7afdd395eb751b166504f6294ba09803c7ed8be91c75ab7', '8593db728cb2741e8e41d28fb3b3e3ea4a31d6167cb21a8a6bc96c5cde501a05', '88b85cf301fd7d18879252c36d4b293b971c0c30d6cd74ab37484553873631e0', '994677f942a8a1042c66a9c287e47a67aaa41f8e3cbeb67cd1e1eb1af05192f9', 'a205e1cf6b47c1f39fb0f55e47a4bcec113e6cf7de04ca9a0844a3437b017c14', 'ce43a07820ea43d7f108c9fe821e0a1c0956703a67e752c73749d1a6d1da9112', 'de6fb2bcd731a49fa77d913efab32119557ca215889c8e54408601f2cadb8b8f', 'ed78974fb39c971768135ca59bc55bacbf39f105782d6a19e056a26c86bc4dcb', 'fbd9377008da358e699bd1389dd71b433e029cabf222521d776fadf8ab417545'], '11': ['009af8f7d8a12d2d31aa79ba3d11682fc6effe3a930c5972b839300910331437', '099dec7e6e54a2f060bc940a4c381c869b4bfc36912ea7ad7427928c6acea044', '0c99e963f5bd835d9a6d74b3895ab386cfd57f65b6e4f131bd0ed84f6b3d34b7', '27bd63290523d3dfbc78052cf535cb1b0165dd5eed04e1a0144daca05a619d82', '49aaecedf81bf410138165d2bfdf9fcf8d156c1f261fce496c6b3b5b0695a64c', '51540788121cfdbdb3496352073cce0623a5fe6d46ff2bbd992e70744b999221', '57b09e4eef515960a088dd3398f78be71b9de51256b1d1e1b3ad45294620983f', '6ba413a3c70849168a40cc1aeefbbd42ebc0112aa887a83ed0a7689ee35b92f5', '7c6aec0b8aa0a29ac7afdd395eb751b166504f6294ba09803c7ed8be91c75ab7', '8593db728cb2741e8e41d28fb3b3e3ea4a31d6167cb21a8a6bc96c5cde501a05', '88b85cf301fd7d18879252c36d4b293b971c0c30d6cd74ab37484553873631e0', '994677f942a8a1042c66a9c287e47a67aaa41f8e3cbeb67cd1e1eb1af05192f9', 'a205e1cf6b47c1f39fb0f55e47a4bcec113e6cf7de04ca9a0844a3437b017c14', 'ce43a07820ea43d7f108c9fe821e0a1c0956703a67e752c73749d1a6d1da9112', 'de6fb2bcd731a49fa77d913efab32119557ca215889c8e54408601f2cadb8b8f', 'ed78974fb39c971768135ca59bc55bacbf39f105782d6a19e056a26c86bc4dcb', 'fbd9377008da358e699bd1389dd71b433e029cabf222521d776fadf8ab417545']}
def keyid(doc):return hashlib.sha256(doc.encode()).hexdigest()
results={}
for code in ('00','01','10','11'):
    grouped,cut=(int(x) for x in code)
    def label(a):return 'alphabet [selected family]' if grouped and a in alphabet else a
    leaders=('anthropic','alphabet [selected family]' if grouped else 'openai')
    base=defaultdict(set);extra=defaultdict(set)
    for a,b,d,h,s in rows:
        if cut and h=='anthropic.com':continue
        a,b=label(a),label(b)
        if a==b:continue
        if s=='dated_in' or s=='forced_in':base[a].add(b)
        elif s=='optional':extra[keyid(d)].add((a,b))
    optional={i for i,es in extra.items() if any(a in leaders and b not in base[a] for a,b in es)}
    if code!='00':assert optional==set(panels[code])
    # All other documents leave both target degrees unchanged across every world.
    for i in fixed:
        for a,b in extra[i]:base[a].add(b)
    unknown=sorted(i for i in optional-fixed if any(a in leaders and b not in base[a] for a,b in extra[i]))
    assert len(unknown)<=12
    whole={a:set(bs) for a,bs in base.items()}
    for es in extra.values():
        for a,b in es:whole.setdefault(a,set()).add(b)
    third=max(len(bs) for a,bs in whole.items() if a not in leaders)
    assert third<max(len(base[a]) for a in leaders)
    worlds=[]
    for mask in range(1<<len(unknown)):
        selected=[i for j,i in enumerate(unknown) if mask&(1<<j)]
        counts=[len(base[a]|{b for i in selected for name,b in extra[i] if name==a}) for a in leaders]
        worlds.append(dict(selected=selected,degrees=counts,margin=counts[0]-counts[1]))
    results[code]=dict(ordered_pair=leaders,unresolved=unknown,other_provider_degree_upper=third,baseline=worlds[0]['degrees'],possible_margins=sorted({s['margin'] for s in worlds}),worlds=worlds)
with zipfile.ZipFile('/content/principal-dates.zip','x',zipfile.ZIP_DEFLATED) as z:z.writestr('principal-dates.json',json.dumps(results,indent=2))
print('archive_sha256 '+hashlib.sha256(Path('/content/principal-dates.zip').read_bytes()).hexdigest())
