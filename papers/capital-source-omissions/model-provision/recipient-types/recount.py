from pathlib import Path
import json,hashlib,io,unicodedata,zipfile
import pandas as pd
from urllib.parse import urlsplit
from urllib.request import Request,urlopen
witnesses=json.loads("{\"recipients\":{\"10\":{\"alphabet [selected family]\":{\"7\":[\"51540788121cfdbdb3496352073cce0623a5fe6d46ff2bbd992e70744b999221\",\"7c6aec0b8aa0a29ac7afdd395eb751b166504f6294ba09803c7ed8be91c75ab7\"],\"8\":[\"7c6aec0b8aa0a29ac7afdd395eb751b166504f6294ba09803c7ed8be91c75ab7\"],\"9\":[]}},\"11\":{\"alphabet [selected family]\":{\"9\":[]}},\"00\":{\"anthropic\":{\"1\":[],\"2\":[\"51540788121cfdbdb3496352073cce0623a5fe6d46ff2bbd992e70744b999221\"],\"3\":[\"7c6aec0b8aa0a29ac7afdd395eb751b166504f6294ba09803c7ed8be91c75ab7\"],\"4\":[\"51540788121cfdbdb3496352073cce0623a5fe6d46ff2bbd992e70744b999221\",\"7c6aec0b8aa0a29ac7afdd395eb751b166504f6294ba09803c7ed8be91c75ab7\"]}},\"01\":{\"openai\":{\"3\":[\"51540788121cfdbdb3496352073cce0623a5fe6d46ff2bbd992e70744b999221\",\"7c6aec0b8aa0a29ac7afdd395eb751b166504f6294ba09803c7ed8be91c75ab7\"],\"4\":[\"7c6aec0b8aa0a29ac7afdd395eb751b166504f6294ba09803c7ed8be91c75ab7\"],\"5\":[\"51540788121cfdbdb3496352073cce0623a5fe6d46ff2bbd992e70744b999221\"],\"6\":[]}}},\"both\":{\"10\":{\"alphabet [selected family]\":{\"7\":[\"51540788121cfdbdb3496352073cce0623a5fe6d46ff2bbd992e70744b999221\",\"7c6aec0b8aa0a29ac7afdd395eb751b166504f6294ba09803c7ed8be91c75ab7\"],\"8\":[\"7c6aec0b8aa0a29ac7afdd395eb751b166504f6294ba09803c7ed8be91c75ab7\"],\"9\":[]}},\"11\":{\"alphabet [selected family]\":{\"9\":[]}},\"00\":{\"anthropic\":{\"1\":[],\"2\":[\"51540788121cfdbdb3496352073cce0623a5fe6d46ff2bbd992e70744b999221\"],\"3\":[\"7c6aec0b8aa0a29ac7afdd395eb751b166504f6294ba09803c7ed8be91c75ab7\"],\"4\":[\"51540788121cfdbdb3496352073cce0623a5fe6d46ff2bbd992e70744b999221\",\"7c6aec0b8aa0a29ac7afdd395eb751b166504f6294ba09803c7ed8be91c75ab7\"]}},\"01\":{\"openai\":{\"3\":[\"51540788121cfdbdb3496352073cce0623a5fe6d46ff2bbd992e70744b999221\",\"7c6aec0b8aa0a29ac7afdd395eb751b166504f6294ba09803c7ed8be91c75ab7\"],\"4\":[\"7c6aec0b8aa0a29ac7afdd395eb751b166504f6294ba09803c7ed8be91c75ab7\"],\"5\":[\"51540788121cfdbdb3496352073cce0623a5fe6d46ff2bbd992e70744b999221\"],\"6\":[]}}}}")
verified=set(["88b85cf301fd7d18879252c36d4b293b971c0c30d6cd74ab37484553873631e0","099dec7e6e54a2f060bc940a4c381c869b4bfc36912ea7ad7427928c6acea044","994677f942a8a1042c66a9c287e47a67aaa41f8e3cbeb67cd1e1eb1af05192f9","8593db728cb2741e8e41d28fb3b3e3ea4a31d6167cb21a8a6bc96c5cde501a05","bc682b9a867a95ef6f59fc51c7061eb30ea86a24b275453ade00a60676a58f73","4f60934e72557da25f0ba23cd733c283ee0c7ba83ac9468cd3324e778b829e16","0c99e963f5bd835d9a6d74b3895ab386cfd57f65b6e4f131bd0ed84f6b3d34b7","57b09e4eef515960a088dd3398f78be71b9de51256b1d1e1b3ad45294620983f","fbd9377008da358e699bd1389dd71b433e029cabf222521d776fadf8ab417545","de6fb2bcd731a49fa77d913efab32119557ca215889c8e54408601f2cadb8b8f","d5f8809630a84cca023bcf0bcf0f63a0de2c0e9a73ec9f4981e58e100f8199ec","ce43a07820ea43d7f108c9fe821e0a1c0956703a67e752c73749d1a6d1da9112","6542423729abb404ef420173970f7ccfe8b75ee260be54a046adbc13d8d39fbc","27bd63290523d3dfbc78052cf535cb1b0165dd5eed04e1a0144daca05a619d82","49aaecedf81bf410138165d2bfdf9fcf8d156c1f261fce496c6b3b5b0695a64c","ed78974fb39c971768135ca59bc55bacbf39f105782d6a19e056a26c86bc4dcb","009af8f7d8a12d2d31aa79ba3d11682fc6effe3a930c5972b839300910331437","6ba413a3c70849168a40cc1aeefbbd42ebc0112aa887a83ed0a7689ee35b92f5"])
u='https://huggingface.co/datasets/sarahcen/ai-supply-chain/resolve/e737b94a38cf77b2ec3a29cb1c6bd756fb1329fb/data/gsearch_relationship_results.parquet'
with urlopen(Request(u,headers={'User-Agent':'Programme-economic-research/1'}),timeout=45) as f:raw=f.read(35815746)
assert hashlib.sha256(raw).hexdigest()=='89752ca13ef5516cf22805616a5976b0fecc717c4fecb29e739bc7297385f56a'
cols='actor_1_name actor_2_name actor_1_type actor_2_type link relationship_type relationship_status ai_stack_layers document_date directionality'.split()
df=pd.read_parquet(io.BytesIO(raw),columns=cols)
df=df[(df.relationship_type=='PROVISION')&(df.relationship_status=='ESTABLISHED')&df.ai_stack_layers.map(lambda v:v is not None and 'MODELS' in v)].copy()
rev=df.directionality.eq('ACTOR_2_TO_ACTOR_1')
for col,suf in [('name','name'),('type','type')]:
    aa=df['actor_1_'+suf];bb=df['actor_2_'+suf]
    df['from_'+col]=aa.where(~rev,bb);df['to_'+col]=bb.where(~rev,aa)
df=df[df.directionality.isin(['ACTOR_2_TO_ACTOR_1','ACTOR_1_TO_ACTOR_2'])].dropna(subset=['from_name','to_name','link']).copy()
df['url']=df.link.str.strip()
df['host']=df.url.map(lambda u:(urlsplit(u).hostname or '').lower().removeprefix('www.'))
df=df[df.host.ne('')]
def norm(v):return ' '.join(unicodedata.normalize('NFKC',v).casefold().split())
for col in ['from_name','to_name']:df[col]=df[col].map(norm)
df=df[df.from_name.ne('')&df.to_name.ne('')].copy()
dt=pd.to_datetime(df.document_date,errors='coerce',format='mixed',utc=True)
df['unknown']=dt.isna()
df['hash']=df.url.map(lambda s:hashlib.sha256(s.encode()).hexdigest())
df['included']=((dt>='2022-11-01')&(dt<'2026-11-01'))|(df.unknown&df.hash.isin(verified))
family={'alphabet','alphabet inc','alphabet inc.','google','google llc','google cloud','google deepmind','deepmind'}
proof=[]
for policy,scenarios in witnesses.items():
    for code,variants in scenarios.items():
        rec=df[df.to_type.eq('COMPANY')].copy()
        if policy=='both':rec=rec[rec.from_type.eq('COMPANY')].copy()
        if code[1]=='1':rec=rec[rec.host.ne('anthropic.com')].copy()
        if code[0]=='1':
            for c in ('to_name','from_name'):rec[c]=rec[c].replace(dict.fromkeys(family,'alphabet [selected family]'))
        rec=rec[rec.from_name.ne(rec.to_name)]
        for win,gaps in variants.items():
            for m,docs in gaps.items():
                sub=rec[rec.included|(rec.unknown&rec.hash.isin(docs))]
                ranked=sub.groupby('from_name').to_name.nunique().sort_values(ascending=False)
                assert ranked.index[0]==win and int(ranked.iloc[0]-ranked.iloc[1])==int(m)
                proof.append(dict(policy=policy,scenario=code,margin=int(m),ranked=ranked.head(3).to_dict()))
out=Path('/content/typed-recount.zip')
with zipfile.ZipFile(out,'x',zipfile.ZIP_DEFLATED) as z:z.writestr('recount.json',json.dumps(proof,indent=2))
print('archive_sha256 '+hashlib.sha256(out.read_bytes()).hexdigest())
