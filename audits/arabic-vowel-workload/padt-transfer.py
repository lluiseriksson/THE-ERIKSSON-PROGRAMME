"""Replicate the published eligibility and check if a dev-ranked band swap transfers.

Inputs are the attributed Amer evidence archive and checksum-pinned UD Arabic-PADT.
The test was inspected in aggregate before this diagnostic. This is retrospective.
"""
from collections import Counter, defaultdict
from fractions import Fraction as F
from functools import lru_cache
import hashlib, json, re, zipfile
from urllib.request import urlopen

with zipfile.ZipFile('zenodo_p2.zip') as z:
    def load(name):
        return json.loads(z.read('zenodo_p2/'+name))
    ref=load('results_539n_stats.json')
    lex=load('results_539p_stats.json')
    checks=dict(line.split()[::-1] for line in z.read('zenodo_p2/treebank_sha256.txt').decode().splitlines())
revs=['5b1ad7e87c70b0e290f8499b64531c7d6a88eea0','53a6ea943f54376bd45f6116fb03ab6c405cc70b','30c8a6fc7f16adee5b2986632d3786b56aef2e6c']
def fetch(rev,split):
    name='ar_padt-ud-'+split+'.conllu'
    with urlopen('https://raw.githubusercontent.com/UniversalDependencies/UD_Arabic-PADT/'+rev+'/'+name,timeout=30) as f:
        data=f.read()
    return data,hashlib.sha256(data).hexdigest()==checks[name]
for rev in revs:
    dev,ok=fetch(rev,'dev')
    if ok:
        train,x=fetch(rev,'train')
        test,y=fetch(rev,'test')
        if x and y:break
else:raise ValueError('No release matches all three source checksums')

vowels='َُِ'
preps=set(lex['PREP'])-set('يا أيها لولا إلا غير سوى لا إنما حتى مذ منذ حيث حين'.split())
excluded=set(lex['MABNI'])
def cue(prev):
    if prev in preps:return ('R1','ِ')
    if re.fullmatch('[ء-ي]{3,}وا',prev) and not re.fullmatch('[وف]?(?:قالوا|أولوا)',prev):return ('R2','َ')
    if prev in {'أن','إن','ان'}:return ('R4','َ')
    if prev in {'كل','بعض','غير','جميع'}:return ('R5','ِ')
    if prev in {'كان','كانت'}:return ('R6','ُ')

def rows(data):
    prev=None
    for line in data.decode().splitlines():
        t=line.split('\t')
        if len(t)<10:
            prev=None
            continue
        if not t[0].isdigit():continue
        alt=re.search(r'(?:^|\|)Vform=([^|]+)',t[9])
        word=alt[1] if alt and re.search('[ً-ْ]',alt[1]) else t[1]
        word=re.sub('[^ء-يً-ْٰ]','',word).replace('ـ','')
        if not word:continue
        bare=re.sub('[ً-ْٰ]','',word)
        if prev is not None and bare.startswith('ال') and len(bare)>=5 and bare not in excluded and bare!='العقود' and not re.search('(?:ان|ون|ين|ات|[يىاءئؤو])$',bare):
            marks=re.search('[ً-ْٰ]*$',word)[0]
            short=[v for v in marks if v in vowels]
            if len(short)==1 and not re.search('[ًٌٍْ]',marks):yield prev,short[0]
        prev=bare

num=defaultdict(Counter)
global_counts=Counter()
splits={k:list(rows(v)) for k,v in [('train',train),('dev',dev),('test',test)]}
assert {k:len(r) for k,r in splits.items()}==ref['n']
for prev,v in splits['train']:
    num[prev][v]+=1
    global_counts[v]+=1
levels=[95,90,85,80,77,70,60]
@lru_cache(None)
def table(prev):
    c=num[prev]
    if sum(c.values())<20:c=global_counts
    v=max(vowels,key=lambda v:c[v])
    score=F(2*c[v]+1,2*sum(c.values())+3)
    return next((k for k in levels if score>=F(k,100)),0),v

def evaluate(k):
    bands={i:[0,0] for i in [100,*levels,0]}
    per=defaultdict(lambda:[0,0])
    for prev,gold in splits[k]:
        rule=cue(prev)
        if rule:
            label,pred=rule
            per[label][0]+=1
            per[label][1]+=int(pred==gold)
            band=100
        else:
            band,pred=table(prev)
        bands[band][0]+=1
        bands[band][1]+=int(pred!=gold)
    if dict(per)!=ref['per_rule'][k]:raise ValueError((k,dict(per),ref['per_rule'][k]))
    d=sum(n for j,(n,e) in bands.items() if j>=77)
    err=sum(e for j,(n,e) in bands.items() if j>=77)
    if k!='train':
        source=ref[k+'_combined_077']
        assert (d,d-err)==(source['dec'],source['ok'])
    return bands
evaluate('train')
dev_b=evaluate('dev')
# Preserve fills at or above 0.80, then choose among three disjoint bands.
# Ties prefer the higher nominal score. Do not infer test errors to pick an arm.
choice=min((i for i in [77,70,60] if dev_b[i][0]),key=lambda i:(F(dev_b[i][1],dev_b[i][0]),-i))
test_b=evaluate('test')
for r in ref['curve']:
    cut=round(100*r['tau'])
    d=sum(n for i,(n,e) in test_b.items() if i>=cut)
    err=sum(e for i,(n,e) in test_b.items() if i>=cut)
    assert (d,d-err)==(r['dec'],r['ok'])
m=test_b[77][0]
assert test_b[choice][0]>=m
expected=F(m*test_b[choice][1],test_b[choice][0])
print(json.dumps(dict(revision=rev,file_hashes=checks,eligible=ref['n'],bands_dev=dev_b,bands_test=test_b,chosen_on_development=choice,test_extra_fills=m,test_original_band_errors=test_b[77][1],expected_errors_selected_band=str(expected),gain=str(test_b[77][1]-expected),external_validation=False),indent=2))
