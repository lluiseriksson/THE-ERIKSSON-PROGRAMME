from pathlib import Path
from collections import defaultdict,Counter
from datetime import datetime,timezone
from urllib.parse import urlencode
from urllib.request import Request,urlopen
import hashlib,json,re,zipfile
def raw(url,params):
    with urlopen(Request(url+'?'+urlencode(params),headers={'User-Agent':'Eriksson Programme aggregate land use audit'}),timeout=50) as f:data=f.read(6000001)
    assert len(data)<=6000000
    return data
def h(x):return hashlib.sha256(x).hexdigest()
def pack(x):return json.dumps(x,sort_keys=True,ensure_ascii=False,indent=2)
def key(x):return re.sub(r'\s+','',(x or '').upper())
def table(values):return dict(sorted(Counter(values).items()))
city='https://data.cityofnewyork.us/resource/hgx4-8ukb.json'
q={'$select':'project_id,actions,project_status,public_status,app_filed_date,certified_referred,approval_date','$where':"approval_date >= '2015-01-01T00:00:00' and approval_date < '2025-01-01T00:00:00' and actions like '%ZM%'",'$order':'project_id','$limit':'50000'}
r0=raw(city,q);assert h(r0)=='619a87ef785ce4352508e51fa62b5f3b2a049ca426fa03c986e6c07abfcd5e42'
q['$select']+=',ulurp_numbers';r1=raw(city,q);ext=json.loads(r1)
assert [{k:v for k,v in r.items() if k!='ulurp_numbers'} for r in ext]==json.loads(r0)
projects={r['project_id']:r for r in ext if 'ZM' in [s.strip() for s in r['actions'].split(';')]};assert len(projects)==126
arc='https://services5.arcgis.com/GfwWNkhOj9bNBqoJ/ArcGIS/rest/services/nyzma/FeatureServer/0/query'
idquery={'f':'json','where':'1=1','returnIdsOnly':'true'}
ids=sorted(json.loads(raw(arc,idquery))['objectIds'])
features=[]; rawdb={'zap.json':r1}
for n in range(0,len(ids),300):
    query={'f':'json','where':f'OBJECTID >= {ids[n]} AND OBJECTID <= {ids[min(n+299,len(ids)-1)]}','outFields':'OBJECTID,ULURPNO,STATUS,EFFECTIVE','returnGeometry':'false'}
    data=raw(arc,query);rawdb[f'map-{n}.json']=data
    features.extend(f['attributes'] for f in json.loads(data)['features'])
assert sorted(f['OBJECTID'] for f in features)==ids==sorted(json.loads(raw(arc,idquery))['objectIds'])
indices=defaultdict(list)
for f in features:
    if f['ULURPNO']:indices[key(f['ULURPNO'])].append(f)
dates=lambda fs:sorted({datetime.fromtimestamp(f['EFFECTIVE']/1000,timezone.utc).date().isoformat() for f in fs if f['EFFECTIVE'] is not None})
keyrows=defaultdict(set);ledger=[];alltokens=set()
for i,r in projects.items():
    tokens={key(s) for s in (r.get('ulurp_numbers') or '').split(';') if key(s)}
    alltokens.update(tokens)
    matched=sorted(t for t in tokens if any(key(f['STATUS'])=='ADOPTED' for f in indices.get(t,[])))
    for k in matched:keyrows[k].add(i)
    ledger.append(dict(project=i,approval=r['approval_date'][:10],certification=r['certified_referred'][:10],tokens=sorted(tokens),adopted_keys=matched))
def adopted(k):return [f for f in indices[k] if key(f['STATUS'])=='ADOPTED']
action=[]
for k,pp in sorted(keyrows.items()):
    fs=adopted(k);ds=dates(fs)
    action.append(dict(key=k,projects=sorted(pp),map_dates=ds,null_dates=sum(f['EFFECTIVE'] is None for f in fs),map_rows=len(fs),project_years=sorted({projects[i]['approval_date'][:4] for i in pp})))
unmatched=[r for r in ledger if not r['adopted_keys']]
opposite=sorted(k for k in indices if k not in keyrows and any('2015'<=dt[:4]<='2024' for dt in dates(adopted(k))))
pairs=[a for a in action if len(a['project_years'])==1 and not a['null_dates'] and len(a['map_dates'])==1]
result=dict(project_n=len(projects),map_object_count=len(ids),map_status_counts=table(f['STATUS'] or 'missing' for f in features),adopted_id_count=len(action),projects_by_adopted_ids=table(len(r['adopted_keys']) for r in ledger),ids_by_projects=table(len(a['projects']) for a in action),ids_by_feature_count=table(a['map_rows'] for a in action),unmatched_projects=[r['project'] for r in unmatched],reverse_unmatched=opposite,reverse_n=len(opposite),ambiguous_or_missing_dates=[a['key'] for a in action if a not in pairs],same_date=sum(all(projects[i]['approval_date'][:10]==a['map_dates'][0] for i in a['projects']) for a in pairs),different_year=[a['key'] for a in pairs if a['map_dates'][0][:4]!=a['project_years'][0]],unique_pairs=len(pairs),year_projects_all=table(r['approval'][:4] for r in ledger),year_projects_matched=table(r['approval'][:4] for r in ledger if r['adopted_keys']),year_actions_by_zap=table(a['project_years'][0] for a in action if len(a['project_years'])==1),year_actions_by_map=table(a['map_dates'][0][:4] for a in pairs),sources={k:h(v) for k,v in rawdb.items()},fetched=datetime.now(timezone.utc).isoformat())
expected_sources={"map-0.json":"585b1740a108e127bf1ef0e3ed19bce849d7bb6783d483533916f0a43cbf71fd","map-1200.json":"1173651ffca33cf36e5259c781da6c72ebba1dadabdef7dc18a0d78fe9833568","map-300.json":"8167ee7cce8b5824ac67256a7dc9af0dc1672039ac8898e7cd8a96dfc7a10e09","map-600.json":"cf7d5f0cc3708fbd154eaafd4eb26bc665579bb23be30ed084b49f053795f21d","map-900.json":"7bf2ca9c2912bbf06a44c176c4c5e9edb7bf3c447def13f067d67e62d5c23098","zap.json":"73d0dc5a51c9f3a88ade1933bb28b33aca01d6d705d75c9b179e5235358f847a"}
# Exploratory sensitivity after the strict link. Drop a single C only for complete borough map-action numbers.
def equivalent(k):
    return k[1:] if re.fullmatch(r'C[0-9]{6}A?ZM[MKQRX]',k) else k
def tokens(r):return {equivalent(key(v)) for v in (r.get('ulurp_numbers') or '').split(';') if key(v)}
domain={k for k in indices if re.fullmatch(r'[0-9]{6}A?ZM[MKQRX]',equivalent(k)) and adopted(k)}
maps=defaultdict(set)
for k in domain:maps[equivalent(k)].add(k)
assert all(len(v)==1 for v in maps.values()),'canonical map keys collide'
links={i:sorted(tokens(r)&maps.keys()) for i,r in projects.items()}
aq={'$select':'project_id,ulurp_numbers,approval_date,actions','$where':"upper(ulurp_numbers) like '%ZM%'",'$order':'project_id','$limit':'50000'}
allraw=raw(city,aq);zz=json.loads(allraw);assert len(zz)<50000 and len({r['project_id'] for r in zz})==len(zz)
lookup=defaultdict(list)
for r in zz:
    for t in tokens(r)&maps.keys():lookup[t].append(r)
def status(r):
    if r['project_id'] in projects:return 'in sample'
    if not r.get('approval_date'):return 'approval date missing'
    if not ('2015'<=r['approval_date'][:4]<='2024'):return 'approval outside years'
    return 'different action token or other exclusion'
coverage=[]
for t,ks in sorted(maps.items()):
    ds=dates(adopted(next(iter(ks))));ys={d[:4] for d in ds}
    if not any('2015'<=y<='2024' for y in ys):continue
    rr=lookup[t]
    coverage.append(dict(key=t,years=sorted(ys),project_ids=sorted(r['project_id'] for r in rr),categories=sorted({status(r) for r in rr})))
edges2=defaultdict(list)
for i,ks in links.items():
    for t in ks:edges2[t].append(i)
cohort=[dict(key=t,projects=sorted(pp),map_dates=dates(adopted(next(iter(maps[t])))),approvals=sorted({projects[i]['approval_date'][:10] for i in pp})) for t,pp in sorted(edges2.items())]
out=dict(links=links,keys=cohort,reverse=coverage,all_zap_rows=len(zz),all_zap_sha=h(allraw),map_digests=result['sources'],strict_source_digests_expected=expected_sources)
assert expected_sources==result['sources']
dest=Path('/content/sensitivity.zip')
with zipfile.ZipFile(dest,'x',zipfile.ZIP_DEFLATED) as z:
    z.writestr('sensitivity.json',pack(out));z.writestr('extended-city.json',allraw)
print('archive_sha256 '+h(dest.read_bytes()))
