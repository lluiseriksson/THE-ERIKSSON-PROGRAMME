from pathlib import Path
from urllib.parse import urlencode
from urllib.request import urlopen, Request
from collections import Counter
from datetime import datetime,timezone
from itertools import combinations
import hashlib,json,zipfile,re,shutil,subprocess

def fetch(url,maxbytes):
    with urlopen(Request(url,headers={'User-Agent':'Eriksson Programme academic metadata audit'}),timeout=60) as f: raw=f.read(maxbytes+1)
    if len(raw)>maxbytes:raise ValueError('Download exceeds archive scope')
    return raw
def digest(data):return hashlib.sha256(data).hexdigest()
def js(v):return json.dumps(v,ensure_ascii=False,indent=2)
base='https://data.cityofnewyork.us/resource/hgx4-8ukb.json?'
q={'$select':'project_id,actions,project_status,public_status,app_filed_date,certified_referred,approval_date','$where':"approval_date >= '2015-01-01T00:00:00' and approval_date < '2025-01-01T00:00:00' and actions like '%ZM%'",'$order':'project_id','$limit':'50000'}
raw=fetch(base+urlencode(q),8000000); rawrows=json.loads(raw); assert len(rawrows)<50000
rows=[r for r in rawrows if 'ZM' in [t.strip() for t in r['actions'].split(';')]]
assert rows and len({r['project_id'] for r in rows})==len(rows)
dates=['app_filed_date','certified_referred','approval_date']
def day(r,k):return r.get(k,'')[:10]
def year(r,k):return day(r,k)[:4]
def stats(rs):
    known_disagree=known_agree=undecided=0
    for r in rs:
        y={year(r,k) for k in dates if day(r,k)}
        if len(y)>1:known_disagree+=1
        elif all(day(r,k) for k in dates):known_agree+=1
        else:undecided+=1
    assert known_disagree+known_agree+undecided==len(rs)
    return dict(n=len(rs),known_different=known_disagree,all_known_same=known_agree,undecided=undecided,different_range=[known_disagree,known_disagree+undecided])
complete=[r for r in rows if all(day(r,k) for k in dates)]
ordered=[r for r in complete if day(r,dates[0])<=day(r,dates[1])<=day(r,dates[2])]
out=dict(as_of=datetime.now(timezone.utc).isoformat(),query=base+urlencode(q),source_sha256=digest(raw),raw_n=len(rawrows),all=stats(rows),complete=stats(complete),ordered=stats(ordered),missing={k:sum(not day(r,k) for r in rows) for k in dates},status=dict(Counter(r.get('project_status','missing') for r in rows)),public_status=dict(Counter(r.get('public_status','missing') for r in rows)),out_of_order_ids=[r['project_id'] for r in complete if r not in ordered])
out['transitions']={a+'__'+b:dict(sorted(Counter(year(r,a)+'/'+year(r,b) for r in complete).items())) for a,b in combinations(dates,2)}
pdf_url='https://osf.io/download/6aff233967755055611fc8fb/'
paper={'url':pdf_url,'expected_sha256':'011a51be784756464718d2c93d69db7e52c540b9835b784f5f66de3435bcde81'}
private={}
try:
    pdf=fetch(pdf_url,3500000);assert digest(pdf)==paper['expected_sha256']
    f=Path('/tmp/zoning-source.pdf');f.write_bytes(pdf)
    if shutil.which('pdftotext'):
        pages=subprocess.check_output(['pdftotext','-layout',str(f),'-']).decode().split('\f')
    else:
        import fitz
        with fitz.open(f) as doc:pages=[page.get_text() for page in doc]
    pattern=r'certif|application dat|filing dat|date of fil|project.level|project level|application.level|approval dat|certification|ZAP|propos.{0,8}date'
    paper['page_matches']=[i+1 for i,p in enumerate(pages) if re.search(pattern,p,re.I)];paper['pages_extracted']=len([pg for pg in pages if pg.strip()])
    private['primary-text-private.txt']='\f'.join(pages)
except Exception as e:paper['error']=str(e)[:250]
out['source_paper']=paper
archive=Path('/content/zoning-dates.zip')
with zipfile.ZipFile(archive,'x',zipfile.ZIP_DEFLATED) as z:
    z.writestr('city-source.json',raw);z.writestr('summary.json',js(out));z.writestr('project-ids.json',js([r['project_id'] for r in rows]))
    for k,v in private.items():z.writestr(k,v)
print('archive_sha256 '+digest(archive.read_bytes()))
