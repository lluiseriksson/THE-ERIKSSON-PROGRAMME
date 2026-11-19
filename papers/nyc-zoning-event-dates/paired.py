from pathlib import Path
import io,json,collections,hashlib,zipfile,re,sys
from urllib.request import urlopen,Request
from urllib.parse import urlencode
def get(url,cap):
    with urlopen(Request(url,headers={'User-Agent':'Programme source reconciliation'}),timeout=55) as f:raw=f.read(cap+1)
    assert len(raw)<=cap
    return raw
def sha(data):return hashlib.sha256(data).hexdigest()
def j(data):return json.dumps(data,indent=2)
q={'$select':'project_id,actions,project_status,public_status,app_filed_date,certified_referred,approval_date','$where':"approval_date >= '2015-01-01T00:00:00' and approval_date < '2025-01-01T00:00:00' and actions like '%ZM%'",'$order':'project_id','$limit':'50000'}
raw=get('https://data.cityofnewyork.us/resource/hgx4-8ukb.json?'+urlencode(q),8000000);assert sha(raw)=='619a87ef785ce4352508e51fa62b5f3b2a049ca426fa03c986e6c07abfcd5e42'
rows=[r for r in json.loads(raw) if 'ZM' in {a.strip() for a in r['actions'].split(';')}]
counts=collections.Counter((r['certified_referred'][:4],r['approval_date'][:4]) for r in rows)
file_year=collections.Counter((r['app_filed_date'][:4],r['approval_date'][:4]) for r in rows if r.get('app_filed_date'))
same=sum(n for (a,b),n in counts.items() if a==b)
result=dict(n=len(rows),certification_approval_changed=len(rows)-same,certification_approval_same=same,filing_approval_changed=sum(n for (a,b),n in file_year.items() if a!=b),filing_approval_known=sum(file_year.values()),certification_approval_matrix={a+'/'+b:n for (a,b),n in sorted(counts.items())})
# Survey aggregate restrictions against the exact returned cohort before considering new estimands.
assert result['n']==126 and sum(counts.values())==126
source='https://osf.io/download/6aff233967755055611fc8fb/'
pdf=get(source,3500000);assert sha(pdf)=='011a51be784756464718d2c93d69db7e52c540b9835b784f5f66de3435bcde81'
meta=json.loads(get('https://pypi.org/pypi/pypdf/5.9.0/json',1000000))
wheel=next(w for w in meta['urls'] if w['filename'].endswith('py3-none-any.whl'))
content=get(wheel['url'],3000000);assert sha(content)==wheel['digests']['sha256']
tmp=Path('/tmp')/wheel['filename'];tmp.write_bytes(content);sys.path.insert(0,str(tmp))
from pypdf import PdfReader
pages=[page.extract_text() for page in PdfReader(io.BytesIO(pdf)).pages]
result['manuscript']={'sha256':sha(pdf),'pages':len(pages),'wheel':wheel['filename'],'wheel_sha256':sha(content)}
archive=Path('/content/paired-years.zip')
with zipfile.ZipFile(archive,'x',zipfile.ZIP_DEFLATED) as z:
    z.writestr('paired.json',j(result));z.writestr('source-text-private.txt','\f'.join(pages))
print('archive_sha256 '+sha(archive.read_bytes()))
