"""Index tables and pages of the pinned, publisher-hosted PDF for a mixture-design audit."""
import hashlib,json,re
from urllib.request import urlopen,Request
import fitz
src=json.load(open('source.json'))
raw=urlopen(Request(src['pdf_url'],headers={'User-Agent':'Research literature audit'}),timeout=30).read()
if hashlib.sha256(raw).hexdigest()!=src['pdf_sha256']:raise ValueError('Publisher PDF changed')
doc=fitz.open(stream=raw,filetype='pdf')
body=[p.get_text(sort=True) for p in doc]
if 'Mixture Design' not in body[0] or '10.3390/foods15224153' not in ''.join(body).replace(' ',''):raise ValueError('Source identity')
hits=[]
for page,txt in enumerate(body,1):
    for line in txt.splitlines():
        if re.match(r'\s*Table\s+[0-9]+\.',line) or re.search(r'(pseudo.components|actual components|coded equation)',line,re.I):
            hits.append([page,' '.join(line.split())[:220]])
pages={str(i):t for i,t in enumerate(body,1) if any(i==page for page,_ in hits)}
print(json.dumps(dict(sha256=src['pdf_sha256'],total_pages=len(doc),headings=hits,pages=pages),ensure_ascii=True))
