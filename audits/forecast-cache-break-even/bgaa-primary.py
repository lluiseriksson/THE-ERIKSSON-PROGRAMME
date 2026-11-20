"""Extract factual timing cells from Table 8 of the authors' versioned HTML."""
import hashlib
import json
from pathlib import Path
from urllib.request import urlopen
from bs4 import BeautifulSoup

source = 'https://arxiv.org/html/2611.25171v1'
with urlopen(source, timeout=30) as response:
    raw = response.read()
table = BeautifulSoup(raw, 'html.parser').find(id='A3.T8')
rows = []
for tr in table.select('tr'):
    cells = [td.get_text(' ', strip=True) for td in tr.select(':scope > td,:scope > th')]
    if len(cells)==10 and cells[1].replace(',','').isdigit():
        rows.append(cells)
    elif len(cells)==3 and cells[0].replace(',','').isdigit():
        rows.append(cells)
if len(rows)!=21:
    raise ValueError('Expected 14 small-model rows and 7 baseline latency rows')
result = dict(url=source+'#A3.T8', published='2026-11-18', identifier='arXiv:2611.25171v1',
              html_sha256=hashlib.sha256(raw).hexdigest(), rows=rows)
print(json.dumps(result,indent=2,ensure_ascii=False))
