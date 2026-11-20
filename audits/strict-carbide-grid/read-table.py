from pathlib import Path
import json, requests
from bs4 import BeautifulSoup
url='https://arxiv.org/html/2611.25127v1';r=requests.get(url,timeout=20);r.raise_for_status();s=BeautifulSoup(r.content,'html.parser')
rows=[]
for t in ['Sx1.T3','Sx1.T4']:
 for tr in s.find(id=t).select('tbody tr'):
  values=[a.get_text(' ',strip=True) for a in tr.select('td')]
  if len(values)!=10:raise ValueError(values)
  rows.append(dict(rank=int(values[0]),metals=values[1],fractions=values[2:8],E=values[8].split()[-1],T=values[9].split()[-1]))
assert [x['rank'] for x in rows]==list(range(1,101))

Path('table-s1.json').write_text(json.dumps(dict(rows=rows),ensure_ascii=False),encoding='utf-8')
