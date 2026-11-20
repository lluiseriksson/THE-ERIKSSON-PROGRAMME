"""Run with python a12-inputs.py path/to/release.zip path/to/ASFINAG-page.html."""
import json,sys,zipfile
from pathlib import Path
from bs4 import BeautifulSoup
with zipfile.ZipFile(sys.argv[1]) as z:
    p,=[p for p in z.namelist() if p.endswith('/tariffs/data/at/at-2026-01-01.orct.json')]
    Path('at.json').write_bytes(z.read(p))
s=BeautifulSoup(Path(sys.argv[2]).read_bytes(),'html.parser')
t,=[t for t in s.select('table') if '0,5724' in t.get_text()]
rows=[[c.get_text(' ',strip=True) for c in tr.select('th,td')] for tr in t.select('tr')]
rows=[r for r in rows if len(r)==5 and r[0].startswith('CO₂-Emissionsklasse')]
if len(rows)!=8:raise ValueError('Expected eight truck rows')
Path('operator.json').write_text(json.dumps({'rows':rows},ensure_ascii=False),encoding='utf-8')