"""Recompute the table-3 design game, using exact fractions on reported values."""
from pathlib import Path
from urllib.request import urlopen
from itertools import combinations
from fractions import Fraction as F
from hashlib import sha256
from bs4 import BeautifulSoup
import json,zipfile

def solve_system(rows):
    n=len(rows)
    for i in range(n):
        j=next((j for j in range(i,n) if rows[j][i]),None)
        if j is None:return None
        rows[i],rows[j]=rows[j],rows[i]
        rows[i]=[v/rows[i][i] for v in rows[i]]
        for j in range(n):
            if j!=i:
                mul=rows[j][i]
                rows[j]=[x-mul*y for x,y in zip(rows[j],rows[i])]
    return [row[-1] for row in rows]

def active(matrix,actions,constraints):
    n=len(actions)
    rows=[[F(matrix[i][j]) for j in actions]+[F(-1),F(0)] for i in constraints]
    sol=solve_system(rows+[[F(1)]*n+[F(0),F(1)]])
    if sol is None or min(sol[:-1])<0:return None
    return [sol[actions.index(j)] if j in actions else F(0) for j in range(len(matrix[0]))],sol[-1]

url='https://arxiv.org/html/2611.24971v1'
with urlopen(url) as r:raw=r.read()
dom=BeautifulSoup(raw,'html.parser')
table=dom.find(id='S3.T3')
if table is None:
    table=next(e for e in dom.find_all('figure') if 'Table 3:' in e.get_text(' ',strip=True) and 'macro-F1' in e.get_text(' ',strip=True))
rows=[]
for tr in table.find_all('tr'):
    cells=[' '.join(c.stripped_strings) for c in tr.find_all(['td','th'])]
    if cells and cells[0] in ('Qwen 30B','Qwen 4B','Phi-4-mini','Phi-4','Gemma 27B','Gemma 4B'):
        import re
        matches=re.findall(r'(\d+\.\d+)\s*\(\s*(\d+)\s*\)',' '.join(cells[2:]))
        assert len(matches)==4,(cells,matches)
        rows.append((cells[0],[(F(point),int(k)) for point,k in matches]))
assert len(rows)==6 and len(set(n for n,_ in rows))==6
loss=[[max(v for v,k in row)-v for v,k in row] for name,row in rows]
dual=list(map(list,zip(*loss)))
pure=[max(col) for col in dual]
def dot(a,b):return sum(x*y for x,y in zip(a,b))
def saddle():
    for size in range(1,5):
        for js in combinations(range(4),size):
            for ii in combinations(range(6),size):
                p=active(loss,js,ii);q=active(dual,ii,js)
                if p and q and p[1]==q[1] and max(dot(row,p[0]) for row in loss)==p[1] and min(dot(col,q[0]) for col in dual)==p[1]:
                    return p[0],q[0],p[1]
    raise ValueError('No certified saddle')
p,q,value=saddle()
result=dict(primary=url,html_sha256=sha256(raw).hexdigest(),models=[x for x,_ in rows],table=[[(str(v),k) for v,k in row] for _,row in rows],pure=[str(v) for v in pure],mix=list(map(str,p)),dual=list(map(str,q)),value=str(value),guaranteed_gain_under_rounding=str(min(pure)-value-F(2,100)))
dest=Path('/content/archive.zip')
with zipfile.ZipFile(dest,'w',zipfile.ZIP_DEFLATED) as z:z.writestr('game.json',json.dumps(result,indent=2))
print('archive_sha256',sha256(dest.read_bytes()).hexdigest())
