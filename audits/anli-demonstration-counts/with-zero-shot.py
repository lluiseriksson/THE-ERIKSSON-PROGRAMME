"""Compute the macro-F1 regret versus example-count frontier, including zero-shot."""
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
        rows.append((cells[0],[(F(point),int(k)) for point,k in matches]+[(F(cells[1]),0)]))
assert len(rows)==6 and len(set(n for n,_ in rows))==6
loss=[[max(v for v,k in row)-v for v,k in row] for name,row in rows]
counts=[[F(k) for _,k in row] for _,row in rows]
names=[n for n,_ in rows]
def dot(x,y):return sum(a*b for a,b in zip(x,y))

def certified_frontier(regret,allowed,cutoff=F(8)):
    # Parametric LP: keep only bases with a dual certificate on all allowed columns.
    m=len(regret);constraints=regret+counts
    pieces=[]
    for num in range(1,len(allowed)+1):
        for support in combinations(allowed,num):
            for active_rows in combinations(range(2*m),num):
                if max(active_rows)<m:continue
                # Cost multiplier sum = 1; Lagrangian column equalities on the support.
                system=[[F(i>=m) for i in active_rows]+[F(1)]]
                for j in support[1:]:
                    system.append([constraints[i][j]-constraints[i][support[0]] for i in active_rows]+[F(0)])
                dual=solve_system(system)
                if dual is None or min(dual)<0:continue
                columns=[sum(y*constraints[i][j] for y,i in zip(dual,active_rows)) for j in range(len(loss[0]))]
                if any(columns[j]<columns[support[0]] for j in allowed):continue
                def primal(r):
                    sys=[[constraints[i][j] for j in support]+[-F(i>=m),r if i<m else F(0)] for i in active_rows]
                    return solve_system(sys+[[F(1)]*num+[F(0),F(1)]])
                vals=[primal(r) for r in [F(0),F(1)]]
                assert all(v is not None for v in vals)
                def slacks(v,r):
                    p=[v[support.index(j)] if j in support else F(0) for j in range(len(loss[0]))]
                    z=v[-1]
                    assert z==columns[support[0]]-r*sum(y for i,y in zip(active_rows,dual) if i<m)
                    return p+[r-dot(row,p) for row in regret]+[z-dot(row,p) for row in counts]
                v0,v1=vals;l=F(0);h=cutoff
                for a,b in zip(slacks(v0,F(0)),slacks(v1,F(1))):
                    d=b-a
                    if d>0:l=max(l,-a/d)
                    elif d<0:h=min(h,-a/d)
                    elif a<0:h=F(-1);break
                if l<=h:
                    pieces.append(dict(l=l,h=h,support=support,rows=active_rows,dual=dual,base=v0,slope=[v-u for u,v in zip(v0,v1)]))
    return pieces

def at(pieces,r):
    matches=[]
    for v in pieces:
        if v['l']<=r<=v['h']:
            sol=[x+r*y for x,y in zip(v['base'],v['slope'])]
            p=[sol[v['support'].index(j)] if j in v['support'] else F(0) for j in range(len(loss[0]))]
            matches.append(dict(p=p,z=sol[-1],rows=v['rows'],dual=v['dual']))
    assert len(set(x['z'] for x in matches))<=1
    return matches[0] if matches else None

def summarize(loss):
    cols=tuple(range(len(loss[0])))
    pieces=certified_frontier(loss,cols)
    endpoints=sorted(set(x[k] for x in pieces for k in ('l','h')))
    for l,h in zip(endpoints,endpoints[1:]):
        assert at(pieces,(l+h)/2) is not None
    # Contiguous pieces with identical dual cost lines describe one frontier segment.
    lines={}
    for v in pieces:
        if v['l']<v['h']:
            line=v['base'][-1],v['slope'][-1]
            if line in lines:
                old=lines[line];lines[line]=(min(old[0],v['l']),max(old[1],v['h']))
            else:lines[line]=(v['l'],v['h'])
    bounds=sorted(set(max(row[j] for row in counts) for j in cols))
    caps=[]
    for cap in bounds:
        permitted=tuple(j for j in cols if max(row[j] for row in counts)<=cap)
        reduced=pieces if permitted==cols else certified_frontier(loss,permitted)
        caps.append(dict(cap=cap,allowed=permitted,one=at(reduced,F(1)),min_regret=min((x['l'] for x in reduced),default=None)))
    return dict(one=at(pieces,F(1)),segments=sorted([dict(lo=l,hi=h,intercept=c,slope=s) for (c,s),(l,h) in lines.items()],key=lambda v:v['lo']),bases=pieces,caps=caps)

# All row winners are unique throughout the rounding boxes. For fixed mix, the
# largest regret raises the best cell by 0.005 and lowers every other by 0.005.
assert all(row[4]>F(11,200) for row in loss)
assert all(sum(x==0 for x in row)==1 and min(x for x in row if x)>F(1,100) for row in loss)
robust=[[v+(F(11,200) if j==4 else F(1,100)) if v else v for j,v in enumerate(row)] for row in loss]
result=dict(url=url,html_sha256=sha256(raw).hexdigest(),names=names,table=rows,
            nominal=summarize(loss),rounded=summarize(robust))
dest=Path('/content/archive.zip')
with zipfile.ZipFile(dest,'w',zipfile.ZIP_DEFLATED) as z:z.writestr('frontier.json',json.dumps(result,default=str,indent=2))
print('archive_sha256',sha256(dest.read_bytes()).hexdigest())
