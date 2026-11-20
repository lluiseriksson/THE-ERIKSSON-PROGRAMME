"""Reconcile A12 tariff totals and invert selected section charges."""
from decimal import Decimal
from fractions import Fraction as F
from pathlib import Path
from io import BytesIO
import re,sys,hashlib,json,subprocess
import requests
try:from pypdf import PdfReader
except ImportError:
    subprocess.run([sys.executable,'-m','pip','install','--quiet','pypdf==5.9.0'],stdout=sys.stderr,check=True)
    from pypdf import PdfReader
def read(n):return json.loads(Path(n).read_bytes())
def pdf_rows(data):
    reader=PdfReader(BytesIO(data))
    lines=[]
    # Pages 3--5 cover the A11/A12 boundary and the corridor in version 88.
    for p in reader.pages[2:5]:lines.extend(p.extract_text(extraction_mode='layout').splitlines())
    out=[]
    for line in lines:
        if not line.strip().startswith('A12-'):continue
        xs=re.findall(r'(?<!\d)(\d+,\d{2,4})(?!\d)',line)
        if len(xs)!=18:raise ValueError(('A12 row layout',line))
        cols=[F(x.replace(',','.')) for x in xs]
        if any(cols[i:i+3]!=cols[i+3:i+6] for i in [0,6,12]):raise ValueError('Day and night differ')
        out.append((line[:line.index(xs[0])].strip(),[cols[i:i+3] for i in [0,6,12]]))
        if 'Innsbruck Ost' in line and 'Innsbruck Mitte' in line:break
    if len(out)!=15 or 'Staatsgrenze Kufstein' not in out[0][0] or 'Innsbruck Mitte' not in out[-1][0]:raise ValueError(('Endpoints',out))
    return out
def clip(poly,a,b,c):
    if not poly:return []
    ans=[];x=poly[-1];sx=a*x[0]+b*x[1]-c
    for y in poly:
        sy=a*y[0]+b*y[1]-c
        if (sx<0 and sy>0) or (sx>0 and sy<0):
            t=sx/(sx-sy);ans.append((x[0]+t*(y[0]-x[0]),x[1]+t*(y[1]-x[1])))
        if sy<=0:ans.append(y)
        x,sx=y,sy
    return ans
def section_inverse(cells,kind):
    # Charges for the component disclosures alone bound L below 100 km here.
    amax=max(x[0][1] for x in cells)
    if amax<=0 or min((a[1]+F(1,20000))/rates[1] for rates,a in cells if rates[1]>0)>=100:raise ValueError('Initial distance box')
    poly=[(F(0),F(0)),(F(100),F(0)),(F(100),F(100))]
    for rates,charges in cells:
        i,a,c=rates
        constraints=[(a,0,charges[1],F(1,20000)),(c,0,charges[2],F(1,20000))]
        if kind=='all':constraints.append((i+a+c,i/4,charges[0],F(1,200)))
        for x,y,v,r in constraints:
            poly=clip(clip(poly,x,y,v+r),-x,-y,-v+r)
    if not poly:return None
    return {name:list(map(str,[min(vals),max(vals)])) for name,vals in [('length',[x for x,y in poly]),('surcharge_length',[y for x,y in poly]),('ordinary_length',[x-y for x,y in poly])]}
source=read('annex-sources.json')['files'];comp=read('components.json')['rows'];corr=read('corridor.json')
matches=[];rawcells=[[] for _ in range(15)];names=[];by_row={}
for code in 'lkjihfedcba g'.replace(' ',''):
    f=source[code];p=Path(code+'.pdf')
    if p.is_file():raw=p.read_bytes()
    else:
        response=requests.get(f['url'],timeout=25);response.raise_for_status();raw=response.content
    if hashlib.sha256(raw).hexdigest()!=f['sha256']:raise ValueError('Annex hash')
    items=pdf_rows(raw)
    idx={'l':0,'k':1,'j':2,'i':3,'h':4,'f':5,'g':5,'e':6,'d':7,'c':7,'b':7,'a':7}[code]
    if not names:names=[x for x,_ in items]
    for ax in range(3):
        row=3*idx+ax;target=F(comp[row]['price'])
        data=[z[ax] for _,z in items];total=sum(c[0] for c in data)
        matches.append(dict(annex=code,row=row,section_sum=str(total),price=str(target),difference=str(total-target)))
        if row in by_row and by_row[row]!=data:raise ValueError(('Grouped euro class differs',code,row))
        if row not in by_row:
            by_row[row]=data;gross,a,c=map(F,comp[row]['components']);rates=[gross*4/5,a,c]
            for j,values in enumerate(data):rawcells[j].append((rates,values))
if len(by_row)!=24 or len(matches)!=36:raise ValueError('Coverage')
out=dict(segment_count=len(names),comparisons=matches,segment_names=names,profiles={str(i):[[str(x) for x in row] for row in v] for i,v in by_row.items()},inverse=[dict(components=section_inverse(z,'components'),all=section_inverse(z,'all')) for z in rawcells])
print(json.dumps(out,indent=2))