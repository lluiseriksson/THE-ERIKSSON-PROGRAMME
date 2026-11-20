"""Recover published counts only. No person-level directory records are used."""
from fractions import Fraction as F
from hashlib import sha256
from pathlib import Path
from urllib.request import urlopen
from io import BytesIO
from itertools import combinations
import json,re,zipfile,shutil,subprocess,sys,tempfile

url='https://arxiv.org/pdf/2611.25218v1'
with urlopen(url) as response:data=response.read()
assert data.startswith(b'%PDF-')
def page(n):
    if shutil.which('pdftotext'):
        return subprocess.check_output(['pdftotext','-f',str(n),'-l',str(n),'-layout','-','-'],input=data).decode()
    from importlib.util import find_spec
    if not find_spec('pypdf'):
        subprocess.run([sys.executable,'-m','pip','install','--quiet','pypdf==6.0.0'],check=True)
    from pypdf import PdfReader
    return PdfReader(BytesIO(data)).pages[n-1].extract_text(extraction_mode='layout')
main=page(12);aux=page(27)
names=['MLLM','Parser','Combined','Open LLM','Open OCR-LLM']
def fields(line):
    return [F(x.replace(',','')) for x in re.findall(r'(?<!\w)[0-9][0-9,]*(?:\.\d+)?',line)]
def row(txt,name,size):
    for l in txt.splitlines():
        l=l.strip()
        if l.startswith(name+' ') and len(fields(l[len(name):]))==size:return fields(l[len(name):])
    raise ValueError(('Could not recover row',name,txt[:350]))
ref=[123726,124167]
assert all(f'{v:,}' in main for v in ref)
years=[{} for _ in ref]
for name in names:
    x=row(main,name,8)
    for i in range(2):
        out,matched,pr,rec=x[i*4:i*4+4]
        assert abs(100*matched/out-pr)<=F(1,200) and abs(100*matched/ref[i]-rec)<=F(1,200)
        years[i][name]=(ref[i]-matched,out-matched)
sections=re.split(r'1921\s*\(1,036 analysis pages\)',aux)
assert len(sections)==2
for i,txt in enumerate(sections):
    for name in names[:-1]:
        for l in txt.splitlines():
            l=l.strip()
            if l.startswith(name+' '):
                x=fields(l[len(name):])
                if len(x)>=3 and x[0]>100000:break
        else:raise ValueError(('Missing appendix row',name,i))
        match=x[0]+x[1];assert (ref[i]-match,x[2]-match)==years[i][name]

def winners(rows,price):
    best=min(m+price*e for m,e in rows.values())
    return [k for k,(m,e) in rows.items() if m+price*e==best]
def costs(rows):
    knots={F(0)}
    for (a,b),(c,d) in combinations(rows.values(),2):
        if b!=d and (c-a)/(b-d)>0:knots.add((c-a)/(b-d))
    order=sorted(knots);switches=[]
    for j,x in enumerate(order):
        win=winners(rows,x)
        if len(win)>1:switches.append([x,win])
    return dict(at_zero=winners(rows,F(0)),switches=switches,at_infinity=winners(rows,order[-1]+1))
curves=[costs(y) for y in years]
comparison=[[a-b for a,b in zip(y['Open LLM'],y['Combined'])] for y in years]
(m1,e1),(m2,e2)=comparison
assert m1>0 and m2>0 and e1<0 and e2>0
cut=(e2/ref[1])/(e2/ref[1]-e1/ref[0])
result=dict(source=url,pdf_sha256=sha256(data).hexdigest(),reference=ref,errors=years,curves=curves,open_minus_combined=comparison,share_boundary=cut,raw_pool=costs({k:[a+b for a,b in zip(years[0][k],years[1][k])] for k in names}),appendix_links_checked=8)
dest=Path('/content/archive.zip')
with zipfile.ZipFile(dest,'w',zipfile.ZIP_DEFLATED) as z:z.writestr('agreement.json',json.dumps(result,default=str,indent=2))
print('archive_sha256',sha256(dest.read_bytes()).hexdigest())
