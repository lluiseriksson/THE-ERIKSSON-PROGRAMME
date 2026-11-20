from pathlib import Path
from fractions import Fraction as F
import hashlib, json, subprocess, re, zipfile
import requests
from decimal import Decimal

url='https://www.ecgi.global/sites/default/files/2026-11/fin-1166-2026_greening_on_hold_environmental_political_risk_and_the_reallo_0.pdf'
root=Path('/content')
raw=requests.get(url,timeout=90)
raw.raise_for_status()
assert raw.content.startswith(b'%PDF-')
pdf=root/'source.pdf'
pdf.write_bytes(raw.content)
import sys
subprocess.run([sys.executable,'-m','pip','install','--quiet','--disable-pip-version-check','pypdf==5.9.0'],check=True,timeout=120)
from pypdf import PdfReader
reader=PdfReader(pdf)
def page(number):
    return reader.pages[number-1].extract_text(extraction_mode='layout').replace('−','-')
def row(page_text, prefix, last=False):
    rows=[' '.join(r.strip().split()) for r in page_text.splitlines()]
    match=[i for i,r in enumerate(rows) if r.replace(' ','').startswith(prefix.replace(' ',''))]
    assert len(match)==1,(prefix,[r[:90] for r in rows if prefix[:4] in r])
    j=match[0]
    vals=re.findall(r'[-+]?\d+\.\d+',rows[j+1] if last else rows[j])
    return [F(v) for v in vals]
ga,nt=page(69),page(70)
res={}
for label in ['E-PRisk','ROA','Debt Ratio','log(Market-to-Book)']:
    v=row(ga,label);ab=row(nt,label)
    g=v[-1];n,t=ab[-2:] if label!='E-PRisk' else (ab[1],ab[3])
    diff=t-g-n
    res[label]=dict(green=str(g),non_green=str(n),total=str(t),discrepancy=str(diff),exceeds_rounding=abs(diff)>F(15,1000))
assert not res['E-PRisk']['exceeds_rounding']
assert all(res[l]['exceeds_rounding'] for l in ['ROA','Debt Ratio','log(Market-to-Book)'])
assert ga.count('2,826')>=7 and nt.count('2,826')>=4
tg=abs(row(ga,'E-PRisk',True)[-1])
tn=abs(row(nt,'E-PRisk',True)[1])
assert (tg,tn)==(4,F('2.05'))
n=F(res['E-PRisk']['non_green']);d=-F(res['E-PRisk']['green'])
h=F('.005');z=F('1.96')
def limits(n,d,tn,tg):
    return n/d*(1-z/tn)/(1+z/tg),n/d*(1+z/tn)/(1-z/tg)
nom=limits(n,d,tn,tg)
lo=limits(n-h,d+h,tn-h,tg-h)[0]
hi=limits(n+h,d-h,tn-h,tg-h)[1]
assert 0<lo<nom[0]<1<nom[1]<hi<3
assert all(n-d*r == sign*z*(n/tn + r*d/tg) for r,sign in zip(nom,[1,-1]))
out=dict(pdf_sha256=hashlib.sha256(raw.content).hexdigest(),url=url,physical_pages=[69,70],rows=res,t_absolute=[str(tn),str(tg)],critical_value=str(z),point=str(n/d),nominal_endpoints=list(map(str,nom)),rounding_outer_endpoints=[str(lo),str(hi)],outer_decimals=[float(lo),float(hi)],nominal_decimals=list(map(float,nom)))
with zipfile.ZipFile(root/'archive.zip','w',zipfile.ZIP_DEFLATED) as archive: archive.writestr('audit.json',json.dumps(out,indent=2))
print('archive_sha256',hashlib.sha256((root/'archive.zip').read_bytes()).hexdigest())
