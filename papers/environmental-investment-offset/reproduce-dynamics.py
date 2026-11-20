import hashlib, io, json, re, subprocess, sys, zipfile
from fractions import Fraction as F
from pathlib import Path

import requests

url = 'https://www.ecgi.global/sites/default/files/2026-11/fin-1166-2026_greening_on_hold_environmental_political_risk_and_the_reallo_0.pdf'
pdf = requests.get(url, timeout=90)
pdf.raise_for_status()
digest = hashlib.sha256(pdf.content).hexdigest()
assert digest == '81eb23297a51050a88da84ec98064118e8d2369acbaab9c1a0153650f261cf09'
subprocess.run([sys.executable, '-m', 'pip', 'install', '-q', '--disable-pip-version-check', 'pypdf==5.9.0'], check=True, timeout=120)
from pypdf import PdfReader

reader = PdfReader(io.BytesIO(pdf.content))
rows = [' '.join(s.replace('−','-').split()) for s in reader.pages[48].extract_text(extraction_mode='layout').splitlines() if s.strip()]
# The PDF stores the two panels in rotated coordinates. The layout extractor
# places panel B then panel A on each row. Separate both at their own labels.
def vals(line):
    return [F(x) for x in re.findall(r'-?\d+\.\d+', line)]
ix=[i for i,line in enumerate(rows) if line.startswith('E-PRisk') and line.count('E-PRisk')==2]
assert len(ix)==2,[(i,rows[i]) for i in ix]
g,n,total,ts=[],[],[],[]
for i in ix:
    _,non_and_total,green=rows[i].split('E-PRisk')
    panel_b,panel_a=vals(non_and_total),vals(green)
    assert len(panel_b)==6 and len(panel_a)>=6,(panel_b,panel_a)
    n.append(panel_b[0])
    total.append(panel_b[3])
    g.append(panel_a[3])
    trow=re.findall(r'\(\s*([-+]?\s*\d+\.\d+)\s*\)', rows[i+1])
    assert len(trow)==12,(rows[i+1],trow)
    parts=[[F(v.replace(' ','')) for v in trow[start:start+6]] for start in (0,6)]
    # The text layer stores the two horizontal halves in a different order
    # on the first t row. Identify panel A by both of its first two cells.
    anchor=(F('-1.97'),F('.23')) if len(ts)==0 else (F('7.46'),F('-.56'))
    green_stats=[row for row in parts if tuple(row[:2])==anchor]
    assert len(green_stats)==1,(parts,anchor)
    ts.append(green_stats[0][3])
assert g==[F('-.62'),F('1.07')] and ts==[F('-3.74'),F('8.41')], (g,ts)
assert n==[F('.61'),F('-1.22')] and total==[F('-.21'),F('-.09')], (n,total)
residuals=[t-x-y for t,x,y in zip(total,g,n)]
assert all(abs(x)>F('.015') for x in residuals)
z=F('1.96')
h=F('.005')
def interval(a,b,ta,tb):
    radius=z*(a/ta+b/tb)
    return b-a-radius,b-a+radius
nominal=interval(-g[0],g[1],-ts[0],ts[1])
# b-a-z(a/u+b/v) increases in b when v>z and decreases in a.
# b-a+z(a/u+b/v) decreases in a when u>z and increases in b.
low=interval(-g[0]+h,g[1]-h,-ts[0]-h,ts[1]-h)[0]
high=interval(-g[0]-h,g[1]+h,-ts[0]-h,ts[1]-h)[1]
assert low<nominal[0]<0<nominal[1]<high
a,b=-g[0],g[1]
sa,sb=a/(-ts[0]),b/ts[1]
rho=((b-a)**2/z**2-sa**2-sb**2)/(2*sa*sb)
assert -1<rho<1
def pair(x):
    return [str(n) for n in x]
out=dict(pdf_sha256=digest,physical_page=49,green=pair(g),non_green=pair(n),total=pair(total),signed_green_t=pair(ts),additivity_residuals=pair(residuals),point_sum=str(sum(g)),interval=pair(nominal),rounded_outer=pair([low,high]),rounded_decimals=[float(low),float(high)],max_correlation_for_positive_sum_nominal=float(rho))
with zipfile.ZipFile('/content/archive.zip','w',zipfile.ZIP_DEFLATED) as zf:
    zf.writestr('dynamic.json', json.dumps(out,indent=2))
print('archive_sha256',hashlib.sha256(Path('/content/archive.zip').read_bytes()).hexdigest())
