from pathlib import Path
from fractions import Fraction as F
from urllib.request import urlopen
from math import isqrt
import io, json, hashlib, re, zipfile, subprocess, shutil, sys

pin="f81ca2a9777f002f98a6b4d0f10b61bd5c8feb02"
pdf="https://proceedings.mlr.press/v202/gao23f/gao23f.pdf"
expected="9f4e97fd779659f8d244b2ab1e108f496368a3ed91776b8519670428a63f7be4"
rows=[
 ("GSM8K","gsm",656,110,720,16),("SVAMP","svamp",748,19,794,20),
 ("ASDIV","asdiv",769,65,796,14),("GSM-HARD","gsmhardv2",233,49,612,91),
 ("SingleEq","mawpssingleeq",891,54,961,30),("SingleOp","mawpssingleop",919,55,946,36),
 ("AddSub","mawpsaddsub",860,62,925,34),("MultiArith","mawpsmultiarith",959,51,992,48)]
def fetch(u):
    with urlopen(u,timeout=30) as r:data=r.read(20000001)
    assert len(data)<20000001
    return data
def ceildiv(a,b):return -(-a//b)
def table_page(raw):
    p=Path('/content/pal-primary.pdf');p.write_bytes(raw)
    if shutil.which('pdftotext'):
        return subprocess.check_output(['pdftotext','-f','19','-l','19','-layout',str(p),'-']).decode()
    try:from pypdf import PdfReader
    except ImportError:
        subprocess.run([sys.executable,'-m','pip','-q','install','pypdf==5.9.0'],check=True)
        from pypdf import PdfReader
    return PdfReader(io.BytesIO(raw)).pages[18].extract_text(extraction_mode='layout')
def possible(n,mu,sd,den):
    totals=range(ceildiv(3*n*(2*mu-1),2000),3*n*(2*mu+1)//2000+1)
    valid=[]
    for total in totals:
        # For either divisor, all observations lie within 2 upper SDs of their mean.
        rad=ceildiv(n*(2*sd+1),10000)+2
        for lo in range(max(0,total//3-rad),total//3+1):
            for hi in range((total+2)//3,min(n,total//3+rad)+1):
                mid=total-lo-hi
                if not lo<=mid<=hi:continue
                spread=3*(lo**2+mid**2+hi**2)-total**2
                val=400000000*spread
                if (2*sd-1)**2*den*n*n<=val<=(2*sd+1)**2*den*n*n:
                    valid.append([lo,mid,hi])
    return valid
def digest(z):return hashlib.sha256(z).hexdigest()
def run():
    primary=fetch(pdf);assert digest(primary)==expected
    t=table_page(primary);norm=' '.join(t.split())
    data=[]
    for label,file,m0,s0,m1,s1 in rows:
        seq=' '.join([f'{m0/10:.1f}',f'{s0/100:.2f}',f'{m1/10:.1f}',f'{s1/100:.2f}'])
        assert seq in norm,(label,seq,norm[:1800])
        raw=fetch(f'https://raw.githubusercontent.com/reasoning-machines/pal/{pin}/datasets/{file}.jsonl')
        items=[json.loads(line) for line in raw.splitlines() if line.strip()]
        n=len(items);assert n>0
        d=F(m1-m0-1,10);sd=F(s0+s1+1,100)
        # Exact lower bound rounded down to .001 percentage point.
        # ceil(sqrt(2)*1000*sd) is computed entirely with integers.
        squared=2*(1000*sd)**2;u=isqrt(squared.numerator//squared.denominator)
        if u*u<squared:u+=1
        floor=int(d*1000)-u
        grid={}
        for conv,den in [('population',9),('sample',6)]:
            left=possible(n,m0,s0,den);right=possible(n,m1,s1,den)
            grid[conv]=dict(cot=left,pal=right,gap_counts=(min(x[0] for x in right)-max(x[2] for x in left)) if left and right else None)
        data.append(dict(task=label,file=file,n=n,input_sha256=digest(raw),row=[m0,s0,m1,s1],gap_lower_thousandths_pp=floor,grid=grid))
    return dict(table=9,page=19,pdf=pdf,pdf_sha256=expected,repository_pin=pin,results=data,scope='three published prompt-order observations; integer feasibility assumes the exact file of n rows and unrounded per-order percentages',table1_vs_9_gsmhard_cot=['23.1','23.3'])
res=run()
archive=Path('/content/pal-prompt-audit.zip')
with zipfile.ZipFile(archive,'x',zipfile.ZIP_DEFLATED) as z:z.writestr('result.json',json.dumps(res,sort_keys=True))
print('archive_sha256 '+digest(archive.read_bytes()))
