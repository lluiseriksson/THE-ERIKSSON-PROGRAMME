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


from math import ceil,floor
# Table D.5 is rotated in the PDF. Values transcribed from the published page.
# H and L contain recall and precision in each method's Table 2 order.
pages=[
 [(7884,61,"80.91 83.43 83.83 82.97 79.60","81.34 83.58 83.77 83.97 82.30"),
  (115842,842,"95.34 98.31 98.76 96.75 94.53","95.81 98.49 98.67 98.67 97.45"),
  (2271,None,"45.13 46.81 47.07 46.15 44.65",""),
  (121455,None,"95.34 98.31 98.75 96.80 94.49","")],
 [(5085,42,"90.84 94.75 95.36 93.35 91.72","92.18 93.34 94.03 92.43 92.05"),
  (119082,994,"94.27 97.56 98.41 95.16 92.77","94.19 96.87 98.21 96.22 95.05"),
  (1627,None,"70.31 84.45 86.17 83.41 82.42",""),
  (122540,None,"94.45 97.62 98.44 95.24 92.86","")]]
assert sha256(data).hexdigest()=='d62c26aca84b2d8c5f6187d14c182b597ae24106c24f52e78f44873aa85d6dd2'
def precision_ok(matches,total_output,rate):
    return total_output>0 and abs(F(100*matches,total_output)-rate)<=F(1,200)
def misses(n,r):
    # Closed half-unit bounds, and verify neither endpoint is a tied integer here.
    a=n*(1-(r+F(1,200))/100);b=n*(1-(r-F(1,200))/100)
    assert a.denominator!=1 and b.denominator!=1
    return range(ceil(a),floor(b)+1)

def overlap_range(H,L,Fcount,M,h,f,x):
    lower=max(0,h+f-M,h-(H-x),f-(Fcount-x))
    upper=min(h,f,x,L-Fcount+x-M+h+f)
    return lower,upper

def realize(rows,flags,pages,high):
    if high:
        assert flags>=pages and flags<=rows<=20*flags
        fs=[flags//pages+(i<flags%pages) for i in range(pages)]
        sizes=fs[:];extra=rows-flags
        for i in range(pages):
            add=min(extra,19*fs[i]);sizes[i]+=add;extra-=add
        assert not extra
    else:
        assert rows>=20*flags+pages
        fs=[flags//pages+(i<flags%pages) for i in range(pages)]
        sizes=[20*f+1 for f in fs];sizes[-1]+=rows-sum(sizes)
    assert sum(sizes)==rows and sum(fs)==flags
    assert all(0<=f<=n and n>=1 and (20*f>=n)==high for f,n in zip(fs,sizes))
    return list(zip(sizes,fs))

def edition(i,table):
    (H,rH,ph),(L,rL,pl),(fc,rF,_),(uc,rU,_)=table
    assert H+L==fc+uc==ref[i]
    hs=[];fs=[]
    for j,name in enumerate(names):
        M=int(years[i][name][0])
        hs.append([h for h in misses(H,rH[j]) if M-h in misses(L,rL[j])])
        fs.append([f for f in misses(fc,rF[j]) if M-f in misses(uc,rU[j])])
        tp=ref[i]-M;output=tp+int(years[i][name][1])
        precH=F(pages[i][0][3].split()[j]);precL=F(pages[i][1][3].split()[j])
        def possible(h):
            t=H-h
            low=ceil(100*t/(precH+F(1,200)));high=floor(100*t/(precH-F(1,200)))
            return any(precision_ok(tp-t,output-o,precL) for o in range(low,high+1))
        hs[-1]=[h for h in hs[-1] if possible(h)]
        assert hs[-1] and fs[-1],(i,j,hs[-1],fs[-1])
    M=int(years[i]['Combined'][0]);best={}
    intervals=[]
    xmin=max(ph,ceil(F(H,20)),fc-(L-pl)//20,fc-L,0)
    for x in range(xmin,min(fc,H)+1):
        ranges=[]
        for j,name in enumerate(names):
            m=int(years[i][name][0])
            choices=[]
            for h in hs[j]:
                for f in fs[j]:
                    low,up=overlap_range(H,L,fc,m,h,f,x)
                    if low<=up:choices.append((h,f,low,up))
            ranges.append(choices)
        if not all(ranges):continue
        for h,f,lo,hi in ranges[2]:
            intervals.append((h+f-hi,h+f-lo))
            for z in {lo,hi}:
                caught=h+f-z;work=H+fc-x
                rec=dict(x=x,h=h,f=f,overlap_missed=z,caught=caught,work=work)
                exp=F(x*f,fc)+F((H-x)*(M-f),uc)
                for k,val in dict(adjusted_excess=h-exp,covered=caught,added=f-z,work=work,yield_per_row=F(caught,work)).items():
                    for direction in ('min','max'):
                        key=k+'_'+direction
                        if key not in best or (val<best[key][0] if direction=='min' else val>best[key][0]):
                            best[key]=(val,rec)
    intervals.sort();first,last=intervals[0]
    for l,h in intervals[1:]:
        assert l<=last+1
        last=max(last,h)
    examples={}
    for k,(v,rec) in best.items():
        x=rec['x'];h=rec['h'];f=rec['f'];z=rec['overlap_missed']
        size=[x,H-x,fc-x,L-fc+x];masks=[z,h-z,f-z,M-h-f+z]
        assert sum(masks)==M and all(0<=m<=s for m,s in zip(masks,size))
        examples[k]=dict(value=str(v),**rec,cell_sizes=size,cell_misses=masks,
            page_sizes_flags_high=realize(H,x,ph,True),page_sizes_flags_low=realize(L,fc-x,pl,False))
    return dict(reference=ref[i],missed=M,high_pages=ph,low_pages=pl,high_rows=H,flagged_rows=fc,
                h_candidates=hs[2],f_candidates=fs[2],covered_integer_interval=[first,last],extrema=examples)

tables=[[(count,list(map(F,r.split())),n_pages) for count,n_pages,r,p in t] for t in pages]
result=dict(pdf_sha256=sha256(data).hexdigest(),source=url,years=[edition(i,t) for i,t in enumerate(tables)])
dest=Path('/content/archive.zip')
with zipfile.ZipFile(dest,'w',zipfile.ZIP_DEFLATED) as z:z.writestr('coverage.json',json.dumps(result,indent=2))
print('archive_sha256',sha256(dest.read_bytes()).hexdigest())
