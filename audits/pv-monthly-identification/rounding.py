from urllib.request import urlopen
from pathlib import Path
import hashlib,subprocess,tempfile,zipfile,json
try:from pypdf import PdfReader
except ImportError:
    import sys
    subprocess.run([sys.executable,'-m','pip','install','--quiet','pypdf==5.9.0'],check=True)
    from pypdf import PdfReader
import io
url='https://aijaset.lppm.unand.ac.id/index.php/aijaset/article/download/378/205'
raw=urlopen(url,timeout=75).read();sha=hashlib.sha256(raw).hexdigest()
assert sha=='b7d3f2aaa44c44fd069bd932cd5080fc6dd77368046aa0e879eaed01775783de' and raw[:5]==b'%PDF-'
r=PdfReader(io.BytesIO(raw))
pages=[p.extract_text(extraction_mode='layout') for p in r.pages]
assert any('54.4' in p for p in pages)
from fractions import Fraction as Q
import re
text=pages[4]
matches=re.findall(r'(?m)^\s*(Sep-25|Oct-25|Nov-25|Dec-25|May-26|Jun-26|Jul-26|Aug-26)\s+([\d.]+)\s+([\d.]+)\s+([\d.,]+)\s+([\d.]+)\s+([\d.]+)%',text)
assert len(matches)==8
data=[]
for month,T,h,E,H,PR in matches:
    t,e,g,p=[Q(s.replace(',','.')) for s in (T,E,H,PR)]
    dt=Q(1,200);de=Q(1,2000) if ',' in E else Q(1,200);dg=Q(1,2000);dp=Q(1,20)
    scale=((t-dt)/(g+dg),(t+dt)/(g-dg))
    ratio=(100*(e-de)/(t+dt),100*(e+de)/(t-dt))
    compatible=(ratio[0]<=p+dp and p-dp<=ratio[1])
    data.append(dict(month=month,printed=[T,E,H,PR],capacity_interval=[float(q) for q in scale],capacity_exact=[str(q) for q in scale],nameplate_compatible=scale[0]<=Q('224.95')<=scale[1],ratio_interval_percent=[float(q) for q in ratio],printed_pr_compatible=compatible))
low=max(data,key=lambda x:Q(x['capacity_exact'][0]));high=min(data,key=lambda x:Q(x['capacity_exact'][1]))
assert Q(low['capacity_exact'][0])>Q(high['capacity_exact'][1])
# Uniform extra recording allowance in irradiation units (kWh/m²) for a fixed
# nameplate to make all eight linear yield identities compatible.
def extra(C):
    return max(max(Q(0),(Q(t)-Q(1,200))/C-(Q(h)+Q(1,2000)),(Q(h)-Q(1,2000))-(Q(t)+Q(1,200))/C) for _,t,_,_,h,_ in matches)
out=dict(source_sha256=sha,source_pdf_page=5,capacity_kWp='409 x 0.550 = 224.95',months=data,incompatible_capacity_pair=[low['month'],high['month']],minimum_separation_kwp=float(Q(low['capacity_exact'][0])-Q(high['capacity_exact'][1])),irradiation_allowance_kwh_m2_at_nameplate=float(extra(Q('224.95'))),mean_ratio_caution='Average daily performance ratios can differ from the ratio of aggregate generation to aggregate theoretical yield.')
with zipfile.ZipFile('/content/archive.zip','w',zipfile.ZIP_DEFLATED) as z:z.writestr('table-check.json',json.dumps(out,indent=2,allow_nan=False))
print('archive_sha256',hashlib.sha256(Path('/content/archive.zip').read_bytes()).hexdigest())
