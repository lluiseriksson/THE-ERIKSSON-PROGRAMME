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
# Exact observational equivalence for the printed monthly aggregates.
from fractions import Fraction as Q
from calendar import monthrange
from statistics import mean
import re
rows=re.findall(r'(?m)^\s*(Sep-25|Oct-25|Nov-25|Dec-25|May-26|Jun-26|Jul-26|Aug-26)\s+([\d.]+)\s+([\d.]+)\s+([\d.,]+)\s+([\d.]+)\s+([\d.]+)%',pages[4])
assert len(rows)==8
C=Q(409)*Q('0.550')
def avg(values):return sum(values,Q(0))/len(values)
data={}
for month,T,_,E,H,P in rows:
    e,t,h,p=[Q(s.replace(',','.')) for s in (E,T,H,P)]
    p/=100
    num={'Sep':9,'Oct':10,'Nov':11,'Dec':12,'May':5,'Jun':6,'Jul':7,'Aug':8}[month[:3]]
    n=monthrange(2000+int(month[-2:]),num)[1]
    u=t/C
    selected=p if abs(e/t-p)>Q('.0005') else e/t
    mismatch=abs(u-h)>Q('.0005')
    # One omitted irradiance day is sufficient in the affected month. All
    # theoretical yields, generation and ratios use every day in both worlds.
    regular=h if mismatch else u
    omitted=n*u-(n-1)*regular
    Htrue=[omitted]+[regular]*(n-1)
    delta=Q(1,2)
    if selected!=e/t:
        # Split the month into floor(n/2) and ceil(n/2) days. Center the
        # two-point contrast exactly, including odd-length months.
        count=n//2
        x=[Q(n-count,n)]*count+[-Q(count,n)]*(n-count)
        assert not mismatch and avg(x)==0
        variance=avg([v*v for v in x])
        Htrue=[u+delta*v for v in x]
        slope=(e/C-u*selected)/(delta*variance)
        ratios=[selected+slope*v for v in x]
    else:ratios=[selected]*n
    true_T=[C*v for v in Htrue];gen=[v*r for v,r in zip(true_T,ratios)]
    assert all(0<hh<10 for hh in Htrue) and all(0<r<1 for r in ratios)
    assert avg(true_T)==t and avg(gen)==e and abs(avg(ratios)-p)<=Q('.0005')
    bias=h-u if mismatch else Q(0)
    A=[v+bias for v in Htrue]
    B=Htrue[1:] if mismatch else Htrue
    assert avg(A)==avg(B) and abs(avg(A)-h)<=Q('.0005')
    data[month]=dict(days=n,daily_true_irradiation=[str(v) for v in Htrue],daily_ratio=[str(r) for r in ratios],daily_true_yield=[str(v) for v in true_T],daily_generation=[str(v) for v in gen],sensor_offset=str(bias),omitted_irradiation_day=1 if mismatch else None,world_A_observed_irradiation_mean=str(avg(A)),world_B_observed_irradiation_mean=str(avg(B)),theoretical_mean=str(t),generation_mean=str(e),ratio_mean=str(avg(ratios)),reported_rounded_values=[T,E,H,P])
assert [m for m,r in data.items() if r['omitted_irradiation_day']]==['Jun-26']
r=data['May-26'];p=Q('0.544');min_p=p-Q('.0005');emin=Q('523.323')-Q('.0005');emax=Q('523.323')+Q('.0005');tmin=Q('965.13')-Q('.005')
floor=min_p-emax/tmin
assert floor>0
# Construct the limiting equality of the rounded-data sensitivity bound on
# closed rounding bins. Moving endpoints into the bins handles tie rules.
n=r['days'];positive=n//2
z=[Q(n-positive,n)]*positive+[-Q(positive,n)]*(n-positive)
var=avg([x*x for x in z]);h0=tmin/C;dH=Q('.5')
hh=[h0+dH*x for x in z];dR=-floor*h0/(dH*var);rr=[min_p+dR*x for x in z]
assert all(x>0 for x in hh) and all(0<x<1 for x in rr)
assert avg([C*v*rate for v,rate in zip(hh,rr)])==emax and avg(rr)==min_p
assert abs(h0-Q('4.290'))<=Q('.0005')
squared_cv=avg([(v-h0)**2 for v in hh])/h0**2
squared_sd=avg([(v-min_p)**2 for v in rr])
assert squared_cv*squared_sd==floor**2
out=dict(source_sha256=sha,dc_capacity=str(C),months=data,may_min_cv_times_sd=str(floor),may_product_percentage_points=float(100*floor),june_sensor_offset=float(Q(data['Jun-26']['sensor_offset'])),june_omitted_day_irradiation=float(Q(data['Jun-26']['daily_true_irradiation'][0])),june_other_days_irradiation=float(Q(data['Jun-26']['daily_true_irradiation'][1])),may_exact_display_ratio=float(Q('523.323')/Q('965.13')),rounding='closed bins at half the last printed unit; sharp infimum under unspecified tie rule',interpretation='Synthetic witnesses for the four audited columns. No assertion about measured daily profiles, actual calibration, missing days or cause of losses.')
with zipfile.ZipFile('/content/archive.zip','w',zipfile.ZIP_DEFLATED) as z:z.writestr('mechanisms.json',json.dumps(out,indent=2,allow_nan=False))
print('archive_sha256',hashlib.sha256(Path('/content/archive.zip').read_bytes()).hexdigest())
