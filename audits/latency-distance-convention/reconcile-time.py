"""Independent replay from the authors' HTML, diagnostic offsets and reweighting."""
from urllib.request import Request,urlopen
import re, json, hashlib
from itertools import product
from fractions import Fraction as F
from decimal import Decimal as D
from math import isqrt
from bs4 import BeautifulSoup
source='https://arxiv.org/html/2610.39621v2'
raw=urlopen(Request(source,headers={'User-Agent':'Research literature audit'}),timeout=25).read()
soup=BeautifulSoup(raw,'html.parser')
def number(tex):
    m=re.fullmatch(r'([0-9]+(?:\.[0-9]+)?)(?:\\times\s*10\^\{(-?\d+)\})?',tex.strip())
    if not m: raise ValueError(tex)
    exponent=int(m[2] or 0)
    quantum=F(10)**(exponent+D(m[1]).as_tuple().exponent)
    return F(m[1])*F(10)**exponent,quantum/2
table=soup.find(id='S4.T2')
pars=[]
for row in table.select('tr')[2:]:
    cells=row.select('td,th')
    pairs=[number(c.select_one('math')['alttext']) for c in cells[1:3]]
    pars.append((pairs[1][0]-pairs[0][0],pairs[0][1]+pairs[1][1]))
if len(pars)!=5:raise ValueError('Table 2')
rivals=[]
for row in soup.find(id='S4.T3').select('tr')[1:]:
    cells=row.select('td,th')
    if not cells:continue
    m=cells[-1].select_one('math')
    rivals.append(F((m['alttext'] if m else cells[-1].get_text(strip=True)).rstrip('.')))
if len(rivals)!=15 or sorted(rivals)[:2]!=[1870,3367]:raise ValueError('Table 3')
sec=soup.find(id='S3.SS1').get_text(' ',strip=True)
for phrase in ['10,000 and 200,000','step size of 10,000','500, 1,000, 1,500, and 2,000']:
    if phrase not in sec:raise ValueError(phrase)
ref=json.load(open('fuente.json'))
if [x[0] for x in pars[1:]]!=[F(l)-F(a) for a,l in zip(ref['api'],ref['local'])] or [x[1] for x in pars[1:]]!=[F(l)+F(a) for a,l in zip(ref['api_halfwidth'],ref['local_halfwidth'])]:raise ValueError('Independent source transcription differs')
points=list(product(range(10000,200001,10000),range(500,2001,500)))
def residual(coef,i,o):return sum(a*b for a,b in zip(coef,(1,i,i*i,o,i*o)))
def mean(a): return sum(a)/len(a)
def sqrt_bounds(v):
    n=isqrt(v.numerator*10**12//v.denominator)
    return [n/1e6,(n+1)/1e6]
offset=pars[0][0]
central=[F(0)]+[v for v,h in pars[1:]]
values=[residual(central,*p) for p in points]
target=rivals[0]**2
results={}
for intercept in (False,True):
    center=[(v if intercept or k else F(0)) for k,(v,h) in enumerate(pars)]
    widths=[(h if intercept or k else F(0)) for k,(v,h) in enumerate(pars)]
    box=[sorted(set((v-h,v+h))) for v,h in zip(center,widths)]
    def loss(c):return mean([residual(c,*p)**2 for p in points])
    def gradient(c):
        err=[residual(c,*p) for p in points]
        return [mean([e*x[k] for e,x in zip(err,[(1,i,i*i,o,i*o) for i,o in points])]) for k in range(5)]
    vertices=list(product(*box)); hi=max(loss(v) for v in vertices)
    # For a convex quadratic, the first-order box optimality conditions certify a global minimizer.
    minima=[loss(v) for v in vertices if all(len(ax)==1 or (g>=0 if val==ax[0] else g<=0) for g,val,ax in zip(gradient(v),v,box))]
    if not minima:raise ValueError('Minimum is not certified at a vertex')
    lo=min(minima)
    results['intercepts_included' if intercept else 'zero_intercepts']=dict(center=sqrt_bounds(loss(center)),sharp_range=[sqrt_bounds(lo)[0],sqrt_bounds(hi)[1]],min_squared=str(lo),max_squared=str(hi),compatible=(lo<=(rivals[0]+F(1,2))**2 and hi>=(rivals[0]-F(1,2))**2))
squares=[e*e for e in values];avg=mean(squares);loss_min=min(squares);loss_max=max(squares)
# Minimum fraction of uniform requests replaced by arbitrary requests for central coefficients.
replace=(avg-target)/(avg-loss_min)
# Minimum total variation: transfer uniform mass from largest loss to a minimum-loss cell.
need=avg-target;tv=F(0);donors=[]
for k in sorted(range(len(points)),key=lambda i:-squares[i]):
    width=squares[k]-loss_min
    if not need:break
    amount=min(F(1,len(points)),need/width)
    donors.append([list(points[k]),str(amount)]);need-=amount*width;tv+=amount
if need or (1-replace)*avg+replace*loss_min!=target:raise ValueError('Weight witness')
lo=F(results['zero_intercepts']['min_squared']);target_hi=(rivals[0]+F(1,2))**2
uppercell=max((abs(y)+residual([0]+[h for _,h in pars[1:]],*p))**2 for y,p in zip(values,points))
results['weights']=dict(nominal_target_ms=1870,minimum_contamination_nominal=str(replace),minimum_tv_nominal=str(tv),uniform_mass_donors=donors,recipient=list(points[squares.index(loss_min)]),minimum_contamination_all_roundings_lower=str(1-target_hi/lo),minimum_tv_all_roundings_lower=str((lo-target_hi)/uppercell),nominal_contamination=float(replace),nominal_tv=float(tv),robust_contamination_lower=float(1-target_hi/lo),robust_tv_lower=float((lo-target_hi)/uppercell))
print(json.dumps(dict(primary_sha256=hashlib.sha256(raw).hexdigest(),url=source,offset_ms=str(offset),results=results),indent=2,sort_keys=True))