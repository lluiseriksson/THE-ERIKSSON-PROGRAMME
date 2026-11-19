from fractions import Fraction as F
from itertools import combinations_with_replacement,product
import json,hashlib,zipfile
from pathlib import Path
rows=[('GSM8K',1319,656,110,720,16),('SVAMP',1000,748,19,794,20),('ASDIV',2096,769,65,796,14),('GSM-HARD',1319,233,49,612,91),('SingleEq',508,891,54,961,30),('SingleOp',562,919,55,946,36),('AddSub',395,860,62,925,34),('MultiArith',600,959,51,992,48)]
def integer_ceiling(a,b):return -(-a//b)
def one(n,m,s,rounded,divisor):
    # Loose necessary deviation bound around the printed mean including both rounding operations.
    radius=2*(2*s+1)+20
    lo=max(0,integer_ceiling(n*(20*m-radius),20000))
    hi=min(n,n*(20*m+radius)//20000)
    den=10 if rounded else n
    points=[]
    for k in range(lo,hi+1):
        if not rounded:points.append((k,100*k));continue
        q,r=divmod(1000*k,n)
        if 2*r<=n:points.append((k,q))
        if 2*r>=n:points.append((k,q+1))
    for i,(ka,a) in enumerate(points):
        for j in range(i,len(points)):
            kb,b=points[j]
            low=integer_ceiling(3*den*(2*m-1),20)-a-b
            high=(3*den*(2*m+1))//20-a-b
            for kc,z in points[j:]:
                if z<low:continue
                if z>high:break
                # The same unrounded count has a single rounded value in a deterministic tie rule.
                if (ka==kb and a!=b) or (kb==kc and b!=z):continue
                spread=(a-b)**2+(a-z)**2+(b-z)**2
                assert spread==3*(a*a+b*b+z*z)-(a+b+z)**2
                value=40000*spread
                if (2*s-1)**2*divisor*den**2<=value<=(2*s+1)**2*divisor*den**2:
                    return {'k':[ka,kb,kc],'z':[a,b,z],'scale':den}
    return None
table={}
for name,N,ma,sa,mb,sb in rows:
    row={}
    for rounding in (False,True):
        for dd in (6,9):
            label=('rounded' if rounding else 'raw')+('_sample' if dd==6 else '_population')
            found=None
            for cut in range(N//10+1):
                n=N-cut
                a=one(n,ma,sa,rounding,dd)
                if a is None:continue
                b=one(n,mb,sb,rounding,dd)
                if b is not None:
                    found=dict(excluded=cut,n=n,cot=a,pal=b);break
            row[label]=dict(result=found,checked_through=cut,initial_N=N)
    table[name]=row
out=Path('/content/denominators.zip')
with zipfile.ZipFile(out,'x',zipfile.ZIP_DEFLATED) as z:z.writestr('grid.json',json.dumps(table,sort_keys=True))
print('archive_sha256 '+hashlib.sha256(out.read_bytes()).hexdigest())
