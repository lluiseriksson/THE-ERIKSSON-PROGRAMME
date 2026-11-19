from fractions import Fraction as F
from math import isqrt
from pathlib import Path
import json,zipfile,hashlib
rows=[('GSM8K',1319,656,110,720,16),('SVAMP',1000,748,19,794,20),('ASDIV',2096,769,65,796,14),('GSM-HARD',1319,233,49,612,91),('SingleEq',508,891,54,961,30),('SingleOp',562,919,55,946,36),('AddSub',395,860,62,925,34),('MultiArith',600,959,51,992,48)]
def ceil(a,b):return -(-a//b)
def solve(n,m,s,mode,d):
    # The reported percentages before aggregation are z*unit, where z is an integer.
    num,den=(1,10) if mode else (100,n)
    bound=den*(2*s+1)*3//(200*num)+1
    for u in range(bound+1):
        for v in range(bound+1):
            H=u*u+u*v+v*v
            if not (2*s-1)**2*d*den**2<=80000*H*num**2<=(2*s+1)**2*d*den**2:continue
            # Mean = (3i+2u+v)*num/(3den).
            offset=20*num*(2*u+v)
            imin=ceil(3*den*(2*m-1)-offset,60*num)
            imax=(3*den*(2*m+1)-offset)//(60*num)
            for i in range(imin,imax+1):
                zs=[i,i+u,i+u+v]
                if min(zs)<0 or max(zs)*num>100*den:continue
                if not mode:return zs
                counts=[]
                for zz in zs:
                    a=max(0,ceil((2*zz-1)*n,2000));b=min(n,(2*zz+1)*n//2000)
                    matching=[k for k in range(a,b+1) if round(F(1000*k,n))==zz]
                    if not matching:break
                    counts.append(matching[0])
                if len(counts)==3:return counts
    return None
output={}
for task,N,ma,sa,mb,sb in rows:
    out={}
    for mode in [False,True]:
        for d in [6,9]:
            key=('rounded' if mode else 'raw')+('_sample' if d==6 else '_population')
            for cut in range(N//10+1):
                n=N-cut;a=solve(n,ma,sa,mode,d);b=solve(n,mb,sb,mode,d)
                if a is not None and b is not None:
                    out[key]=[cut,a,b];break
            else:out[key]=None
    output[task]=out
# For SD of rounded-to-one-decimal scores, the relevant H intervals contain one integer.
def candidates(sd,d):
    return [h for h in range(1000) if (2*sd-1)**2*d*100<=80000*h<=(2*sd+1)**2*d*100]
assert candidates(20,9)==[18] and candidates(19,6)==[11]
assert all((u*u+u*v+v*v)%4!=2 for u in range(4) for v in range(4))
assert all((u*u+u*v+v*v)%3!=2 for u in range(3) for v in range(3))
out=Path('/content/lattice.zip')
with zipfile.ZipFile(out,'x',zipfile.ZIP_DEFLATED) as z:z.writestr('verification.json',json.dumps({'minimal_cuts':output,'infeasible_rounded_sd':{'population_0.20':18,'sample_0.19':11},'prior_rounding':'nearest, half to even'}))
print('archive_sha256 '+hashlib.sha256(out.read_bytes()).hexdigest())
