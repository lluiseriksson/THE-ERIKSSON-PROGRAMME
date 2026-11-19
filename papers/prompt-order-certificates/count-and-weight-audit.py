from pathlib import Path
import hashlib,json,zipfile,itertools
from fractions import Fraction as F
from urllib.request import urlopen
rows=[('GSM8K',1319,656,110,720,16),('SVAMP',1000,748,19,794,20),('ASDIV',2096,769,65,796,14),('GSM-HARD',1319,233,49,612,91),('SingleEq',508,891,54,961,30),('SingleOp',562,919,55,946,36),('AddSub',395,860,62,925,34),('MultiArith',600,959,51,992,48)]
def possibilities(n,m,s,rounded):
    # Use the larger (population SD) finite-sample deviation bound, relaxed from sqrt(2) to 2.
    lo=F(m,10)-F(1,20)-2*F(2*s+1,200)-F(1,20)
    hi=F(m,10)+F(1,20)+2*F(2*s+1,200)+F(1,20)
    candidates=[k for k in range(n+1) if lo<=F(100*k,n)<=hi]
    den=10 if rounded else n
    def scores(k):
        if not rounded:return [100*k]
        q,r=divmod(1000*k,n)
        return [q] if 2*r<n else [q+1] if 2*r>n else [q,q+1]
    values={k:scores(k) for k in candidates}
    result={6:[],9:[]}
    for comb in itertools.combinations_with_replacement(candidates,3):
        for triple in itertools.product(*(values[k] for k in comb)):
            total=sum(triple)
            if abs(20*total-6*m*den)>3*den:continue
            var=3*sum(y*y for y in triple)-total*total
            for divisor in (6,9):
                if (2*s-1)**2*divisor*den**2<=40000*var<=(2*s+1)**2*divisor*den**2:
                    result[divisor].append(comb)
    return {k:sorted(set(v)) for k,v in result.items()}
record={}
for task,n,ma,sa,mb,sb in rows:
    methods={}
    for mode in (False,True):
        a=possibilities(n,ma,sa,mode);b=possibilities(n,mb,sb,mode)
        methods[str(mode)]={}
        for dd in (6,9):
            result={'cot':a[dd],'pal':b[dd]}
            if a[dd] and b[dd]:
                A=max(x[-1] for x in a[dd]);B=min(x[0] for x in b[dd]);L=min(A,n-B)
                assert B>A and L>0
                ratio=F(B-A+L,L)
                # One attaining table (gain, loss, both, neither).
                table=[B-A+L,L,A-L,n-B-L]
                assert sum(table)==n and table[1]+table[2]==A and table[0]+table[2]==B
                result.update(worst={'cot_order':next(x for x in a[dd] if x[-1]==A),'pal_order':next(x for x in b[dd] if x[0]==B),'A':A,'B':B,'gain_loss_both_neither':table,'tie_weight_ratio':str(ratio)})
            methods[str(mode)][str(dd)]=result
    record[task]=methods
# Conservative cross-task guarantee for raw or pre-rounded order scores.
# Upper-bound sqrt(2) by 141422/100000, valid by squaring.
u=F(141422,100000);assert u*u>2
limits={}
for task,n,ma,sa,mb,sb in rows:
    A=F(ma,10)+F(1,20)+u*F(2*sa+1,200)+F(1,20)
    B=F(mb,10)-F(1,20)-u*F(2*sb+1,200)-F(1,20)
    h=min(A,100-B)
    assert B-A>0 and h>0
    limits[task]={'A_upper':str(A),'B_lower':str(B),'ratio_lower':str(1+(B-A)/h)}
data={'rows':rows,'tables':record,'continuous_lower_limits':limits,'definition':'6 = sample SD, 9 = population SD; True = per-order percentages rounded to one decimal before summary, ties allowed either way. Published summary intervals closed.'}
archive=Path('/content/pal-precision.zip')
with zipfile.ZipFile(archive,'x',zipfile.ZIP_DEFLATED) as z:z.writestr('comparison.json',json.dumps(data,sort_keys=True))
print('archive_sha256 '+hashlib.sha256(archive.read_bytes()).hexdigest())
