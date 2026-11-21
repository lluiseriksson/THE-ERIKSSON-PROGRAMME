"""Integer and rounding-robust stopping limits for the LAGS micro-word calibration."""
from fractions import Fraction as F
from itertools import product
import json,math
def rates(n,per_mille):
    # Include both half endpoints conservatively; report whether either is attainable.
    low=F(2*per_mille-1,2000)*n
    high=F(2*per_mille+1,2000)*n
    if low.denominator==1 or high.denominator==1:raise ValueError('Specify tie convention')
    return range(math.ceil(low),math.floor(high)+1)
def crossing(n,e,p):
    # With at most floor(p*m) added errors, calculate earliest guaranteed pass.
    # For p>0, monotonicity can fail at jumps; use a sharp best-case and a sufficient all-later boundary.
    slack=F(3,20)-p
    if slack<=0:raise ValueError('Inadequate future word accuracy')
    bound=math.ceil((e-F(3,20)*n)/slack)
    left=max(0,math.floor((e-F(3,20)*n-1)/slack))
    def passed(m):return 20*(e+math.floor(p*m))<=3*(n+m)
    first=next(m for m in range(left,bound+1) if passed(m))
    lastfail=max((m for m in range(left,bound+1) if not passed(m)),default=left-1)
    if not passed(first) or not all(passed(m) for m in range(lastfail+1,bound+1)):raise ArithmeticError('gate')
    return dict(first=first,all_later=lastfail+1)
def run():
    a,b=7515,10910;n=a+b
    pairs=[(v,w) for v,w in product(rates(a,426),rates(b,351)) if v+w in rates(n,381)]
    if not pairs:raise ValueError('Incompatible table')
    out={}
    for k,cap,errors in [('first_only',a,set(rates(a,426))),('first_with_whole_table',a,{v for v,w in pairs}),('pooled',n,{v+w for v,w in pairs})]:
        e0,e1=min(errors),max(errors);assert errors==set(range(e0,e1+1))
        out[k]=dict(reference_words=cap,edit_range=[e0,e1],rates={str(p):[crossing(cap,e,p) for e in (e0,e1)] for p in [F(0),F(1,20),F(1,10)]})
    # Counterexample cohort uses four correctly transcribed hypothetical infills with equal word count.
    future=4*10000
    out['six_speaker_completion']=dict(added_words=future,range_agreement=[str(1-F(e,n+future)) for e in reversed(out['pooled']['edit_range'])],perfect_future_passes=20*max(v+w for v,w in pairs)<=3*(n+future),truth='hypothetical feasibility, no transcripts of the remaining four')
    out['pairs']=pairs
    return out
if __name__=='__main__':print(json.dumps(run(),sort_keys=True))
