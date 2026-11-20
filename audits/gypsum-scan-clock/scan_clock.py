"""Exact minimax error of an affine clock for archived dataset start times."""
from fractions import Fraction as Q
from datetime import datetime, timezone
from itertools import combinations
from pathlib import Path
import json

def need(ok,msg):
    if not ok: raise ValueError(msg)

def millis(delta):
    need(delta.microseconds%1000==0,'Submillisecond timestamp')
    return (delta.days*86400+delta.seconds)*1000+delta.microseconds//1000

def affine_clock(t):
    # A line takes its value at j by interpolating its values at i and k.
    # Hence twice the uniform error bounds every interior interpolation residual.
    best,i,j,k= max((abs(t[b]-Q((c-b)*t[a]+(b-a)*t[c],c-a))/2,a,b,c)
                    for a,b,c in combinations(range(len(t)),3))
    slope=Q(t[k]-t[i],k-i)
    resid=[v-slope*h for h,v in enumerate(t)]
    offset=(max(resid)+min(resid))/2
    actual=max(abs(v-offset) for v in resid)
    need(actual==best,'Three-point lower bound and fitted upper bound differ')
    return dict(max_error_ms=str(best),offset_ms=str(offset),slope_ms=str(slope),lower_witness=[i,j,k])

def analyze(rows):
    ordered=sorted(rows,key=lambda r:r['name'])
    origin=datetime.fromisoformat(ordered[0]['startDate'])
    t=[];end=[];table=[]
    for i,r in enumerate(ordered):
        epoch,num,*label=r['name'].split('_')
        a,b=map(datetime.fromisoformat,[r['startDate'],r['endDate']])
        need(int(num)==i and r['sampleName']=='VA_dirS_08-LR' and b>a,'Run identity or window')
        # The filename encodes the epoch second of the scan command and may
        # precede the recorded start by a second.
        time_ms=millis(a-datetime(1970,1,1,tzinfo=timezone.utc))
        t.append(millis(a-origin));end.append(millis(b-origin))
        table.append(dict(scan=i,id=r['id'],start=r['startDate'],end=r['endDate'],
                          filename_minus_start_ms=int(epoch)*1000-time_ms))
    gaps=[t[k+1]-end[k] for k in range(len(t)-1)]
    need(len(t)==54 and len(set(r['id'] for r in rows))==54 and min(gaps)>=0,'Incomplete or overlapping metadata windows')
    need(affine_clock([0,2,4])['max_error_ms']=='0' and affine_clock([0,1,4])['max_error_ms']=='1/2','Clock controls')
    # Identical endpoint observations with an earlier or later threshold event
    # in the longest uncovered interval and a peak at its midpoint.
    k=max(range(len(gaps)),key=gaps.__getitem__)
    x,y=end[k],t[k+1]
    ordered_times=[Q(3*x+y,4),Q(x+y,2),Q(x+3*y,4)]
    need(x<ordered_times[0]<ordered_times[1]<ordered_times[2]<y,'Indistinguishability witness')
    return dict(first_start=ordered[0]['startDate'],last_start=ordered[-1]['startDate'],
                affine=affine_clock(t),max_gap_after=k,max_gap_ms=gaps[k],
                long_gap_after=[i for i,d in enumerate(gaps) if d>300000],
                short_gap_max_ms=max(d for d in gaps if d<=300000),
                long_gap_min_ms=min(d for d in gaps if d>300000),
                hypothetical_event_times_ms_from_first_start=list(map(str,ordered_times)),
                first_to_last_start_ms=t[-1],rows=table)
if __name__=='__main__':
    print(json.dumps(analyze(json.loads(Path(__file__).with_name('scans.json').read_bytes())),indent=2))

