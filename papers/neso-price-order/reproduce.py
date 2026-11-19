"""Reproduce the July--September 2026 DFS tables using the archived operator data."""
import csv
import hashlib
import io
import json
import re
from collections import defaultdict
from datetime import datetime
from decimal import Decimal as D
from pathlib import Path
from zipfile import ZipFile

ROOT = Path(__file__).resolve().parent
PINS = {
    'official-snapshot.csv': ('settlement.zip', '8817edc41c28f16ed2c4d3eaa378256dc5f5da8424d6c792c11436f525da930c'),
    'req.csv': ('procurement.zip', '4be63895f124585cf5446bbb4299e03dc0a7d8bf96f5ecdcc782c42f87119d5f'),
    'bids.csv': ('procurement.zip', '02d849dbc7ee8303307062ac4184b6963f5d205649074a006bb62f963d4f96a2'),
}

def source(name):
    archive, digest = PINS[name]
    with ZipFile(ROOT / archive) as z:
        raw = z.read(name)
    if hashlib.sha256(raw).hexdigest() != digest:
        raise ValueError('Source changed: ' + name)
    return csv.DictReader(io.StringIO(raw.decode('utf-8-sig')))

def key(row):
    date = row['Delivery Date']
    if '/' in date:
        date = datetime.strptime(date, '%d/%m/%Y').date().isoformat()
    return (row['Event ID'], date, row['From_UTC'], row['To_UTC'], row['Event Type'])

def amount(row, field):
    s = row[field].strip()
    return D(s) if s else None

def calculate():
    windows = {}
    for r in source('official-snapshot.csv'):
        k = key(r)
        req = amount(r, 'Service Requirement MW')
        if not ('2026-07-01' <= k[1] <= '2026-09-30' and r['Service Requirement Type'] == 'Live' and req and req > 0):
            continue
        start, end = [datetime.strptime(v,'%H:%M') for v in k[2:4]]
        if k in windows or (end-start).seconds!=1800:
            raise ValueError(('Nonunique or non-half-hour key', k))
        windows[k] = (req, amount(r,'DFS Procured MW'), amount(r,'Settled Volume MW'))
    requirements = {}
    for r in source('req.csv'):
        k = key(r)
        if k in windows:
            if k in requirements or amount(r,'Service Requirement MW')!=windows[k][0]:
                raise ValueError(('Requirement mismatch', k))
            requirements[k] = r['Zonal Cap']
    if requirements.keys()!=windows.keys():
        raise ValueError('Missing requirements')
    bids = defaultdict(list)
    decisions = defaultdict(int)
    for r in source('bids.csv'):
        k = key(r)
        if k in windows:
            status = r['Status'].strip().lower()
            if status not in ('accepted','rejected'):
                raise ValueError(('Unknown status',status))
            decisions[status]+=1
            bids[k].append((status,int(r['Zone']),D(r['DFS Procured MW']),D(r['Utilisation Price GBP per MWh'])))
    row_results=[]
    upper_total=single_total=D(0)
    for k,(req,proc,settled) in sorted(windows.items()):
        accepted=[b for b in bids[k] if b[0]=='accepted' and b[2]>0]
        rejected=[b for b in bids[k] if b[0]=='rejected' and b[2]>0]
        if sum(b[2] for b in accepted)!=proc:raise ValueError(('Bid sum differs',k))
        if k[-1]!='Downwards' or not (0<proc<req and rejected):continue
        caps={}
        for field in requirements[k].split(','):
            zone,value=field.strip().split(':')
            if not re.fullmatch(r'Z\d+',zone):raise ValueError(zone)
            i=int(zone[1:])
            if i in caps:raise ValueError(('duplicate zone',k))
            caps[i]=D(value)
        if set(caps)!=set(range(1,13)):raise ValueError(('incomplete caps',k))
        head={i:caps[i]-sum(b[2] for b in accepted if b[1]==i) for i in caps}
        if min(head.values())<0:raise ValueError(('observed cap exceeded',k))
        fitting=[b for b in rejected if b[2]<=min(req-proc,head[b[1]])]
        pairs=[(a[3],b[3]) for a in accepted for b in fitting if a[1]==b[1]]
        upper=min(req-proc,sum(min(head[i],sum(b[2] for b in rejected if b[1]==i)) for i in caps))
        single=max((b[2] for b in fitting),default=D(0))
        upper_total+=upper/2
        single_total+=single/2
        low=max(a[3] for a in accepted)
        high=min(b[3] for b in rejected)
        row_results.append(dict(key=list(k),L=str(low),U=str(high),gap=str(high-low),whole=bool(fitting),
                                same_zone=bool(pairs),rejected_cheaper=any(b<a for a,b in pairs),tie=any(a==b for a,b in pairs)))
    down=[x for k,x in windows.items() if k[-1]=='Downwards']
    comp=[(r,p,s) for r,p,s in down if s is not None]
    before=sum((r-p)/2 for r,p,s in down)
    V=sum(p/2 for r,p,s in down)
    Y=sum(s/2 for r,p,s in comp)
    obs=dict(windows=len(windows),decisions=dict(decisions),down=len(down),up_zero=sum(k[-1]=='Upwards' and v[1]==0 for k,v in windows.items()),
             complete_down=len(comp),negative=sum(s<0 for r,p,s in comp),mixed=len(row_results),events=len({x['key'][0] for x in row_results}),
             whole=sum(x['whole'] for x in row_results),comparable=sum(x['same_zone'] for x in row_results),
             inverted=sum(x['rejected_cheaper'] for x in row_results),tied=sum(x['tie'] for x in row_results),
             price_separated=sum(D(x['gap'])>0 for x in row_results),min_gap=str(min(D(x['gap']) for x in row_results)),
             max_gap=str(max(D(x['gap']) for x in row_results)),upper_mwh=str(upper_total),single_mwh=str(single_total),
             complete_before=str(sum((r-p)/2 for r,p,s in comp)),complete_after=str(sum((p-s)/2 for r,p,s in comp)),
             before=str(before),procured=str(V),settled_known=str(Y),equal_gap_missing=str(V-Y-before))
    return {'summary':obs,'rows':row_results}
if __name__=='__main__':
    print(json.dumps(calculate(),indent=2,sort_keys=True))

