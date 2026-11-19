import csv, hashlib, io, json, zipfile
from datetime import datetime, timedelta, timezone
from decimal import Decimal
from pathlib import Path
from urllib.request import Request, urlopen
import openpyxl
def require(condition,message):
    if not condition:raise ValueError(message)
def fetch(url, expected, cap):
    with urlopen(Request(url,headers={'User-Agent':'Scientific reproducibility audit'}),timeout=75) as r:
        data=r.read(cap+1)
    require(len(data)<=cap and hashlib.sha256(data).hexdigest()==expected,'Primary input differs: '+url)
    return data
pin='34403aef78c2690a8e4f0ba8f7f62d302cdba967'
base='https://raw.githubusercontent.com/ai-emerald/emerald-ai-demo-may-2025/'+pin+'/data/'
inputs={'SRP_total_power.csv':'75f54ebb443898768e585fc970cd51739d1da0fa6cc80d849ff94b744e120fef','Fig2_data.xlsx':'9be3b6cd9074bac295e32a49ce1d7ff7f69957e0c0d5562233acecc461e99ec6','SRP_0503.csv':'8a4155b54876ac2f530907f03422fcc26004e5f6301b75a584f258e0805aa71a'}
raw={k:fetch(base+k,h,250000) for k,h in inputs.items()}
eia='https://www.eia.gov/electricity/gridmonitor/sixMonthFiles/EIA930_BALANCE_2025_Jan_Jun.csv';eh='fac4bb991dfa1dab3b4b35300ccab54ac99be13a40ce91954db8ddafb2816242'
def rows(data):return csv.DictReader(io.StringIO(data.decode('utf-8-sig')))
csv_trace=[(datetime.fromisoformat(r['timestamp']),Decimal(r['total'])) for r in rows(raw['SRP_total_power.csv'])]
wb=openpyxl.load_workbook(io.BytesIO(raw['Fig2_data.xlsx']),read_only=True,data_only=True)
sheet=list(wb['SRP_granular'].values)
require(sheet[1][:2]==('timestamp','total'),'Unexpected figure columns')
fig_trace=[(datetime.fromisoformat(str(row[0])),Decimal(str(row[1]))) for row in sheet[2:] if row[0] is not None]
require(len(csv_trace)==len(fig_trace)==400,'Trace length')
require(all(t-u==timedelta(days=1) and t.utcoffset()==u.utcoffset()==timedelta(hours=-7) and v==w for (t,v),(u,w) in zip(csv_trace,fig_trace)),'Value, date or offset discrepancy outside prespecified relation')
require(all(csv_trace[i+1][0]-a[0]==timedelta(minutes=1) for i,a in enumerate(csv_trace[:-1])),'Minute gap')
tz=timezone(timedelta(hours=-7));ds={t[0][0].date().isoformat():t for t in (fig_trace,csv_trace)}
load={d:{} for d in ds}
for r in rows(fetch(eia,eh,70_000_000)):
    if r['Balancing Authority']!='SRP' or r['Data Date'] not in ('05/03/2025','05/04/2025'):continue
    date=datetime.strptime(r['Data Date'],'%m/%d/%Y').date().isoformat();h=int(r['Hour Number']);require(h not in load[date],'Duplicate hour')
    utc=datetime.strptime(r['UTC Time at End of Hour'],'%m/%d/%Y %I:%M:%S %p')
    end=datetime.fromisoformat(date)+timedelta(hours=h)
    require(utc-end==timedelta(hours=7),'Hour-ending UTC mismatch')
    load[date][h]=Decimal(r['Demand (MW)'].replace(',',''))
def peak(series):
    require(set(series)==set(range(1,25)),'24 unique values required')
    hours=[h for h in series if series[h]==max(series.values())];require(len(hours)==1,'Tied maximum');return hours[0]
def mean(v):return sum(v)/len(v)
def summarize(trace,day,hour):
    end=datetime.fromisoformat(day).replace(tzinfo=tz)+timedelta(hours=hour);start=end-timedelta(hours=1)
    ref=[v for t,v in trace if (t.hour,t.minute)>=(14,40) and t.hour<15]
    require(len(ref)==20,'Reference incomplete')
    summary={}
    for convention in ('start','end'):
        v=[v for t,v in trace if (start<=t<end if convention=='start' else start<t<=end)]
        require(len(v)==60,'Incomplete interval')
        summary[convention]=dict(n=len(v),mean=str(mean(v)),ratio_to_reference=str(mean(v)/mean(ref)))
    return dict(day=day,hour_ending=hour,reference_mean=str(mean(ref)),means=summary)
a,b=sorted(ds);by_day={d:summarize(ds[d],d,peak(load[d])) for d in ds}
author={int(r['hour']):Decimal(r['SRP Actual']) for r in rows(raw['SRP_0503.csv'])}
out=dict(inputs=inputs,eia_sha256=eh,revision=pin,eia_peak=by_day,reference_grid_peak=summarize(ds[a],a,peak(author)),ratio_earlier_day_mean_to_later_day_mean={k:str(Decimal(by_day[a]['means'][k]['mean'])/Decimal(by_day[b]['means'][k]['mean'])) for k in ('start','end')})
z=Path('/content/phoenix-peak-hour.zip')
with zipfile.ZipFile(z,'x',zipfile.ZIP_DEFLATED) as f:f.writestr('result.json',json.dumps(out,indent=2))
print('archive_sha256 '+hashlib.sha256(z.read_bytes()).hexdigest())
