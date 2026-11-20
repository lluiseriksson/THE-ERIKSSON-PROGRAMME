"""Compare reconstructed vendor CSV fingerprints and recompute the deposited CAR cells."""
from pathlib import Path
from datetime import datetime,timezone
import requests,hashlib,io,csv,json,time
from urllib.parse import quote
import numpy as np
import pandas as pd

d=json.loads(Path('source-inputs.json').read_text())
events=d['events']; stocks=list(events[0]['stocks']);series={};records={}
columns=['open','high','low','close','adjclose','volume']
def stamp(x):return int(datetime.fromisoformat(x).replace(tzinfo=timezone.utc).timestamp())
for t in stocks+['^BVSP','SMH']:
    safe=t.replace('^','_')
    raw=d['files'][safe+'.json'];target=d['files'][safe+'.csv']
    url='https://query1.finance.yahoo.com/v8/finance/chart/'+quote(t,safe='')
    resp=requests.get(url,params={'period1':stamp('2023-01-01'),'period2':stamp(raw['modified_utc']),'interval':'1d','events':'div,split','includeAdjustedClose':'true'},headers={'User-Agent':'Mozilla/5.0'},timeout=12)
    records[t]={'http':resp.status_code,'csv_target':target['sha256'],'source_modified':raw['modified_utc'],'csv_match':False}
    if resp.status_code!=200:break
    result=resp.json()['chart']['result'][0];assert result['meta']['symbol']==t
    ts=result['timestamp'];q=dict(result['indicators']['quote'][0]);q.update(result['indicators']['adjclose'][0])
    dates=[datetime.fromtimestamp(z,timezone.utc).date().isoformat() for z in ts]
    values=list(zip(dates,*[q[k] for k in columns],strict=True))
    rawmatch=hashlib.sha256(resp.content).hexdigest()==raw['sha256']
    records[t]['raw_match']=rawmatch
    series[t]=np.log(pd.Series(q['adjclose'],index=pd.to_datetime(dates),dtype=float).dropna().loc[lambda v:~v.index.duplicated()]).diff().dropna()
    def number(v,fmt,comma):
        if v is None:return ''
        if isinstance(v,int):return str(v)
        x=format(v,fmt).upper() if fmt!='short' else (repr(v).upper() if not v.is_integer() else str(int(v)))
        return x.replace('.',',') if comma else x
    for fmt in ['.15g','.16g','.17g','short']:
        if records[t]['csv_match']:break
        for comma in [True,False]:
            buf=io.StringIO(newline='');writer=csv.writer(buf,quoting=csv.QUOTE_ALL,lineterminator='\r\n')
            writer.writerow(['date']+columns)
            for day,*row in values:writer.writerow([day]+[number(v,fmt,comma) for v in row])
            payload=buf.getvalue().encode('ascii')
            if len(payload)==int(target['bytes']) and hashlib.sha256(payload).hexdigest()==target['sha256']:
                records[t].update(csv_match=True,format=fmt,comma=comma);break
    time.sleep(.5)
rows=[]
if len(series)==10:
 R=pd.concat([series[t].rename(t) for t in stocks],axis=1,sort=True)
 for event in events:
    ticks=['^BVSP','SMH'] if event['factor2'] else ['^BVSP']
    X=pd.concat([series[t].rename(t) for t in ticks],axis=1,sort=True).dropna()
    idx=R.index.intersection(X.index);x=X.loc[idx];r=R.loc[idx];k=idx.searchsorted(pd.Timestamp(event['date']))
    assert k>=250 and str(idx[k].date())==event['day0']
    est=slice(k-250,k-30);window=slice(k-1,k+2);ars={}
    for t in stocks:
        y=r[t].iloc[est];ok=y.notna();assert ok.sum()>=150
        fit=np.linalg.lstsq(np.column_stack([np.ones(ok.sum()),x.iloc[est][ok].values]),y[ok].values,rcond=None)[0]
        ars[t]=r[t]-(fit[0]+x.values@fit[1:])
    ar=pd.DataFrame(ars);p=ar.mean(axis=1)
    calc={t:round(100*ar[t].iloc[window].sum(),2) for t in stocks}
    actual={**event['stocks'],'portfolio':event['[-1,+1]']['CAR%'],'day0':event['[0,0]']['CAR%']}
    calc.update(portfolio=round(100*p.iloc[window].sum(),2),day0=round(100*p.iloc[k],2))
    rows.append(dict(event=event['event'],factor2=event['factor2'],distinct_days=[str(z.date()) for z in idx[window]],counts=[int(z) for z in ar.iloc[window].count(axis=1)],cells=len(actual),mismatches={t:[actual[t],calc[t]] for t in calc if abs(actual[t]-calc[t])>1e-6}))
print(json.dumps(dict(series=records,event_reproduction=rows)))
