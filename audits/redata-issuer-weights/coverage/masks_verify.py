"""Public reproducibility probe and exact synthetic counterexamples. Retain no price series."""
from fractions import Fraction as F
from datetime import datetime,timezone
from pathlib import Path
from urllib.parse import quote
import json,hashlib,requests,csv,io
inp=json.loads(Path('source-inputs.json').read_text(),parse_float=F)
events=inp['events']; tickers=list(events[0]['stocks'])+['^BVSP','SMH']
assert len(set(tickers))==10
def ts(s):return int(datetime.fromisoformat(s).replace(tzinfo=timezone.utc).timestamp())
def observations(res):
    prices=res['indicators']['adjclose'][0]['adjclose'];dates=res['timestamp']
    assert len(prices)==len(dates)
    return sorted(set(datetime.fromtimestamp(t,timezone.utc).date().isoformat() for t,p in zip(dates,prices) if p is not None))[1:]
attempts={};dates={};match={}
for name in tickers:
    safe=name.replace('^','_');expected=inp['files'][safe+'.json']
    endpoint='https://query1.finance.yahoo.com/v8/finance/chart/'+quote(name,safe='')
    try:
        r=requests.get(endpoint,params={'period1':ts('2023-01-01'),'period2':ts(expected['modified_utc']),'interval':'1d','events':'div,split','includeAdjustedClose':'true'},headers={'User-Agent':'Mozilla/5.0'},timeout=12)
        info={'http':r.status_code,'requested_url':r.url,'original_hash':expected['sha256']}
        attempts[name]=info
        if r.status_code!=200:
            info['retry_after']=r.headers.get('Retry-After')
            if r.status_code in (401,403,429):break
            continue
        res=r.json()['chart']['result'][0]
        if res['meta']['symbol']!=name:raise ValueError('Wrong symbol')
        h=hashlib.sha256(r.content).hexdigest();match[name]=h.lower()==expected['sha256'].lower()
        dates[name]=observations(res)
        info.update(received_hash=h,exact_original=match[name],date_count=len(dates[name]))
    except (requests.RequestException,IndexError,KeyError,ValueError,TypeError) as exc:
        attempts.setdefault(name,{})['error_type']=type(exc).__name__
        break
out={'attempts':attempts,'observed_windows':[],'complete_vintage_match':len(match)==10 and all(match.values()),'examples':[]}
if len(dates)==10:
    for r in events:
        stockdates=set.union(*(set(dates[n]) for n in r['stocks']))
        idx=sorted(stockdates&set(dates['^BVSP'])&(set(dates['SMH']) if r['factor2'] else stockdates))
        k=next(j for j,d in enumerate(idx) if d>=r['date'])
        window=idx[k-1:k+2]
        out['observed_windows'].append({'event':r['event'],'factor2':r['factor2'],'dates':window,'day0_matches':idx[k]==r['day0'],'missing':{t:[n for n in r['stocks'] if t not in dates[n]] for t in window}})
def wc(day,w):
    return sum(x*a for x,a in zip(day,w) if x is not None)/sum(a for x,a in zip(day,w) if x is not None)
def total(panel,w):return sum(wc(day,w) for day in panel)
def individual(panel):return [sum(x for x in col if x is not None) for col in zip(*panel)]
u=[F(1,8)]*8
w=[F(1,5)]*4+[F(1,20)]*4
# k=1 is missing on the first day, i=0,j=4 are present on both days.
for r in events:
    a=list(r['stocks'].values());p=r['[-1,+1]']['CAR%'];center=r['[0,0]']['CAR%'];m=sum(a)/8
    correction=(p-m)/2;c=[x+correction for x in a]
    assert abs(correction)<F(1,200) and abs(sum(c)/8-p)<F(1,200)
    complete=[[F(0)]*8,[center]*8,[x-center for x in c]]
    one_missing=[day[:] for day in complete];one_missing[0][1]=None
    bases=[wc(day,u) for day in complete]
    assert individual(complete)==individual(one_missing)==c and [wc(day,u) for day in one_missing]==bases
    coeff=(w[0]-w[4])*w[1]/(1-w[1])
    assert coeff==F(3,80)
    def shifted(h):
        panel=[day[:] for day in one_missing]
        panel[0][0]+=h;panel[0][4]-=h;panel[2][0]-=h;panel[2][4]+=h
        assert individual(panel)==c and [wc(day,u) for day in panel]==bases
        return total(panel,w)
    values={str(h):shifted(F(h)) for h in [-1,0,1]}
    assert values['1']-values['0']==values['0']-values['-1']==coeff
    out['examples'].append({'event':r['event'],'factor2':r['factor2'],'ticker_order':list(r['stocks']),'common_weights':w,'complete_and_missing_equal_daily_means':bases,'issuer_rounding_offset':correction,'slope':coeff,'weighted_values':values})
print(json.dumps(out,default=str))
