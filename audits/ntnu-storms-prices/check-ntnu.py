"""Verify archived integer covers, price projections and selected hydraulic replays."""
from decimal import Decimal as D
from itertools import product
from pathlib import Path
from hashlib import sha256
import json
import ntnu_engine as engine
import pricing_ntnu as price
from storm_pairs import alternatives

def need(x, why):
    if not x:raise ValueError(why)

def main():
    r=json.loads(Path('pairs.json').read_bytes())
    t=engine.source('NTNU_case_withLID.inp').replace('\r\n','\n')
    data=json.loads(engine.source('MultiOpt.json'),parse_float=D,parse_int=D)
    usage=engine.rows_of(t,'LID_USAGE')
    areas={v[0]:D(v[3]) for v in engine.rows_of(t,'SUBCATCHMENTS')}
    summary={}
    for key,row in r['rows'].items():
        allvals=row['allocations']
        grid=alternatives(areas,usage,data['parameters'][int(key)-1])
        need([list(x) for x in product(*grid)]==[v[0] for v in allvals],'Incomplete allocation census')
        target=D(row['published'])
        good=[v for v in allvals if abs(D(str(v[1]))-target)<=D('0.00005')]
        need(len(good)==row['exact_matches'],'Match count')
        # Independently repeat the extrema in the input file, including unfiltered endpoints.
        probes={tuple(v[0]):v for field in [1,2] for v in
                [min(allvals,key=lambda z:z[field]),max(allvals,key=lambda z:z[field])]}
        if good:
            for v in [min(good,key=lambda z:z[2]),max(good,key=lambda z:z[2])]:probes[tuple(v[0])]=v
        for counts,v in probes.items():
            parsed=[u[:2]+[str(n)]+u[3:] for u,n in zip(usage,counts)]
            for k,storm in [(1,'des2'),(2,'design1')]:
                need(engine.evaluate_counts(t,parsed,storm)==v[k],'Different solver extremum')
        summary[key]=dict(count=len(allvals),matches=len(good),recomputed_extrema=len(probes))
    p=json.loads(Path('prices.json').read_bytes());areas2,rows=price.setup(data,price.sections(t))
    # Independently narrow integer prices using conservative bounds with other prices in [0,200].
    # Each row yields a generous necessary interval for permeable pavement considered alone.
    low,upper=0,200;low_row=high_row=None
    for idx,(cost,lower,higher,_) in enumerate(rows,1):
        if higher[1]:
            other=sum(200*higher[j] for j in (0,2,3))
            value=-((other-(cost*1000-500)*price.S)//higher[1])
            if value>low:low,low_row=value,idx
        if lower[1]:
            value=((cost*1000+500)*price.S)//lower[1]
            if value<upper:upper,high_row=value,idx
    tuples={tuple(v) for v in p['tuples']}
    need(len(tuples)==p['feasible_count']==8896 and all(v[1]==45 for v in tuples),'Price projection')
    need(all(price.exact(v,areas2,rows) for v in [min(tuples),max(tuples)]),'Price extremes')
    out=dict(hydraulic=summary,engine=engine.solver.swmm_version_info(),census=len(tuples),
             isolated_pavement_price_bounds=[low,upper],bound_rows=[low_row,high_row],
             conservative_contrast=r['conservative_contrast'],conditioned_contrast=r.get('conditioned_contrast'))
    # Native engine writes to stdout too; keep arithmetic output separate.
    Path('checked.json').write_text(json.dumps(out,sort_keys=True,indent=2)+'\n')

if __name__=='__main__':main()

