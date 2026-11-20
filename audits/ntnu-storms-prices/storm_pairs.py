"""Bound the second-storm contrast over all integer allocations compatible with displayed fractions."""
from itertools import product
from pathlib import Path
from decimal import Decimal as D
from math import prod
import json
import ntnu_engine as audit


def alternatives(area,usage,display):
    # Inclusive outer box. Extra endpoints only expand the enumerated set.
    err=D('0.00005')
    grids=[]
    for row,x in zip(usage,display):
        scale=area[row[0]]*10000
        lo=int(max(D(0),x-err)*scale)
        hi=int(min(D(1),x+err)*scale)
        grids.append(range(lo,hi+1))
    return grids


def run():
    t=audit.source('NTNU_case_withLID.inp').replace('\r\n','\n')
    data=json.loads(audit.source('MultiOpt.json'),parse_float=D,parse_int=D)
    obj=data['objectives'];cost=[r[0] for r in obj];peaks=[r[1] for r in obj]
    u=audit.rows_of(t,'LID_USAGE');area={v[0]:D(v[3]) for v in audit.rows_of(t,'SUBCATCHMENTS')}
    costs=sorted((cost[i-1],i) for i in audit.PORTFOLIO)
    first,second=costs[:2]
    j=min((i for i,c in enumerate(cost,1) if c<second[0]),key=lambda i:peaks[i-1])
    audit.need(first[1]==2 and j==176 and [i for c,i in costs if c<=cost[j-1]]==[2],'Budget selection changed')
    out=dict(criterion='Minimum published peak strictly below the second portfolio cost; unique affordable portfolio witness',
             engine=audit.solver.swmm_version_info(),files=audit.HASH,unit_token='Explicit nonnegative integer',
             density_box='Closed radius 0.00005 around every displayed fraction, intersected with [0,1], all combinations. Outer bound ignores cross-coordinate density or cost restrictions.',
             comparison=[first[1],j],portfolio=list(audit.PORTFOLIO),portfolio_costs=[int(c) for c,_ in costs],threshold='107.9319',rows={})
    for i in (first[1],j):
        grids=alternatives(area,u,data['parameters'][i-1])
        count=prod(map(len,grids));audit.need(count<=7000,'Enumerated grid too large')
        vals=[]
        for v in product(*grids):
            # Put the explicit integer into the Number field; no division/re-multiplication.
            fixed=[r[:2]+[str(n)]+r[3:] for r,n in zip(u,v)]
            result={}
            for storm in ('des2','design1'):
                result[storm]=audit.evaluate_counts(t,fixed,storm)
            vals.append([list(v),result['des2'],result['design1']])
        err=[abs(D(str(a))-peaks[i-1]) for _,a,_ in vals]
        exact=[v for v,d in zip(vals,err) if d<=D('0.00005')]
        out['rows'][str(i)]=dict(cost=int(cost[i-1]),published=str(peaks[i-1]),allocation_count=count,
                extrema1=[min(v[1] for v in vals),max(v[1] for v in vals)],
                extrema2=[min(v[2] for v in vals),max(v[2] for v in vals)],
                minimum_base_error=str(min(err)),exact_matches=len(exact),
                exact_storm2=[min(v[2] for v in exact),max(v[2] for v in exact)] if exact else None,
                allocations=vals)
    a,z=out['rows']['2'],out['rows'][str(j)]
    out['conservative_contrast']=[a['extrema2'][0]-z['extrema2'][1],a['extrema2'][1]-z['extrema2'][0]]
    if a['exact_matches'] and z['exact_matches']:
        out['conditioned_contrast']=[a['exact_storm2'][0]-z['exact_storm2'][1],a['exact_storm2'][1]-z['exact_storm2'][0]]
    Path('witness.json').write_text(json.dumps(out,sort_keys=True,indent=2))

if __name__=='__main__':run()

