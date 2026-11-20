"""Compare Ghana's four printed recalculation series with two official CRT trend sheets."""
from decimal import Decimal as D
from pathlib import Path
import json

def read(name):
    return json.loads(Path(name).read_bytes())

def number(v):
    return D(v.replace(',',''))

def direction(change,tolerance):
    return 1 if change>tolerance else -1 if change < -tolerance else 0

def analyze(recalc,anchors,crt):
    if [r['year'] for r in recalc]!=list(range(1990,2022)) or [r['year'] for r in crt]!=list(range(1990,2023)):
        raise ValueError('Calendar discontinuity')
    keys=('previous_with','current_with','previous_without','current_without')
    series=[{k:number(r[k]) for k in keys} for r in recalc]
    pairs={'revision_with':(keys[0],keys[1]),'revision_without':(keys[2],keys[3]),'coverage_previous':(keys[0],keys[2]),'coverage_current':(keys[1],keys[3]),
           'table97_vs_crt_with':('current_with','s6_with'),'table97_vs_crt_without':('current_without','s6_without'),
           'crt_sheets_with':('s1_with','s6_with'),'crt_sheets_without':('s1_without','s6_without'),'crt_coverage':('s6_with','s6_without')}
    rows=[]
    for i,r in enumerate(crt):
        if i<len(series): values=series[i].copy()
        else:values={}
        values.update({k:number(v) for k,v in r.items() if k.startswith('s')})
        if i:
            diffs={k:v-last[k] for k,v in values.items() if k in last}
            signs={k:direction(v,D('.1') if k in keys else D('.000001')) for k,v in diffs.items()}
            rows.append({'to_year':r['year'],'change':{k:str(v) for k,v in diffs.items()},'sign':signs})
        last=values
    flipped={k:[r['to_year'] for r in rows if a in r['sign'] and b in r['sign'] and r['sign'][a]*r['sign'][b]==-1] for k,(a,b) in pairs.items()}
    residuals={}
    for r in crt:
        y=str(r['year']);a={k:number(r[k]) for k in r if k.startswith('s')}
        delta=a['s1_without']-a['s6_without']
        residuals[y]=dict(sheet1_minus_sheet6_without=str(delta),hwp=str(a['s1_hwp']),sheet1_matches_sheet6=abs(delta)<D('.000001'),sheet1_minus_sheet6_equals_minus_hwp=abs(delta+a['s1_hwp'])<D('.000001'),
                          sector_closure=str(a['s6_with']-a['s6_lulucf']-a['s6_without']))
        if y in anchors['with']:
            tw=number(anchors['with'][y]);tn=number(anchors['without'][y]);land=number(anchors['land'][y]);wood=number(anchors['hwp'][y])
            residuals[y]['anchor']=dict(with_residual=str(tw-a['s6_with']),without_residual=str(tn-a['s6_without']),net_land_residual=str(land+wood-a['s6_lulucf']),printed_without_minus_wood_minus_crt=str(tn-wood-a['s6_without']))
    return dict(flips=flipped,changes=rows,reconciliation=residuals,indeterminate={k:[r['to_year'] for r in rows if r['sign'].get(k)==0] for k in keys})

if __name__=='__main__':
    print(json.dumps(analyze(read('table97.json')['rows'],read('table17.json'),read('crt-trends.json')['rows']),indent=2,sort_keys=True))

