"""Normalized toll-only break-even distances across published Austrian freight classes."""
from fractions import Fraction as F
from pathlib import Path
import json
def read(p):return json.loads(Path(p).read_bytes())
v=read('at.json');official=read('operator.json')
def matches(criteria,attributes):
    for k,a in criteria.items():
        x=attributes[k]
        if isinstance(a,dict):
            if x<a.get('min',x) or x>a.get('max',x):return False
        elif x not in a:return False
    return True
def rate(component,attributes):
    cls,=[cl['id'] for cs in v['vehicle_class_sets'] for cl in cs['classes'] if cs['id']==component+'-1' and matches(cl['criteria'],attributes)]
    table,=[d for d in v['charges'] if d['id']==component]
    val,=[amount for obj,c,amount in table['rows'] if obj=='roads' and c==cls]
    return F(val)
rule,=[r for r in v['rules'] if r['params']['object']=='stretch:a12']
if rule['applies_to']!=['infrastructure'] or F(rule['params']['factor'])!=F(5,4):raise ValueError(rule)
rows=[]
for label,euro,*totals in official['rows']:
    co=int(label[-1]);emission={'emissionsfrei':'6','EURO VI':'6','EURO V / EEV':'5','EURO IV':'4','EURO 0 - III':'3'}[euro]
    for ax,text in zip([2,3,4],totals):
        attr=dict(co2_class=co,euro_class=emission,train_axles=ax,train_mass_kg=18000)
        i,a,d=[rate(k,attr) for k in ['infrastructure','air_noise','co2']]
        t=i+a+d
        if t!=F(text.replace(',','.')):raise ValueError((attr,t,text))
        ratio=1+i/(4*t)
        rows.append(dict(co2=co,euro=euro,axles=ax,base=str(t),infrastructure=str(i),surcharge=str(i/4),ratio=str(ratio)))
lo=min(F(r['ratio']) for r in rows);hi=max(F(r['ratio']) for r in rows)
scalar=2*lo*hi/(lo+hi)
if scalar/lo-1!=1-scalar/hi:raise ValueError('minimax equalization')
print(json.dumps(dict(rows=rows,minimum=str(lo),maximum=str(hi),minimax=str(scalar),max_relative_error=str((hi-lo)/(hi+lo)),at_1_22=[{'co2':r['co2'],'euro':r['euro'],'axles':r['axles'],'ordinary_cheaper':F(122,100)<F(r['ratio'])} for r in rows]),indent=2))
