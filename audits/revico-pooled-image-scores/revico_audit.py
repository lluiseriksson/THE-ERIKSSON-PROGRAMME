"""Certify what two micro F1 scores identify under ReViCo Appendix E."""
from fractions import Fraction as F
from pathlib import Path
import json
tables=json.loads(Path('tables.json').read_bytes())
one={r['model']:list(map(F,r['values'])) for r in tables['S3.T1'] if r['section']=='vision'}
two={r['model']:list(map(F,r['values'])) for r in tables['S4.T2']}
eps=F(1,20)
def rate(d,c):
    return c*(200-d)/(d*(200-c))
def band(d,c):
    return [rate(d+eps,c-eps),rate(d-eps,c+eps)]
def direction(u,v):
    return 'increase' if u[1]<v[0] else 'decrease' if v[1]<u[0] else 'undetermined'
mismatch={};evidence={};recall_check={}
for model,row in two.items():
    d,c=row[0],row[4]
    base=band(d,c);enh=band(row[1],row[5])
    rec=dict(direct=list(map(str,base)),background=list(map(str,enh)),direction=direction(base,enh),delta_sign_ic=int(row[5]>c)-int(row[5]<c))
    if model in one:
        v=one[model];f1=v[2::3]
        if row[::2]!=f1:mismatch[model]=dict(table1=list(map(str,f1)),table2=list(map(str,row[::2])))
        alt=band(f1[0],f1[2]);rec['direction_table1']=direction(alt,enh)
        rec['delta_ic_table1']=int(row[5]>f1[2])-int(row[5]<f1[2])
        rd,rc=v[1],v[7]
        ratio=[(rc-eps)/(rd+eps),(rc+eps)/(rd-eps)]
        recall_check[model]=max(alt[0],ratio[0])<=min(alt[1],ratio[1])
    evidence[model]=rec
from collections import Counter
print(json.dumps(dict(table2_directions=dict(Counter(r['direction'] for r in evidence.values())),mismatch=mismatch,recall_consistency=recall_check,rows=evidence)))
