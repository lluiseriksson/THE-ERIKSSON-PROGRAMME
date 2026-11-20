"""Verify finite-design functional diameters on the exact archived decimal rows."""
import csv,itertools,json
from fractions import Fraction as F
from pathlib import Path


def check(ok, message):
    if not ok:raise ValueError(message)


def dot(a,b):
    check(len(a)==len(b),'Dimension mismatch')
    return sum(x*y for x,y in zip(a,b))


def verify(label):
    with open(label+'-loadings.csv') as stream:
        rows=list(csv.reader(stream))[1:]
    codes=[r[0] for r in rows]
    x=[[F(v) for v in row[1:]] for row in rows]
    target=x[0]
    cert=json.loads(Path(label+'-radii.json').read_text())
    check(codes==cert['stations'] and codes[0]==cert['target']=='G110003','Station order differs')
    donors=set(range(1,len(rows)))
    checked={}
    for n in cert['nodes']:
        removed=frozenset(n['removed']);ss=n['support']
        check(removed<=donors and len(removed)<=2 and removed not in checked,'Invalid removed donors')
        check(set(ss)<=donors-removed and len(ss)==len(set(ss)),'Donor used after removal')
        w=list(map(F,n['weights']));h=list(map(F,n['direction']))
        check(len(w)==len(ss),'Weight count mismatch')
        check(all(dot(w,[x[i][j] for i in ss])==v for j,v in enumerate(target)),'Target representation fails')
        check(all(abs(dot(x[i],h))<=1 for i in donors-removed),'Direction not feasible')
        upper=sum(map(abs,w))
        check(upper==dot(target,h)==F(n['value']),'Primal and dual certificates disagree')
        checked[removed]=(upper,set(ss))
    worst=max(value for value,support in checked.values())
    baseline=checked[frozenset()][0]
    comparisons=0
    for size in range(3):
        for removed in itertools.combinations(sorted(donors),size):
            check(any(not ss.intersection(removed) and val<=worst for val,ss in checked.values()),'A deletion has no upper certificate')
            comparisons+=1
    winners=frozenset(codes.index(k) for k in cert['max_removed'])
    check(checked[winners][0]==worst and 2*worst==F(cert['worst_diameter']) and 2*baseline==F(cert['baseline_diameter']),'Bad extrema')
    return dict(stations=len(rows),donors=len(donors),tested_deletions=comparisons,nodes=len(checked),baseline=str(2*baseline),diameter=str(2*worst),worst_removed=sorted(cert['max_removed']))

if __name__=='__main__':
    out={label:verify(label) for label in ['full','restricted']}
    # A changed numerator must be rejected by the actual checker.
    p=Path('full-radii.json');data=p.read_bytes()
    try:
        mutation=json.loads(data)
        old=F(mutation['nodes'][0]['weights'][0])
        mutation['nodes'][0]['weights'][0]=str(old+1)
        p.write_text(json.dumps(mutation))
        try: verify('full')
        except ValueError: pass
        else:raise RuntimeError('Weight mutation passed')
    finally:p.write_bytes(data)
    out['changed_weight_rejected']=True
    print(json.dumps(out,indent=2,sort_keys=True))

