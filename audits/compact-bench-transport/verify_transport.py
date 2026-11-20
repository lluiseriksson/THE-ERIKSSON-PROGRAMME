"""Replay the archived certificates with the Python standard library."""
from fractions import Fraction as F
from pathlib import Path
import json

root = Path(__file__).parent
def check(ok,message):
    if not ok: raise ValueError(message)
def dot(a,b):
    return sum(x*y for x,y in zip(a,b,strict=True))
def proof(cert,H,b,c):
    x=list(map(F,cert['x']));y=list(map(F,cert['y']))
    check(len(x)==len(c) and len(y)==len(H)==len(b),'Certificate dimensions')
    check(min(x)>=0 and all(dot(row,x)==rhs for row,rhs in zip(H,b)),'Primal infeasible')
    check(all(dot(col,y)<=cost for col,cost in zip(zip(*H,strict=True),c)),'Dual infeasible')
    value=F(cert['value'])
    check(dot(c,x)==value==dot(b,y),'Optimal values disagree')
    return value

def invert(row,n,repeats):
    v=[]
    for j,nj in enumerate(n):
        p=F(row[1+j+j//3])
        possible=[k for k in range(repeats*nj+1) if abs(F(100*k,repeats*nj)-p)<=F(1,20)]
        v.append(possible[0] if len(possible)==1 else None)
    return v
def aggregates(row,n,v,repeats):
    for pos,group in [(4,range(3)),(8,range(3,6)),(12,range(6,9)),(13,range(9))]:
        rate=F(100*sum(v[j] for j in group),repeats*sum(n[j] for j in group))
        check(abs(rate-F(row[pos]))<=F(1,20),'Aggregate mismatch')

def main():
    data=json.loads((root/'compact-cells.json').read_bytes())
    r=json.loads((root/'certificates.json').read_bytes())
    n=data['counts'];rates={};unresolved={}
    for row in data['rows']:
        v=invert(row,n,3)
        if None not in v:
            aggregates(row,n,v,3)
            rates[row[0]]=[F(k,3*m) for k,m in zip(v,n)]
        else:
            check(row[0]=='DeepSeek V4 Pro (Max)' and v[3:6]==[None]*3,'Unexpected grid discrepancy')
            alternative=invert(row,n,2);check(None not in alternative,'Two-unit witness failed')
            aggregates(row,n,alternative,2)
            unresolved[row[0]]=alternative
            rates[row[0]]=[(F(row[1+j+j//3])+F(1,20))/100 for j in range(9)]
    leaders=list(rates)[:2];check(leaders==r['leaders'],'Leaders differ')
    gap=[a-b for a,b in zip(rates[leaders[0]],rates[leaders[1]])]
    check(list(map(F,r['gaps']))==gap,'Input contrast differs')
    A=[[int(j//3==i) for j in range(9)] for i in range(3)]+[[int(j%3==i) for j in range(9)] for i in range(2)]
    b=[dot(row,n) for row in A]
    low=proof(r['minimum'],A,b,gap)/200
    high=-proof(r['negative_maximum'],A,b,[-x for x in gap])/200
    E=[row+[0]*18 for row in A]+[gap+[0]*18]
    for i in range(9):
        eye=[int(j==i) for j in range(9)]
        E.append(eye+[-x for x in eye]+eye)
    radius=proof(r['nearest_tie'],E,b+[0]+n,[0]*9+[1]*9+[0]*9)/200
    floors={}
    for name in list(rates)[2:]:
        E=[row+[0]*3 for row in A]
        for i,lead in enumerate(leaders):
            E.append([a-b for a,b in zip(rates[lead],rates[name])]+[-1,int(i==0),int(i==1)])
        floors[name]=(proof(r['separation'][name]['certificate'],E,b+[-200,-200],[0]*9+[1,0,0])-200)/200
        check(floors[name]==F(r['separation'][name]['floor'])>0,'Rival not excluded')
    interior=r['interior_witness']
    check(min(interior)>0 and [dot(row,interior) for row in A]==b and dot(gap,interior)<0,'No interior reversal')
    check(radius==F(r['radius']) and F(r['original'])==dot(gap,n)/200,'Radius or original discrepancy')
    return dict(range=[str(low),str(high)],radius=str(radius),interior=str(dot(gap,interior)/200),closest_rival=min(floors,key=floors.get),rival_floor=str(min(floors.values())),two_unit_witness=unresolved)
if __name__=='__main__': print(json.dumps(main(),sort_keys=True,indent=2))

