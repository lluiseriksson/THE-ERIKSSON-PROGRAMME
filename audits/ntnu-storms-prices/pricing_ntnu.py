"""Identify admissible integer prices from rounded design and cost pairs (exact integers)."""
from decimal import Decimal
from fractions import Fraction
from pathlib import Path
from hashlib import sha256
from itertools import product
import json
from urllib.request import urlopen

ROOT='https://raw.githubusercontent.com/ElhadiMohsenAbdalla/SWMMLIDOPT/a824c03d1864b02d153c81679b61e2d9125d090a/Example/'
DIGEST={'MultiOpt.json':'2423484a58456c597d7eea2241a650d3447e56461c1cb51e3ee77d72ea8f2321','NTNU_case_withLID.inp':'0d48118a8b9ed836812a67729d14da6464c5151f5f57b58675ebf1f229897fa8'}
S=10**18
TYPES=('BR','PP','VS','GR')

def need(ok,m):
    if not ok:raise ValueError(m)

def get(n):
    p=Path(n)
    if not p.exists():
        with urlopen(ROOT+n,timeout=25) as f:p.write_bytes(f.read())
    raw=p.read_bytes()
    need(sha256(raw).hexdigest()==DIGEST[n],n)
    return raw.decode()

def integer(v):
    need(int(v)==v,'Inexact fixed point')
    return int(v)

def sections(t):
    out={}
    for s in t.splitlines():
        if s.startswith('['): group=out.setdefault(s.strip(),[])
        elif s.strip() and not s.startswith(';'):group.append(s.split())
    return out

def setup(x,s):
    areas={r[0]:integer(Decimal(r[3])*10000) for r in s['[SUBCATCHMENTS]']}
    usage=[(r[0],TYPES.index(r[1])) for r in s['[LID_USAGE]']]
    out=[]
    for row,(bin_cost,_) in zip(x['parameters'],x['objectives']):
        intervals={}
        lower,upper=[0]*4,[0]*4
        for (label,k),val in zip(usage,row):
            mid=integer(val*S);width=S//20000
            lo,hi=max(0,mid-width),min(8*S//10,mid+width)
            intervals.setdefault(label,[]).append((k,lo,hi))
            lower[k]+=areas[label]*lo
            upper[k]+=areas[label]*hi
        for v in intervals.values():need(sum(lo for _,lo,_ in v)<=8*S//10,'Infeasible density interval')
        out.append((integer(bin_cost),lower,upper,intervals))
    return areas,out

def contract(rows,lo,hi):
    while True:
        old=(tuple(lo),tuple(hi))
        for cost,lower,upper,_ in rows:
            low_target=(1000*cost-500)*S; high_target=(1000*cost+500)*S
            smallest=sum(p*v for p,v in zip(lo,lower));largest=sum(p*v for p,v in zip(hi,upper))
            if smallest>high_target or largest<low_target:return False
            for k in range(4):
                if lower[k]:hi[k]=min(hi[k],(high_target-smallest+lo[k]*lower[k])//lower[k])
                if upper[k]:
                    # Recompute the other-variable upper contribution using current bounds.
                    rest=sum(hi[j]*upper[j] for j in range(4) if j!=k)
                    lo[k]=max(lo[k],-((rest-low_target)//upper[k]))
                if lo[k]>hi[k]:return False
        if old==(tuple(lo),tuple(hi)):return True

def exact(price,areas,rows):
    for cost,lower,_,groups in rows:
        low=sum(v*p for p,v in zip(price,lower))
        high=low
        for label,values in groups.items():
            room=8*S//10-sum(l for _,l,_ in values)
            for k,l,h in sorted(values,key=lambda a:price[a[0]],reverse=True):
                add=min(h-l,room);room-=add
                high+=add*areas[label]*price[k]
        left=(cost*1000-500)*S;right=(cost*1000+500)*S
        if low>right or high<left or cost%2 and (low==right or high==left):return False
    return True

def solve():
    x=json.loads(get('MultiOpt.json'),parse_float=Decimal,parse_int=Decimal)
    areas,rows=setup(x,sections(get('NTNU_case_withLID.inp')))
    lo,hi=[0]*4,[200]*4
    ok=contract(rows,lo,hi)
    measured={'rows':len(rows),'types':TYPES,'box_after_contraction':[lo,hi],'fraction_radius':'0.00005','density_cap':'0.8','files':DIGEST}
    viable=[]
    def search(l,h):
        if not contract(rows,l,h):return
        if l==h:
            if exact(l,areas,rows):viable.append(tuple(l))
            return
        k=max(range(4),key=lambda j:h[j]-l[j]);mid=(l[k]+h[k])//2
        u=h.copy();u[k]=mid;search(l.copy(),u)
        v=l.copy();v[k]=mid+1;search(v,h.copy())
    if ok:search(lo.copy(),hi.copy())
    measured['feasible_count']=len(viable)
    measured['projections']=[sorted({v[j] for v in viable}) for j in range(4)]
    measured['extreme_examples']=[viable[0],viable[-1]] if viable else []
    measured['tuples']=viable
    # A straightforward enumerator on a restricted grid provides a separate branch-pruning check.
    if viable:
        grid=[range(max(0,v-1),min(200,v+1)+1) for v in viable[0]]
        direct={v for v in product(*grid) if exact(v,areas,rows)}
        need(direct=={v for v in viable if all(a in r for a,r in zip(v,grid))},'Restricted enumeration mismatch')
    print(json.dumps(measured,sort_keys=True,indent=2))

if __name__=='__main__':solve()

