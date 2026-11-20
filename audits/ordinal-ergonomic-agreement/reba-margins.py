"""Exact agreement profiles with both histograms fixed. Standard library only."""
from itertools import combinations_with_replacement, product
from collections import defaultdict
import json

def limits(rows, cols, up, down):
    k=len(rows)
    if len(cols)!=k or len(up)!=k-1 or len(down)!=k-1 or sum(rows)!=sum(cols) or min((*rows,*cols,*up,*down))<0:
        return None
    u=(0,*up,0);d=(0,*down,0);out=[];bounds=[]
    for i,(r,c) in enumerate(zip(rows,cols)):
        o=u[i+1]+d[i];a=u[i]+d[i+1]
        lower=max(0,o-r);upper=min(u[i],u[i+1])+min(d[i],d[i+1])
        if r-c!=o-a or lower>upper:return None
        out.append(o);bounds.append((lower,upper))
    return (sum(out)-sum(h for l,h in bounds),sum(out)-sum(l for l,h in bounds),out,bounds)

def witness(r,c,u,d,e):
    v=limits(r,c,u,d)
    if v is None or not v[0]<=e<=v[1]:return None
    lo,hi,out,bounds=v
    k=len(r);table=[[0]*k for _ in r];extra=hi-e
    through_up=[];through_down=[]
    for i,(a,b) in enumerate(bounds):
        take=min(extra,b-a);s=a+take;extra-=take
        up=min(s,min((0,*u,0)[i:i+2]))
        through_up.append(up);through_down.append(s-up)
        table[i][i]=r[i]-out[i]+s
    for upward,thru in [(True,through_up),(False,through_down)]:
        active=[]
        for i in (range(k) if upward else reversed(range(k))):
            leave=(u[i] if i<k-1 else 0) if upward else (d[i-1] if i else 0)
            while len(active)>thru[i]:table[active.pop()][i]+=1
            active.extend([i]*(leave-thru[i]))
    return table

def summary(t):
    k=len(t);r=tuple(map(sum,t));c=tuple(map(sum,zip(*t)))
    e=sum(r)-sum(t[i][i] for i in range(k))
    u=tuple(sum(t[i][j] for i in range(a+1) for j in range(a+1,k)) for a in range(k-1))
    d=tuple(sum(t[i][j] for j in range(a+1) for i in range(a+1,k)) for a in range(k-1))
    return r,c,u,d,e

def hist(k,n):
    if k==1:
        yield (n,)
    else:
        for i in range(n+1):
            for rest in hist(k-1,n-i):yield (i,*rest)

def profiles(r,c,cap):
    # Balance determines the downward crossings once upward counts are known.
    k=len(r);diff=[sum(r[:i])-sum(c[:i]) for i in range(1,k)]
    for u in product(range(cap+1),repeat=k-1):
        d=tuple(a-delta for a,delta in zip(u,diff))
        if min(d)<0 or max(d)>cap:continue
        yield u,d

def exhaust(k,n):
    actual=set();num=0
    for cells in combinations_with_replacement(range(k*k),n):
        table=[[0]*k for _ in range(k)]
        for a in cells:table[a//k][a%k]+=1
        actual.add(summary(table));num+=1
    found=set()
    for r,c in product(hist(k,n),repeat=2):
        for u,d in profiles(r,c,n):
            lim=limits(r,c,u,d)
            if lim:
                for e in range(lim[0],lim[1]+1):
                    key=(r,c,u,d,e)
                    if summary(witness(*key))!=key:raise ValueError(key)
                    found.add(key)
    if actual!=found:raise ValueError('Exhaustive mismatch')
    return dict(categories=k,trials=n,matrices=num,summaries=len(found))

def published(name,t):
    # Huang et al. tables 2 and 3: transpose to reference rows, system columns.
    r,c,uo,do,e=summary(list(zip(*t)))
    options=[]
    for u,d in profiles(r,c,e):
        lim=limits(r,c,u,d)
        if lim and lim[0]<=e<=lim[1]:
            if summary(witness(r,c,u,d,e))!=(r,c,u,d,e):raise ValueError('Wrong matrix')
            options.append((u,d))

    ranges=[[min(d[i] for u,d in options),max(d[i] for u,d in options)] for i in (0,1)]
    both=[d for u,d in options if d[0]==ranges[0][1] and d[1]==ranges[1][1]]
    cond=[d[1] for u,d in options if d[0]==do[0]]
    extrema={}
    for label,op in [('minimum',min),('maximum',max)]:
        u,d=op(options,key=lambda q:q[1][1])
        extrema[label]=witness(r,c,u,d,e)
    actual=limits(r,c,uo,do)
    return dict(name=name,expert_rows=r,system_cols=c,discordant=e,observed_up=uo,observed_down=do,possible_directed_profiles=len(options),down_ranges=ranges,both_upper_attained=bool(both),high_down_given_observed_low=sorted(set(cond)),mismatch_range_given_actual_cuts=actual[:2],extreme_high_witnesses=extrema)

def main():
    checks=[exhaust(k,n) for k,ns in [(2,range(6)),(3,range(6)),(4,range(4)),(5,range(3))] for n in ns]
    tables=[published('RULA',[[30,8,0],[2,153,15],[0,10,82]]),published('REBA',[[18,1,0],[1,191,12],[0,11,66]])]
    print(json.dumps(dict(checks=checks,tables=tables,source='https://doi.org/10.3390/ijerph17176050'),indent=2))
if __name__=='__main__':main()
