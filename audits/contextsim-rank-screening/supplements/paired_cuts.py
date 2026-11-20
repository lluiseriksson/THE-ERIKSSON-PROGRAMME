"""Minimum half-squared displacement with prescribed shortlist misses at two cuts."""
from itertools import permutations
import json

def energy(p):
    return sum((i-v)**2 for i,v in enumerate(p))//2

def cells(n,k,l,demands):
    """Enumerate the integer 3-by-3 transport tables. Each table has one best order."""
    sizes=(k,l-k,n-l)
    starts=(0,k,l)
    best=None
    for a in range(k-demands[0]+1):
        for b in range(min(k-a,l-k)+1):
            c=k-a-b
            if c>n-l:continue
            for d in range(min(l-k,k-a)+1):
                g=k-a-d
                if g>n-l:continue
                low=max(0,l-k-d-(n-l-c),l-k-b-(n-l-g))
                high=min(l-k-d,l-k-b,l-demands[1]-a-b-d)
                for e in range(low,high+1):
                    f=l-k-d-e;h=l-k-b-e;i=n-l-c-f
                    T=((a,b,c),(d,e,f),(g,h,i))
                    rank=list(starts);cost=0
                    for s,row in zip(starts,T):
                        pos=s
                        for col,x in enumerate(row):
                            cost+=x*(rank[col]-pos)**2
                            rank[col]+=x;pos+=x
                    if best is None or cost<best[0]:best=(cost,T)
    if best is None:raise ValueError('infeasible')
    cost,T=best;rank=list(starts);p=[]
    for row in T:
        for col,x in enumerate(row):
            p.extend(range(rank[col],rank[col]+x));rank[col]+=x
    if sorted(p)!=list(range(n)) or 2*energy(p)!=cost or any(sum(v>=cut for v in p[:cut])<d for cut,d in zip((k,l),demands)):
        raise ValueError('Invalid minimizing witness')
    return cost//2,p

def main():
    checks=0
    for n in range(3,9):
        exact={}
        for p in permutations(range(n)):
            E=energy(p);miss=[sum(v>=k for v in p[:k]) for k in range(n)]
            for k in range(1,n-1):
                for l in range(k+1,n):
                    key=(k,l,miss[k],miss[l]);exact[key]=min(exact.get(key,E),E)
        for k in range(1,n-1):
            for l in range(k+1,n):
                for d in range(min(k,n-k)+1):
                    for z in range(min(l,n-l)+1):
                        want=min(E for (a,b,x,y),E in exact.items() if (a,b)==(k,l) and x>=d and y>=z)
                        if cells(n,k,l,(d,z))[0]!=want:raise ValueError((n,k,l,d,z))
                        checks+=1
    examples=[]
    for k,l,d,z in [(15,20,15,15),(15,20,15,14),(15,20,14,14),(15,20,15,12),(15,20,15,10),(15,20,14,12),(15,20,13,13),(10,30,8,10)]:
        cost,p=cells(55,k,l,(d,z));examples.append(dict(k=k,l=l,d=d,z=z,energy=cost,permutation=p))
    print(json.dumps(dict(brute_force_cases=checks,examples=examples)))
if __name__=='__main__':main()