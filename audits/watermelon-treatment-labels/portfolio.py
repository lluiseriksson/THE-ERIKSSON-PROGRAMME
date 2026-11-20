"""Verify the finite competitors and the dual upper bounds for the equal-base-cost example."""
from fractions import Fraction as F
from itertools import combinations
from pathlib import Path
import json
from yield_audit import audit, require

def solve(raw):
    data=audit(raw)
    left=list(map(F,data['2025']['actual_means']))
    right=left.copy()
    right[3],right[4]=right[4],right[3]
    high,low,invariant=left[4],left[3],left[5]
    b1,b2=2*invariant-high-low,high-low
    require((b1,b2)==(F(269,300),F(889,300)),'Breakpoint identity')
    # Independently intersect the two scenario-payoff coordinates on every simplex edge.
    def verify(k):
        r=[y-(k if j%2 else 0) for j,y in enumerate(left)]
        s=[y-(k if j%2 else 0) for j,y in enumerate(right)]
        candidates=[min(a,b) for a,b in zip(r,s)]
        pure=max(candidates)
        for i,j in combinations(range(6),2):
            u,v=r[i]-s[i],r[j]-s[j]
            if u*v<0:
                t=v/(v-u)
                candidates.append(t*r[i]+(1-t)*r[j])
        optimal=max(candidates)
        require(optimal==max(invariant-k,(high+low-k)/2,low),'Edge maximization mismatch')
        return [str(pure),str(optimal)]
    probes=[F(0),b1/2,b1,(b1+b2)/2,F(2),b2,b2+1]
    data['equal_base_costs']={'breaks':[str(b1),str(b2)],'pure_and_split':{str(k):verify(k) for k in probes}}
    return data

if __name__=='__main__':
    print(json.dumps(solve(Path('supplement.zip').read_bytes()),indent=2,sort_keys=True))

