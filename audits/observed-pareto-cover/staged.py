"""Exact contingent versus immediate-completion costs for three staged designs."""
from fractions import Fraction as F
from functools import lru_cache
from itertools import permutations, product
import json


def certify(a, b, prob, deadline):
    n = len(a)
    @lru_cache(None)
    def best(state, remaining):
        if all(s == 0 for s in state):
            return F(0)
        options = [F(cost) for cost,s in zip(b,state) if s == 1 and cost <= remaining]
        for i, s in enumerate(state):
            if s != -1 or a[i] > remaining:
                continue
            children = [best(state[:i]+(h,)+state[i+1:],remaining-a[i]) for h in (0,1)]
            if None not in children:
                options.append(a[i]+(1-prob[i])*children[0]+prob[i]*children[1])
        return min(options) if options else None
    fixed=[]
    for perm in permutations(range(n)):
        costs=[]
        for row in product((0,1),repeat=n):
            time=0
            for i in perm:
                time+=a[i]
                if row[i]:
                    time+=b[i]
                    break
            mass=F(1)
            for bit, p in zip(row, prob):
                mass *= p if bit else 1-p
            costs.append((time,mass))
        if max(x for x,_ in costs)<=deadline:
            fixed.append((sum(x*p for x,p in costs),perm))
    return best((-1,)*n,deadline),min(fixed) if fixed else None


def main():
    examples=[]
    for m,p in [(3,(F(1,2),F(1,2),F(3,4)))]+[(v,(F(v-1,v),)*3) for v in (2,4,16,64,256)]:
        q,r=certify([1]*3,[m,m,1],p,m+2)
        if not r or q is None:
            raise ValueError('Expected a feasible policy')
        policy=p[0]*(p[2]*3+(1-p[2])*(2+m))+(1-p[0])*(p[1]*(2+m)+(1-p[1])*(p[2]*4+(1-p[2])*3))
        if q>policy or r[0]<p[0]*(1+m):
            raise ValueError('Counts disagree with strategy or lower bound')
        if m==3 and (q!=F(63,16) or r[0]!=F(67,16)):
            raise ValueError('Three-design regression')
        if m!=3 and policy>6:
            raise ValueError('Uniform upper bound failed')
        examples.append(dict(tail=m,probabilities=list(map(str,p)),deadline=m+2,optimal=str(q),
                             immediate=str(r[0]),upper_strategy=str(policy),fixed_order=r[1]))
    infeasible=certify([1]*3,[3,3,1],(F(1,2),)*3,4)
    if infeasible!=(None,None):
        raise ValueError('Mutated deadline incorrectly accepted')
    print(json.dumps(examples, indent=2,sort_keys=True))


if __name__ == '__main__':
    main()

