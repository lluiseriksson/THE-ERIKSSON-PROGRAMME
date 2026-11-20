"""Compare Theorem 2 with exhaustive unilateral deviations on rational grids."""
import json
from collections import Counter

def inspect(m, q, v, e, tick, numerator, denominator):
    residual = (m-q[1], m-q[0])
    d = sum(q)-m
    if not (0 <= e[0] < residual[0] < q[0] < m and
            0 < residual[1] < e[1] < q[1] < m and sum(e) <= m and
            d*v[0] > (q[0]-e[0])*v[1] and v[1] % tick == 0):
        raise ValueError("Invalid example")
    # Integer payoffs scaled by the probability denominator.
    def payoff(x,y):
        price = min(x,y)
        weight = denominator if x > y else 0 if x < y else numerator
        allocation = (denominator*residual[0]+weight*d,denominator*q[1]-weight*d)
        return tuple(allocation[i]*(v[i]-price)+denominator*e[i]*price for i in range(2))
    cap = ((2*v[0]+tick-1)//tick)*tick
    candidates = range(0,cap+tick,tick)
    actions = range(0,cap+2*tick,tick)
    # Against a fixed rival all bids above the rival give the identical payoff.
    best1 = {y:max(payoff(z,y)[0] for z in actions) for y in candidates}
    best2 = {x:max(payoff(x,z)[1] for z in actions) for x in candidates}
    counts = Counter()
    for x in candidates:
        for y in candidates:
            first, second = payoff(x,y)
            actual = first == best1[y] and second == best2[x]
            if x < y:
                predicted = x == 0 and y*(q[0]-e[0]) >= d*v[0]
            elif x == y:
                predicted = numerator == denominator and v[1] <= x and x*(q[0]-e[0]) <= d*v[0]
            else:
                predicted = (x-y == tick and numerator < denominator and
                             (denominator-numerator)*d*(y-v[1]+tick) >= denominator*(e[1]-residual[1])*tick
                             and y*(q[0]-e[0]) <= d*v[0])
            if actual != predicted:
                raise ArithmeticError((q,v,e,tick,numerator,denominator,x,y,actual,predicted))
            counts["profiles"] += 1
            counts["equilibria"] += actual
    return counts

def main():
    summary=Counter()
    for primitives in [(10,(8,6),(10,4),(1,3)),(12,(9,8),(16,6),(2,5)),(13,(10,9),(18,6),(2,5))]:
        for tick in (1,2):
            for num in range(17):
                summary.update(inspect(*primitives,tick,num,16))
                summary["instances"] += 1
    if summary["instances"] != 102 or summary["equilibria"] <= 0:
        raise ValueError("Incomplete validation")
    print(json.dumps(dict(summary),sort_keys=True))
if __name__ == "__main__":
    main()

