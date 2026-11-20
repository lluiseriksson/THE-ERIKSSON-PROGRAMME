"""Exact checks of monthly retention profiles and minimum cash transfers."""
from fractions import Fraction as F
from itertools import accumulate, product
import json
from pathlib import Path


def need(condition, reason):
    if not condition:
        raise ValueError(reason)


def profile(caps, total, payments):
    """Least safe retained capacity after each date, including starting cash."""
    size = len(payments)
    need(size == len(caps) and 0 <= total <= sum(caps), 'Invalid horizon or cash total')
    need(all(x >= 0 for x in (*caps, *payments)), 'Negative cash cap or service')
    h = list(accumulate(caps, initial=0))
    d = list(accumulate(payments, initial=0))
    slack = h[-1] - total
    suffix = [d[t]-h[t] for t in range(size+1)]
    for t in reversed(range(size)):
        suffix[t] = max(suffix[t], suffix[t+1])
    k = 0
    result = []
    for i in range(size):
        k = max(i, k)
        while k < size and h[k+1] <= h[i] + slack:
            k += 1
        amount = d[k] - d[i]
        if k < size:
            amount = max(amount, h[i] + slack - d[i] + suffix[k+1])
        result.append(amount)
    return result


def distance(nominal, caps, pays, retained):
    costs = []
    slack = sum(caps) - sum(nominal)
    for i, balance in enumerate(retained):
        for stop in range(i+1, len(caps)+1):
            months = slice(i, stop)
            due = sum(pays[months])
            boundary = balance + sum(nominal[months]) - due
            need(boundary >= 0, 'Nominal path already fails')
            if balance + max(0, sum(caps[months])-slack) < due:
                costs.append(boundary)
    return min(costs, default=None)


def survives(receipts, payments, retained):
    cash = retained[0]
    for month, (receipt, due) in enumerate(zip(receipts, payments)):
        cash += receipt - due
        if cash < 0:
            return False
        if month+1 < len(payments):
            cash = min(cash, retained[month+1])
    return True


def small_panels():
    count = profiles = transfers = 0
    for caps in product(range(3), repeat=3):
        all_paths = list(product(*(range(n+1) for n in caps)))
        for total in range(sum(caps)+1):
            paths = [p for p in all_paths if sum(p) == total]
            for pays in product(range(2), repeat=3):
                k = profile(caps, total, pays)
                direct = [max([0]+[sum(pays[i:j])-sum(p[i:j]) for p in paths for j in range(i+1,4)]) for i in range(3)]
                need(k == direct, 'Suffix envelope disagrees with direct paths')
                profiles += 1
                for kept in product(range(3), repeat=3):
                    good, bad = [], []
                    for path in paths:
                        (good if survives(path, pays, kept) else bad).append(path)
                    need((not bad) == all(x>=y for x,y in zip(kept,k)), 'Simulation mismatch')
                    count += 1
                    for path in good:
                        radius = distance(path, caps, pays, kept)
                        if bad:
                            cost = min(sum(abs(x-y) for x,y in zip(path,p))//2 for p in bad)
                            need(radius is not None and cost == radius+1, 'Wrong integer failure radius')
                        else:
                            need(radius is None, 'Spurious vulnerable interval')
                        transfers += 1
    return dict(profiles=profiles, retention_panels=count, nominal_paths=transfers)


def main():
    data = json.loads(Path('campus-table.json').read_text())
    need(data['annual_service'] == 112 and data['cash'] == [175,132,82] and data['combined_reserves'] == [95,122,165], 'Source rows differ')
    pays = [F(data['annual_service'],12)]*12
    base, moderate, severe = data['cash']
    results = [profile([v]*12, v, pays)[0] for v in data['cash']]
    need(results == [F(308,3)]*3, 'Annual scenarios differ')
    retained = [95]+[1000]*11
    rho = distance([F(base,12)]*12,[base]*12,pays,retained)
    need(rho == F(611,4), 'Base timing radius')
    h = F(502,3)
    need(profile([h]*12,base,pays)[0] == 95 and profile([h+F(1,100)]*12,base,pays)[0] > 95, 'Receipt cap threshold')
    need(not survives([3,0,0],[0,1,1],[0,1,3]) and survives([3,0,0],[0,1,1],[0,2,3]), 'Interior cash sweep')
    try:
        profile([2,2], 5, [0,1])
    except ValueError:
        pass
    else:
        raise RuntimeError('Infeasible receipt mutation accepted')
    counts = small_panels()
    need(all(counts.values()), 'No exhaustive tests ran')
    print(json.dumps(dict(counts=counts, robust_reserve=str(results[0]), base_radius=str(rho), cap_threshold=str(h), usable_fractions=[str(results[i]/data['combined_reserves'][i]) for i in [1,2]]),sort_keys=True,indent=2))


if __name__ == '__main__':
    main()

