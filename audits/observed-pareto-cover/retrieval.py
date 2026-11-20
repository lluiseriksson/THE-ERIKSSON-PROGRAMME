"""Exact finite checks for observed one-sided Pareto coverage (unit query costs)."""
from collections import Counter
from functools import lru_cache
from itertools import combinations, product
import json


def require(condition, message):
    if not condition:
        raise ValueError(message)


def projections(worlds, order):
    """Uniform law on the listed worlds; compare exact multiplicities separately."""
    for subset in combinations(range(len(worlds[0])), order):
        yield Counter(tuple(row[i] for i in subset) for row in worlds)


def same_marginals(left, right, order):
    for a, b in zip(projections(left, order), projections(right, order)):
        if a.keys() != b.keys() or any(a[k]*len(right) != b[k]*len(left) for k in a):
            return False
    return True


def optimal_depth(worlds, baseline=2):
    """All costs equal, scalar loss, zero tolerance. Only queried items can witness."""
    n = len(worlds[0])
    groups = [dict() for _ in range(n)]
    failures = [0] * (1 << n)
    for idx, row in enumerate(worlds):
        truth = min((baseline, *row))
        bit = 1 << idx
        for j, value in enumerate(row):
            groups[j][value] = groups[j].get(value, 0) | bit
        if baseline > truth:
            winners = sum(1 << j for j, value in enumerate(row) if value == truth)
            remaining = ((1 << n) - 1) ^ winners
            mask = remaining
            while True:
                failures[mask] |= bit
                if not mask:
                    break
                mask = (mask - 1) & remaining

    @lru_cache(None)
    def solve(queried, compatible):
        if not failures[queried] & compatible:
            return 0
        return 1 + min(
            max(solve(queried | (1 << j), compatible & branch)
                for branch in groups[j].values() if compatible & branch)
            for j in range(n) if not queried & (1 << j)
        )

    all_worlds = (1 << len(worlds)) - 1
    return dict(adaptive=solve(0, all_worlds),
                fixed=min(mask.bit_count() for mask, bad in enumerate(failures) if not bad))


def sharing(m, t):
    full, joint = [], []
    for bits in product((0, 2), repeat=m):
        signal = bits.index(0) + 1 if 0 in bits else 0
        for digits in product(range(m + 1), repeat=t + 1):
            row = bits + tuple(3 + v for v in digits)
            full.append(row)
            if sum(digits) % (m + 1) == signal:
                joint.append(row)
    return full, joint


def box_test():
    """Direct scenario test with exact costs, two coordinates and nonzero tolerance."""
    costs = (1, 2, 2, 3)
    choices = [((1, 3), (3, 5)), ((2, 1), (4, 2)), ((1, 1), (2, 4)), ((3, 4), (5, 5))]
    worlds = list(product(*choices))
    checks = 0
    for eps in (0, 1, 2):
        def covers(r, j, a, b):
            return costs[r] <= costs[j] and all(x <= y + eps for x, y in zip(a, b))
        for mask in range(1 << len(costs)):
            selected = [r for r in range(len(costs)) if mask & (1 << r)]
            direct = all(all(any(covers(r,j,row[r],row[j]) for r in selected)
                             for j in range(len(costs))) for row in worlds)
            graph = all(j in selected or any(covers(r,j,choices[r][1],choices[j][0])
                                             for r in selected) for j in range(len(costs)))
            require(graph == direct, "Corner certificate disagrees with scenario coverage")
            checks += 1
    return checks


def main():
    report = dict(box_subset_tests=box_test(), parity=[], sharing=[])
    for k in range(1, 6):
        full = list(product((0, 2), repeat=k+1))
        even = [row for row in full if row.count(0) % 2 == 0]
        a, b = optimal_depth(full), optimal_depth(even)
        require(same_marginals(full, even, k), "Parity marginal disagreement")
        require(a['adaptive']==k+1 and b['adaptive']==k, "Parity budget mismatch")
        report['parity'].append(dict(k=k, product=a, parity=b))
    for m, t in [(3,1),(4,1),(5,2)]:
        full, joint = sharing(m, t)
        a, b = optimal_depth(full), optimal_depth(joint)
        require(same_marginals(full, joint, t), "Share marginal disagreement")
        require(a==dict(adaptive=m,fixed=m) and b==dict(adaptive=min(m,t+2),fixed=m),
                "Adaptive or fixed budget mismatch")
        report['sharing'].append(dict(m=m,t=t,product=a,joint=b,worlds=[len(full),len(joint)]))
    # Negative control: alter a candidate outcome without altering the test routine.
    full, joint = sharing(3,1)
    changed = list(joint)
    changed[0] = (2,) + changed[0][1:]
    require(not same_marginals(full, changed, 1), "Mutated marginal accepted")
    print(json.dumps(report, sort_keys=True, indent=2))


if __name__ == "__main__":
    main()

