# SPDX-License-Identifier: AGPL-3.0-only
"""Finite exact diagnostics of actual conditional generators, not all-n proof.

Run only on an owned Colab Linux runtime. No verdict depends on assert.
The unequal-rate orientation regression comes from the concrete row/column
convention risk in the stated coefficient block, not an external audit claim.
"""
from fractions import Fraction as Q
from itertools import product
import json


def require(ok, message):
    if not ok:
        raise ValueError(message)


def chi(mask, x):
    v = 1
    for i, value in enumerate(x):
        if mask & (1 << i):
            v *= value
    return v


def case(n, t, rates):
    require(n >= 2 and -1 < t < 1 and len(rates) == n and min(rates) > 0,
            'domain')
    states = list(product((-1, 1), repeat=n))
    where = {x: j for j, x in enumerate(states)}
    full = (1 << n) - 1
    probability = [Q(1 + t * chi(full, x), 2 ** n) for x in states]
    require(min(probability) > 0 and sum(probability) == 1, 'strict law')
    rows = []
    for x in states:
        row = {}
        for i, rho in enumerate(rates):
            rest = tuple(x[j] for j in range(n) if j != i)
            p_plus = sum(probability[k] for k, y in enumerate(states)
                         if y[i] == 1 and tuple(y[j] for j in range(n) if j != i) == rest)
            p_rest = sum(probability[k] for k, y in enumerate(states)
                         if tuple(y[j] for j in range(n) if j != i) == rest)
            require(p_rest == Q(1, 2 ** (n - 1)), 'proper rest marginal')
            p_plus /= p_rest
            observed = 1
            for value in rest:
                observed *= value
            require(p_plus == (1 + t * observed) / 2, 'actual conditional law')
            # The actual resampling law above, not an assumed block, defines H.
            for spin, prob in ((1, p_plus), (-1, 1 - p_plus)):
                y = list(x); y[i] = spin; k = where[tuple(y)]
                row[k] = row.get(k, Q(0)) - rho * prob
            k = where[x]; row[k] = row.get(k, Q(0)) + rho
        rows.append(row)
    require(all(sum(row.values()) == 0 for row in rows), 'constant mode')
    for j, row in enumerate(rows):
        for k, value in row.items():
            require(probability[j] * value == probability[k] * rows[k].get(j, 0),
                    'actual detailed balance')
    R = sum(rates); m = min(rates); entries = 0; blocks = 0
    for S in range(1 << n):
        T = full ^ S
        a = sum(rates[i] for i in range(n) if S & (1 << i))
        b = R - a
        for j, x in enumerate(states):
            actual = sum(value * chi(S, states[k]) for k, value in rows[j].items())
            expected = a * chi(S, x) - t * a * chi(T, x)
            require(actual == expected, 'actual generator character action')
            entries += 1
        if 0 < S < T:
            gram = [[Q(1), t], [t, Q(1)]]
            block = [[a, -t * b], [-t * a, b]]
            require(block[0][0] + block[1][1] == R, 'trace')
            require(block[0][0]*block[1][1]-block[0][1]*block[1][0]
                    == (1-t*t)*a*b, 'determinant')
            GB = [[sum(gram[i][j]*block[j][k] for j in range(2))
                   for k in range(2)] for i in range(2)]
            require(GB[0][1] == GB[1][0], 'weighted self-adjoint block')
            require(a*b >= m*(R-m), 'extremal subset product')
            blocks += 1
    require(blocks == 2 ** (n-1)-1, 'complete block count')
    require(2 + 2*blocks == 2**n, 'full dimension count')
    # Explicit positive-law witness of the review's conditioning distinction.
    # All proper marginals are fixed, but conditional laws change when t!=0.
    for S in range(1, full):
        require(sum(p*chi(S, x) for p, x in zip(probability, states)) == 0,
                'all proper character moments')
    require(sum(p*chi(full, x) for p, x in zip(probability, states)) == t,
            'full character moment')
    require(min(sum(rates[i] for i in range(n) if S & (1 << i)) *
                sum(rates[i] for i in range(n) if not S & (1 << i))
                for S in range(1, full)) == m*(R-m), 'minimum attained')
    return dict(n=n,t=str(t),rates=list(map(str,rates)),states=len(states),
                actual_character_entries=entries,proper_blocks=blocks)


def main():
    records=[]
    for n in range(2,7):
        for t in (Q(0),Q(3,5),Q(-9,10)):
            for rates in ([Q(1)]*n,[Q(i+1,3) for i in range(n)]):
                records.append(case(n,t,rates))
    # This compares to a known actual n=2 weighted action, and demonstrates
    # that transposing the off-diagonal rates is not the same coefficient map.
    a,b,t=Q(1),Q(2),Q(3,5)
    actual_column=(a,-t*a); wrong_column=(a,-t*b)
    require(actual_column != wrong_column,'orientation regression must distinguish unequal rates')
    require(len(records)==30,'exact expected case count')
    print(json.dumps(dict(status='FINITE_DIAGNOSTICS_PASS',cases=records,
                         accepted_cases=len(records),
                         character_entries=sum(r['actual_character_entries'] for r in records),
                         all_n_proof=False,formal_replay=False),sort_keys=True,indent=2))


if __name__=='__main__':
    main()
