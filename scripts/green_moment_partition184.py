# SPDX-License-Identifier: AGPL-3.0-or-later
"""Selected exact finite controls for research184. Run only on own Colab Linux.

This verifies small actual graph/Green matrices and finite mode blocks. It is
not an all-size proof, Lean check, novelty audit or independent replication.
"""
from fractions import Fraction as F
from itertools import product
from math import comb, prod
import hashlib
import json


class Rejected(ValueError):
    pass


def need(condition, message):
    if not condition:
        raise Rejected(message)


def matrix(n):
    return [[F(0) for _ in range(n)] for _ in range(n)]


def mul(a, b):
    return [[sum((x*y for x, y in zip(row, col)), F(0))
             for col in zip(*b)] for row in a]


def inverse(a):
    n = len(a)
    b = [row[:] + [F(i == j) for j in range(n)] for i, row in enumerate(a)]
    for k in range(n):
        pivot = next((i for i in range(k, n) if b[i][k]), None)
        need(pivot is not None, 'singular matrix')
        b[k], b[pivot] = b[pivot], b[k]
        d = b[k][k]
        b[k] = [x/d for x in b[k]]
        for i in range(n):
            if i != k:
                d = b[i][k]
                b[i] = [x-d*y for x, y in zip(b[i], b[k])]
    return [row[n:] for row in b]


def graph(lengths, periodic, mu):
    vertices = list(product(*(range(l) for l in lengths)))
    index = {x: i for i, x in enumerate(vertices)}
    a = matrix(len(vertices))
    for x in vertices:
        for j, l in enumerate(lengths):
            if x[j]+1 == l and not periodic[j]:
                continue
            y = list(x)
            y[j] = (x[j]+1) % l
            u, v = index[x], index[tuple(y)]
            if u != v:
                a[u][u] += mu
                a[v][v] += mu
                a[u][v] -= mu
                a[v][u] -= mu
    return a


def green(a):
    n = len(a)
    p = [[F(1, n) for _ in range(n)] for _ in range(n)]
    b = inverse([[a[i][j]+p[i][j] for j in range(n)] for i in range(n)])
    return [[b[i][j]-p[i][j] for j in range(n)] for i in range(n)]


def verify_green(a, g):
    n = len(a)
    need(all(sum(row) == 0 for row in g), 'Green constant kernel')
    need(all(g[i][j] == g[j][i] for i in range(n) for j in range(n)), 'Green symmetry')
    need(mul(a, g) == [[F(i == j)-F(1, n) for j in range(n)] for i in range(n)],
         'Green inverse identity')
    trace = sum(g[i][i] for i in range(n))
    resistance_sum = sum((g[i][i]+g[j][j]-2*g[i][j]
                          for i in range(n) for j in range(i)), F(0))
    need(resistance_sum == n*trace, 'Kirchhoff identity')


def psd(a):
    a = [row[:] for row in a]
    while a:
        need(all(a[i][j] == a[j][i] for i in range(len(a)) for j in range(len(a))),
             'PSD symmetry')
        need(all(a[i][i] >= 0 for i in range(len(a))), 'negative PSD diagonal')
        k = next((i for i in range(len(a)) if a[i][i] > 0), None)
        if k is None:
            need(all(x == 0 for row in a for x in row), 'zero diagonal nonzero cross term')
            return
        rest = [i for i in range(len(a)) if i != k]
        a = [[a[i][j]-a[i][k]*a[k][j]/a[k][k] for j in rest] for i in rest]


def trace1(g):
    return sum((g[i][i] for i in range(len(g))), F(0))


def trace2(g):
    return sum((x*x for row in g for x in row), F(0))


def ceil(x):
    return -((-x.numerator)//x.denominator)


def mode_blocks(lengths, overlap=False):
    m = min(lengths)
    count = max(0, m.bit_length()-3)
    seen = set()
    records = []
    for j in range(count):
        t = F(2**(j+1), m)
        modes = list(product(*(range(ceil(t*l), ceil(2*t*l)+(1 if overlap else 0))
                                for l in lengths)))
        need(not seen.intersection(modes), 'mode block overlap')
        seen.update(modes)
        need(all(all(0 < F(k, l) < 2*t for k, l in zip(mode, lengths)) for mode in modes),
             'mode block endpoint')
        need(len(modes) >= prod(lengths)*t**len(lengths)/2**len(lengths), 'mode count')
        records.append({'t': str(t), 'modes': len(modes)})
    return records


def reject(operation):
    try:
        operation()
    except Rejected:
        return
    raise Rejected('mutation was not rejected')


def main():
    controls = []
    gs = {}
    for r in range(5):
        lengths = (2,)*r + (1,)*(4-r)
        a = graph(lengths, (True,)*4, F(4))
        g = green(a)
        verify_green(a, g)
        expected = sum((F(comb(r, k), (16*k)**2) for k in range(1, r+1)), F(0))
        need(trace2(g) == expected, 'actual matrix versus exact product spectrum')
        need((256*trace2(g) <= 1) == (r <= 1), 'critical passing cell classification')
        gs[r] = (a, g)
        if r:
            cut = graph(lengths, (False,)*4, F(4))
            gc = green(cut)
            verify_green(cut, gc)
            need(trace2(gc) == 4*trace2(g), 'n2 path versus duplicated cycle edges')
        controls.append({'r': r, 'vertices': 2**r, 'critical_c16_trace': str(256*trace2(g))})
    a, g = gs[4]
    n = len(a)
    psd([[a[i][j]+F(16, n)-16*F(i == j) for j in range(n)] for i in range(n)])
    need(256*trace2(g) == F(865, 144), 'critical root value')
    need(256*trace2(gs[1][1]) == 1, 'passing full-period line')
    lines = [set((x,)+tail for x in range(2)) for tail in product(range(2), repeat=3)]
    need(len(lines) == 8 and sum(map(len, lines)) == 16 and
         len(set().union(*lines)) == 16, 'eight actual disjoint covering lines')
    cut3 = graph((2, 2, 2), (False,)*3, F(4))
    g3 = green(cut3)
    verify_green(cut3, g3)
    need(trace1(g3) == F(29, 48), 'D3 cut exact trace')
    cyclic3 = graph((2, 2, 2), (True,)*3, F(4))
    need(trace1(green(cyclic3)) == F(29, 96), 'D3 cyclic exact trace')
    block_cases = []
    for shape in [(7, 7, 7), (8, 8, 8), (9, 11, 13), (8, 9, 10, 11),
                  (16, 16, 16, 16), (32, 33, 35, 40)]:
        blocks = mode_blocks(shape)
        block_cases.append({'shape': shape, 'blocks': blocks})
    mutations = []
    def mutated_green():
        bad = [[g[i][j]+F(1, n) for j in range(n)] for i in range(n)]
        verify_green(a, bad)
    operations = [
        ('kernel included', mutated_green),
        ('lost periodic multiplicity', lambda: need(trace2(green([[x/2 for x in row] for row in a]))
                                                   == F(865, 36864), 'edge multiplicity')),
        ('trace normalized by volume', lambda: need(trace2(g)/n == F(865, 36864), 'unnormalized trace')),
        ('wrong energy scale', lambda: need(trace2(green(graph((2,)*4, (True,)*4, F(1))))
                                             == F(865, 36864), 'n squared coefficient')),
        ('critical multiplicity omitted', lambda: need(trace2(g) == sum((F(1, (16*k)**2)
                                                   for k in range(1, 5)), F(0)), 'spectral multiplicity')),
        ('shell endpoint included', lambda: mode_blocks((16,)*4, overlap=True)),
    ]
    for label, operation in operations:
        reject(operation)
        mutations.append(label)
    need(len(controls) == 5 and len(block_cases) == 6 and len(mutations) == 6, 'acceptance counters')
    payload = {'status': 'SELECTED_EXACT_FINITE_CONTROLS', 'controls': controls,
               'mode_blocks': block_cases, 'mutations_rejected': mutations,
               'critical_D4_n2_c16_min_cells': 8, 'actual_global_mean_cells': 1,
               'limits': 'Analytical asymptotic proof not verified by these finite cases; no Lean, independent review or physical claim.'}
    raw = (json.dumps(payload, sort_keys=True, separators=(',', ':'))+'\n').encode()
    print(raw.decode(), end='')
    print('PAYLOAD_SHA256='+hashlib.sha256(raw).hexdigest())


if __name__ == '__main__':
    main()
