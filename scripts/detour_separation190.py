"""Unexecuted preparation190. Scientific replay belongs only on own Colab Linux."""
from collections import Counter
from fractions import Fraction
from itertools import product
from pathlib import Path
import hashlib
import json
import platform


def require(condition, message):
    if not condition:
        raise ValueError(message)


def shift(x, i, step, n):
    y = list(x)
    y[i] = (y[i] + step) % n
    return tuple(y)


def distance(x, y, n):
    return max(min(abs(a-b), n-abs(a-b)) for a, b in zip(x, y))


def edge_uses(D, n, weak, sigma=None, wrong_reverse_start=False):
    sigma = sigma or tuple((i+1) % D for i in range(D))
    uses = Counter()
    for x in weak:
        for i in range(D):
            j = sigma[i]
            y = shift(x, j, -1, n)
            z = shift(y, i, 1, n)
            starts = [(x if wrong_reverse_start else y, j), (y, i), (z, j)]
            require(len(set(starts)) == 3, 'Repeated edge in an individual path')
            require(all(start not in weak for start, _ in starts), 'Weak bypass start')
            uses.update(starts)
    return uses


def check_detours(D, n, weak, **kwargs):
    require(all(distance(x, y, n) >= 2 for x in weak for y in weak if x != y),
            'Distance2 hypothesis failed')
    uses = edge_uses(D, n, weak, **kwargs)
    bound = 1 if D >= 3 else 2
    require(max(uses.values(), default=0) <= bound, 'Edge-use congestion failed')
    return max(uses.values(), default=0)


def parity_fixture(D, n, collapse_two_cycle=False, reverse_potential=False):
    require(n % 2 == 0 and n >= 4, 'Parity needs even n>=4')
    m = n//2
    z = [1, -1] + [0]*(m-2)
    layer = [z[((s+1)//2) % m] for s in range(n)]
    psi = [0]
    for s in range(1, n):
        psi.append(psi[-1] + layer[s])
    points = list(product(range(n), repeat=D))
    f = {x: layer[sum(x) % n] for x in points}
    potential = {x: psi[sum(x) % n] for x in points}
    weak = {x for x in points if sum(x) % 2 == 0}
    require(all(shift(x, i, 1, n) not in weak for x in weak for i in range(D)),
            'Nearest-neighbour independence failed')
    A = {}
    for x in points:
        q1 = potential[x] - potential[shift(x, 1, -1, n)]
        q2 = -potential[x] + potential[shift(x, 0, -1, n)]
        if reverse_potential:
            q1 = -q1
        A[x] = (q1, q2) + (0,)*(D-2)
        require(A[x] == (f[x], -f[x]) + (0,)*(D-2), 'Coexact preimage identity failed')
    require(sum(f.values()) == 0, 'Mean failed')
    require(all(sum(A[x][i]-A[shift(x, i, -1, n)][i] for i in range(D)) == 0
                for x in points), 'Backward divergence failed')
    Ew = sum((f[shift(x, i, 1, n)]-f[x])**2 for x in weak for i in range(D))
    Es = sum((f[shift(x, i, 1, n)]-f[x])**2 for x in points if x not in weak
             for i in range(D))
    norm = sum(value*value for value in f.values())
    cycle = sum((z[(r+1) % m]-z[r])**2 for r in range(m))
    if collapse_two_cycle and m == 2:
        cycle //= 2
    require(Es == 0 and Ew > 0, 'Strong zero/weak positivity failed')
    require(Ew == D*n**(D-1)*cycle, 'Positive-start cycle multiplicity failed')
    require(norm == 2*n**(D-1)*sum(v*v for v in z), 'Layer norm failed')
    epsilon, H = Fraction(1, 7), Fraction(11)
    energyA = sum((epsilon if x in weak else H)*sum(
        (A[shift(x, i, 1, n)][j]-A[x][j])**2 for j in range(D))
        for x in points for i in range(D))
    normA = sum(sum(v*v for v in row) for row in A.values())
    require(energyA == 2*epsilon*Ew and normA == 2*norm,
            'Actual weighted vector energy/norm failed')
    require(energyA <= 2*D*epsilon*normA, 'Coexact subspace quotient bound failed')
    return {'D': D, 'n': n, 'weak': len(weak), 'Es': Es, 'Ew': Ew,
            'norm': norm, 'energyA': str(energyA), 'normA': normA}


def rejected(action, label):
    try:
        action()
    except ValueError:
        return label
    raise ValueError('Mutated acceptance incorrectly passed: '+label)


def main():
    require(platform.system() == 'Linux', 'Scientific replay only in own Colab Linux')
    positive = []
    for D in (2, 3, 4):
        for n in (3, 4, 5, 6):
            coordinates = range(0, n if n % 2 == 0 else n-1, 2)
            lattice = set(product(coordinates, repeat=D))
            shifted = {shift(x, 0, 1, n) for x in lattice}
            for tag, weak in [('empty', set()), ('lattice', lattice), ('shifted', shifted)]:
                positive.append({'D': D, 'n': n, 'kind': tag,
                                 'maximum_uses': check_detours(D, n, weak)})
    for n in (4, 5, 6):
        weak = {(0, 1), (1, n-1)}
        maximum = check_detours(2, n, weak)
        require(maximum == 2, 'D2 double-use witness missing')
        positive.append({'D': 2, 'n': n, 'kind': 'D2-double-use', 'maximum_uses': maximum})
    parity = [parity_fixture(D, n) for D in (2, 3, 4) for n in (4, 6, 8)]
    bad_sigma_weak = {(0, 1, 0, 0), (1, 3, 0, 0)}
    parity_weak = {x for x in product(range(4), repeat=3) if sum(x) % 2 == 0}
    mutations = [
        rejected(lambda: check_detours(3, 4, {(0, 0, 0)}, wrong_reverse_start=True),
                 'wrong-positive-start-of-reversed-edge'),
        rejected(lambda: check_detours(4, 4, bad_sigma_weak, sigma=(1, 0, 3, 2)),
                 'replace-cycle-by-two-cycles'),
        rejected(lambda: edge_uses(3, 4, parity_weak),
                 'nearest-neighbour-independent-set-substituted'),
        rejected(lambda: parity_fixture(3, 4, collapse_two_cycle=True),
                 'collapse-induced-two-cycle-positive-starts'),
        rejected(lambda: parity_fixture(3, 6, reverse_potential=True),
                 'flip-actual-potential-component-sign'),
    ]
    require(len(positive) == 39 and len(parity) == 9 and len(mutations) == 5,
            'Explicit acceptance counters failed')
    payload = {'positive_count': len(positive), 'parity_count': len(parity),
               'mutation_count': len(mutations), 'positive': positive,
               'parity': parity, 'rejected_mutations': mutations,
               'all_size_proof': False, 'independent_replication': False,
               'formal_verification': False}
    raw = (json.dumps(payload, sort_keys=True, separators=(',', ':'))+'\n').encode()
    Path('payload190.json').write_bytes(raw)
    print('FINITE190_COMPLETE_SHA256='+hashlib.sha256(raw).hexdigest())


if __name__ == '__main__':
    main()
