"""Pinned finite rational diagnostics for161. Run in own Colab Linux only."""
from fractions import Fraction as Q
import itertools
import json
import math
import sys
from exact159 import need, zero, eye, tr, mul, add, rank, inertia, low, psd


def geometry(D, n):
    points = list(itertools.product(range(n), repeat=D))
    where = {x: i for i, x in enumerate(points)}
    rows, ends = [], []
    for a, x in enumerate(points):
        for i in range(D):
            y = list(x)
            y[i] = (y[i]+1) % n
            b = where[tuple(y)]
            row = [Q(0)]*len(points)
            row[a], row[b] = Q(-1), Q(1)
            rows.append(row)
            ends.append((a, b))
    return points, rows, ends


def form(rows, values):
    N = len(rows[0])
    out = zero(N)
    for row, val in zip(rows, values):
        support = [i for i, x in enumerate(row) if x]
        for i in support:
            for j in support:
                out[i][j] += val*row[i]*row[j]
    return out


def inv_power(x, D):
    need(x > 0, 'positive inverse power domain')
    if D % 2 == 0:
        return x**(-D//2)
    a, b = math.isqrt(x.numerator), math.isqrt(x.denominator)
    need(a*a == x.numerator and b*b == x.denominator,
         'odd-dimensional rational square fixture')
    return Q(b, a)**D


def components(N, ends):
    parent = list(range(N))
    def find(i):
        while parent[i] != i:
            i = parent[i]
        return i
    for a, b in ends:
        parent[find(a)] = find(b)
    return len({find(i) for i in range(N)})


rejected = []


def reject(name, validator):
    try:
        validator()
    except ValueError:
        rejected.append(name)
        return
    raise ValueError('Mutation incorrectly accepted: '+name)


def test_case(D, n, mode):
    points, d, ends = geometry(D, n)
    N = len(points)
    rows = [r[:] for r in d]
    m, c = Q(64), Q(1, 4)
    values = [m]*len(rows)
    if mode in ('zero_star', 'tiny_star'):
        for j, (a, b) in enumerate(ends):
            if a == 0 or b == 0:
                values[j] = Q(0) if mode == 'zero_star' else Q(1, 4096)
    elif mode == 'one_negative':
        values[0] = Q(-1024)
    elif mode == 'mixed_rotated':
        for x in range(N):
            j = x*D
            # Local rational orthogonal eigenspaces; directions mix.
            a, b = d[j], d[j+1]
            sign = 1 if x % 2 else -1
            rows[j] = [Q(3, 5)*u+sign*Q(4, 5)*v for u, v in zip(a, b)]
            rows[j+1] = [-sign*Q(4, 5)*u+Q(3, 5)*v for u, v in zip(a, b)]
            values[j] = Q(-1) if x % 3 == 0 else Q(1, 4096)
            values[j+1] = Q(0) if x % 3 == 1 else Q(64)
    else:
        raise ValueError('Unknown fixture mode')
    H = form(rows, values)
    alpha = Q(D, 2)*Q(D, D-2)**(D-1)*Q(3, 4)**D
    scale = alpha/inv_power(c, D)
    weights = [None if x <= 0 else scale*inv_power(x, D) for x in values]
    mandatory = [j for j, x in enumerate(values) if x <= 0]
    cap = [j for j, x in enumerate(values) if x <= 0 or weights[j] >= 1]
    sparse = [j for j, x in enumerate(values) if x < m]
    k = low(H, c)
    result = {'D': D, 'n': n, 'mode': mode, 'low_count': k}
    bounds = {}
    for label, S in (('mandatory', mandatory), ('capped', cap), ('sparse', sparse)):
        selected = set(S)
        need(all(j in selected for j in mandatory), 'all nonpositive channels selected')
        R = rank([rows[j] for j in S])
        repaired = [Q(1024) if j in selected else x for j, x in enumerate(values)]
        # Repair must be strictly above every selected eigenvalue.
        need(all(repaired[j] > values[j] for j in S), 'strict positive repair')
        HT = form(rows, repaired)
        update = add(HT, H, -1)
        need(psd(update) and rank(update) == R, 'actual PSD repair/update rank')
        need(k <= low(HT, c)+R, 'strict-threshold rank interlacing')
        moment = sum((inv_power(x, D) for j, x in enumerate(values)
                      if j not in selected), Q(0))
        bound = 1+R+scale*moment
        need(k <= bound, 'selected-channel count bound')
        bounds[label] = bound
        result[label] = {'channels': len(S), 'actual_rank': R,
                         'bound': str(bound), 'positive_unselected_moment': str(moment)}
        if mode != 'mixed_rotated':
            cc = components(N, [ends[j] for j in S])
            need(R == N-cc, 'actual graph incidence rank')
            result[label]['components'] = cc
    cap_local = 1+len(mandatory)+sum((min(Q(1), w) for w in weights if w is not None), Q(0))
    need(k <= min(N, cap_local), 'local capped bound')
    need(bounds['capped'] <= bounds['mandatory'], 'capped actual-rank improvement')
    sparse_coarse = 1+len(sparse)+scale*len(rows)*inv_power(m, D)
    need(k <= sparse_coarse, 'explicit sparse-channel budget')
    result.update(local_capped_bound=str(cap_local), sparse_coarse_bound=str(sparse_coarse))
    if mode == 'zero_star':
        need(inertia(H)[2] == 2 and k >= 2, 'isolated vertex and nonempty complement kernel')
        omitted = 1+sum((w for w in weights if w is not None), Q(0))
        reject('zero_star_omitted_defect', lambda: need(k <= omitted, 'defect omitted'))
        true_R = result['sparse']['actual_rank']
        reject('altered_actual_repair_rank', lambda: need(rank([rows[j] for j in sparse]) == true_R-1, 'rank'))
        cc = result['sparse']['components']
        reject('altered_graph_component_count', lambda: need(true_R == N-(cc+1), 'components'))
        reject('nonpositive_channel_dropped', lambda: need(all(j in set(sparse[1:]) for j in mandatory), 'missing zero'))
    if mode == 'tiny_star':
        need(k >= 2, 'near-zero isolated-star strict low modes')
        raw = sum((inv_power(x, D) for x in values), Q(0))
        need(raw > 1000000 and result['sparse']['channels'] == 2*D,
             'near-zero full moment versus fixed sparse count')
        result['full_inverse_moment'] = str(raw)
    if mode == 'one_negative':
        a, b = ends[0]
        v = [Q(int(i == b)-int(i == a)) for i in range(N)]
        norm = sum(x*x for x in v)
        rayleigh = sum((H[i][j]*v[i]*v[j] for i in range(N) for j in range(N)), Q(0))/norm
        expected = -2*Q(1024)+(2*D-1)*m
        need(rayleigh == expected and result['sparse']['actual_rank'] == 1,
             'single negative channel exact penalty witness')
        reject('altered_single_edge_rayleigh', lambda: need(rayleigh == expected+1, 'Rayleigh'))
        reject('uniform_penalty_ignores_negative_depth', lambda: need(rayleigh+c >= c, 'coercivity'))
        result.update(trial_rayleigh=str(rayleigh), normalized_penalty_lower_bound=str(c-rayleigh))
    if mode == 'mixed_rotated':
        reject('signed_channel_inverse_power', lambda: inv_power(Q(-1), D))
    return result


def main():
    need(sys.platform.startswith('linux'), 'Own Colab Linux only')
    fixtures = [test_case(3, 3, name) for name in ('zero_star', 'tiny_star', 'one_negative')]
    fixtures.append(test_case(4, 2, 'mixed_rotated'))
    need(len(fixtures) == 4 and len(rejected) == 7, 'explicit final fixture/mutation counter')
    print(json.dumps({'status': 'EXACT_SPARSE_DIAGNOSTICS_PASS', 'fixtures': fixtures,
                      'rejected_mutations': rejected, 'mutation_count': 7,
                      'all_size_theorem_verified': False, 'independent_review': False,
                      'Lean_verified': False}, sort_keys=True, indent=2))


if __name__ == '__main__':
    main()
