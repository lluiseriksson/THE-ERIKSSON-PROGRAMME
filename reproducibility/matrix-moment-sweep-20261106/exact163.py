"""Own Colab rational threshold/interaction diagnostics; no universal verifier."""
from fractions import Fraction as Q
import json
import sys
from exact159 import need, zero, eye, tr, mul, add, inv, inertia, low, psd
from exact162 import geometry, form


def dot(a, b):
    return sum((x*y for x, y in zip(a, b)), Q(0))


def apply(a, x):
    return [dot(r, x) for r in a]


def fixture(D, n, h):
    points, scalar, ends = geometry(D, n)
    V, N = len(points), len(points)*h
    scalarL = form(scalar, [Q(1)]*len(scalar))
    scalarP = [[Q(1, V)]*V for _ in range(V)]
    scalarG = add(inv(add(scalarL, scalarP)), scalarP, -1)
    rows = []
    for row in scalar:
        for a in range(h):
            rows.append([x if b == a else Q(0) for x in row for b in range(h)])
    L0 = form(rows, [Q(1)]*len(rows))
    P = [[Q(int(i % h == j % h), V) for j in range(N)] for i in range(N)]
    G = [[scalarG[i//h][j//h] if i % h == j % h else Q(0)
          for j in range(N)] for i in range(N)]
    IminusP = add(eye(N), P, -1)
    need(mul(L0, G) == IminusP and mul(G, L0) == IminusP, 'actual mean-zero Green inverse')
    v = rows[0]
    gv = apply(G, v)
    rho = dot(v, gv)
    expected = Q(V-1, D*V)
    need(rho == expected, 'actual torus leverage normalization')
    need(sum((dot(r, apply(G, r)) for r in rows), Q(0)) == h*(V-1), 'actual leverage trace')
    need(all(dot(r, apply(G, r)) == rho for r in rows), 'all actual row leverages')
    m = Q(n*n)
    critical = m*(1/rho-1)
    phases = []
    for label, B, expected_inertia in (
            ('below', critical-m/2, (N-h, 0, h)),
            ('equal', critical, (N-h-1, 0, h+1)),
            ('above', critical+m/2, (N-h-1, 1, h))):
        values = [m]*len(rows)
        values[0] = -B
        H = form(rows, values)
        actual = inertia(H)
        need(actual == expected_inertia, 'actual below/equal/above inertia')
        delta = m-(m+B)*rho
        need(apply(H, gv) == [delta*x for x in v], 'actual Green equality witness')
        relative = add(H, L0, -delta)
        need(psd(relative), 'actual sharp energy-relative comparison')
        need(low(H, Q(1)) <= h+1, 'one-row strict low count')
        phases.append({'phase': label, 'B': str(B), 'inertia_pos_neg_zero': actual,
                       'low_count_c1': low(H, Q(1))})
        if label == 'equal':
            equalityH = H
        if label == 'above':
            aboveH = H
    theta = Q(D-1, 2)
    B = theta*m
    values = [m]*len(rows)
    values[0] = -B
    stableH = form(rows, values)
    gap = Q(16)*(D-1-theta)/D
    need(psd(add(stableH, IminusP, -gap)), 'actual uniform mean-zero gap')
    need(psd(add(add(stableH, P, gap), eye(N), -gap)), 'actual mean observation coercivity')
    need(low(stableH, gap) == h, 'actual optimal constant observation rank')

    # Two selected rows sharing the same source and component.
    v2 = rows[h]
    offdiag = dot(v, apply(G, v2))
    need(offdiag != 0, 'interaction fixture genuinely coupled')
    t = 1/(rho+abs(offdiag)/2)
    need(t > 1 and t*rho < 1 and t*(rho+abs(offdiag)) > 1,
         'individually stable but jointly unstable parameter')
    bad = m*(t-1)
    each_inertias = []
    for changed in (0, h):
        values = [m]*len(rows)
        values[changed] = -bad
        actual = inertia(form(rows, values))
        need(actual == (N-h, 0, h), 'individual negative channel stable')
        each_inertias.append(actual)
    values = [m]*len(rows)
    values[0] = values[h] = -bad
    pairH = form(rows, values)
    pair_actual = inertia(pairH)
    gram = [[rho, offdiag], [offdiag, rho]]
    reduced = add([[1/t, Q(0)], [Q(0), 1/t]], gram, -1)
    reduced_inertia = inertia(reduced)
    need(pair_actual == (N-h-1, 1, h) and reduced_inertia == (1, 1, 0),
         'actual coupled pair and two-by-two reduced inertia')
    # Different field components have zero Green coupling.
    if h > 1:
        need(dot(v, apply(G, rows[1])) == 0, 'actual component decoupling')

    rejected = []
    def reject(name, validator):
        try:
            validator()
        except ValueError:
            rejected.append(name)
            return
        raise ValueError('Mutation incorrectly accepted: '+name)
    reject('altered_rho', lambda: need(rho == expected+1, 'rho'))
    reject('dropped_volume_factor', lambda: need(rho == Q(V-1, D), 'volume'))
    values = [m]*len(rows)
    values[0] = -(critical+m/2)
    reject('wrong_critical_weight', lambda: need(inertia(form(rows, values)) == (N-h-1, 0, h+1), 'threshold'))
    wrong = gv[:]
    wrong[0] += 1
    reject('altered_Green_witness', lambda: need(apply(equalityH, wrong) == [Q(0)]*N, 'Green witness'))
    reject('reversed_phase_sign', lambda: need(inertia(aboveH)[1] == 0, 'negative phase'))
    reject('gap_claim_above_threshold', lambda: need(psd(add(aboveH, IminusP, -gap)), 'false gap'))
    reject('ignore_offdiagonal_coupling', lambda: need(psd(pairH), 'joint stability from individual tests'))
    need(len(rejected) == 7, 'explicit mutation acceptance counter')
    return {'D': D, 'n': n, 'h': h, 'field_dimension': N, 'rho': str(rho),
            'critical_B': str(critical), 'm': str(m), 'phases': phases,
            'stable_theta': str(theta), 'proved_gap_bound': str(gap),
            'stable_low_count_at_gap': low(stableH, gap),
            'pair': {'offdiagonal_Green': str(offdiag), 'update_ratio_t': str(t),
                     'each_negative_B': str(bad), 'individual_inertias': each_inertias,
                     'joint_inertia': pair_actual, 'reduced_inertia': reduced_inertia},
            'rejected_mutations': rejected}


def main():
    need(sys.platform.startswith('linux'), 'Own Colab Linux only')
    fixtures = [fixture(*params) for params in ((3, 2, 1), (3, 3, 1), (3, 3, 2), (4, 2, 2))]
    need(len(fixtures) == 4 and sum(len(row['rejected_mutations']) for row in fixtures) == 28,
         'final explicit fixture/mutation count')
    print(json.dumps({'status': 'EXACT_RESISTANCE_DIAGNOSTICS_PASS', 'fixtures': fixtures,
                      'mutation_pairs': 28, 'distinct_mutation_types': 7,
                      'all_size_theorem_verified': False, 'independent_review': False,
                      'Lean_verified': False}, sort_keys=True, indent=2))


if __name__ == '__main__':
    main()
