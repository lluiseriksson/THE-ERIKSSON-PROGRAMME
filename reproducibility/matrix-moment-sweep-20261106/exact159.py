"""Own Colab Linux rational diagnostics only, never a universal theorem checker."""
from fractions import Fraction as Q
import copy
import hashlib
import itertools
import json
import math
import sys


def need(ok, why):
    if not ok:
        raise ValueError(why)


def zero(n, m=None):
    return [[Q(0) for _ in range(n if m is None else m)] for _ in range(n)]


def eye(n):
    a = zero(n)
    for i in range(n):
        a[i][i] = Q(1)
    return a


def tr(a):
    return list(map(list, zip(*a)))


def mul(a, b):
    need(len(a[0]) == len(b), 'matrix dimensions')
    bt = tr(b)
    return [[sum((x*y for x, y in zip(row, col)), Q(0)) for col in bt] for row in a]


def add(a, b, scale=1):
    return [[x+scale*y for x, y in zip(r, s)] for r, s in zip(a, b)]


def inv(a):
    n = len(a)
    w = [r[:] + s[:] for r, s in zip(a, eye(n))]
    for k in range(n):
        j = next((i for i in range(k, n) if w[i][k]), None)
        need(j is not None, 'singular inverse input')
        w[k], w[j] = w[j], w[k]
        v = w[k][k]
        w[k] = [x/v for x in w[k]]
        for i in range(n):
            if i != k and w[i][k]:
                v = w[i][k]
                w[i] = [x-v*y for x, y in zip(w[i], w[k])]
    return [r[n:] for r in w]


def rank(a):
    if not a:
        return 0
    w = copy.deepcopy(a)
    k = 0
    for j in range(len(w[0])):
        i = next((i for i in range(k, len(w)) if w[i][j]), None)
        if i is None:
            continue
        w[k], w[i] = w[i], w[k]
        v = w[k][j]
        w[k] = [x/v for x in w[k]]
        for i in range(k+1, len(w)):
            v = w[i][j]
            if v:
                w[i] = [x-v*y for x, y in zip(w[i], w[k])]
        k += 1
        if k == len(w):
            break
    return k


def inertia(a):
    need(a == tr(a), 'inertia input not symmetric')
    w = copy.deepcopy(a)
    pos = neg = null = 0
    while w:
        n = len(w)
        pivot = next((i for i in range(n) if w[i][i]), None)
        if pivot is not None:
            order = [pivot]+[i for i in range(n) if i != pivot]
            w = [[w[i][j] for j in order] for i in order]
            v = w[0][0]
            pos += int(v > 0)
            neg += int(v < 0)
            w = [[w[i][j]-w[i][0]*w[0][j]/v for j in range(1, n)] for i in range(1, n)]
            continue
        edge = next(((i, j) for i in range(n) for j in range(i+1, n) if w[i][j]), None)
        if edge is None:
            null += n
            break
        i, j = edge
        order = [i, j]+[k for k in range(n) if k not in (i, j)]
        w = [[w[i][j] for j in order] for i in order]
        v = w[0][1]
        pos += 1
        neg += 1
        w = [[w[i][j]-(w[i][0]*w[1][j]+w[i][1]*w[0][j])/v for j in range(2, n)] for i in range(2, n)]
    return pos, neg, null


def psd(a):
    return inertia(a)[1] == 0


def low(a, c):
    return inertia(add(a, eye(len(a)), -c))[1]


def fixture(h):
    D = 4
    points = list(itertools.product(range(2), repeat=D))
    V = len(points)
    where = {x: i for i, x in enumerate(points)}
    N, r = V*h, D*h
    d = zero(V*r, N)
    for a, x in enumerate(points):
        for i in range(D):
            y = list(x)
            y[i] ^= 1
            for t in range(h):
                row = a*r+i*h+t
                d[row][where[tuple(y)]*h+t] += 1
                d[row][a*h+t] -= 1
    P = [[Q(int(i % h == j % h), V) for j in range(N)] for i in range(N)]
    L0 = mul(tr(d), d)
    G0 = add(inv(add(L0, P)), P, -1)
    need(mul(L0, G0) == add(eye(N), P, -1), 'actual pseudoinverse')
    J = mul(d, G0)
    need(mul(tr(d), J) == add(eye(N), P, -1), 'feasible flow')
    need(rank(d) == h*(V-1), 'actual constant kernel rank')
    blocks = []
    b = h+min(1, h-1)
    for a in range(V):
        A = eye(r)
        if a % 2:
            A[0][0] = A[b][b] = Q(2)
            A[0][b] = A[b][0] = Q(-1)
        else:
            A[b][b] = Q(4)
        need(inertia(A) == (r, 0, 0), 'SPD coefficients')
        blocks.append(A)
    need(mul(blocks[0], blocks[1]) != mul(blocks[1], blocks[0]), 'noncommuting fixture')

    def assemble(coeff, rows=d):
        out = zero(N)
        for x, A in enumerate(coeff):
            dx = rows[x*r:(x+1)*r]
            out = add(out, mul(tr(dx), mul(A, dx)))
        return out

    LA = assemble(blocks)
    GA = add(inv(add(LA, P)), P, -1)
    inverses = [inv(A) for A in blocks]
    compare = add(assemble(inverses, J), GA, -1)
    need(psd(compare), 'noncommuting inverse comparison')
    need(inertia(LA)[2] == h, 'SPD constant modes')
    moment = sum((sum(mul(A, A)[i][i] for i in range(r)) for A in inverses), Q(0))
    alpha = Q(81, 16)
    counts = []
    for c in (Q(1, 8), Q(1, 2), Q(2)):
        k = low(LA, c)
        bound = h+alpha*c*c*moment
        need(k <= bound, 'SPD low count')
        counts.append({'c': str(c), 'low_count': k, 'bound': str(bound)})
    # Exact Walsh transform at n=2,D=4, with the same counting normalization.
    F = [[Q((-1)**sum(a*b for a, b in zip(x, k)), 4) for x in points] for k in points]
    need(mul(F, tr(F)) == eye(V), 'unitary counting Fourier')
    C2 = max(v*v for row in F for v in row)
    need(C2 == Q(1, V), 'Fourier L1-Linfinity square')
    weak = max(Q(sum(math.comb(D, j) for j in range(1, ell+1)), 16*ell*ell) for ell in range(1, D+1))
    need(weak/V <= Q(3, 4)**D, 'actual weak multiplier count')

    signed = []
    for mode in ('zero', 'negative', 'one_bad_channel'):
        badrows = []
        AA, AT = [], []
        S = Q(0)
        for x in range(V):
            diag = [Q(0 if mode == 'zero' else -1) for _ in range(r)] if mode != 'one_bad_channel' else [Q(-1 if x == 0 and j == 0 else 2) for j in range(r)]
            A, T = zero(r), zero(r)
            for j, v in enumerate(diag):
                A[j][j] = v
                T[j][j] = 16 if v <= 0 else v
                if v <= 0:
                    badrows.append(d[x*r+j][:])
                else:
                    S += 1/(v*v)
            AA.append(A)
            AT.append(T)
        H, HT = assemble(AA), assemble(AT)
        R = rank(badrows)
        update = add(HT, H, -1)
        need(psd(update) and rank(update) == R, 'exact defect update rank')
        rows = []
        for c in (Q(1, 8), Q(1, 2), Q(2)):
            k = low(H, c)
            need(k <= low(HT, c)+R, 'finite rank interlacing')
            need(k <= h+R+alpha*c*c*S, 'signed defect bound')
            if mode in ('zero', 'negative'):
                need(k == N == h+R and S == 0, 'sharp defect coefficient')
            rows.append({'c': str(c), 'low_count': k})
        signed.append({'mode': mode, 'defect_rank': R, 'positive_inverse_square_sum': str(S), 'counts': rows})

    rejected = []
    def reject(name, check):
        try:
            check()
        except ValueError:
            rejected.append(name)
            return
        raise ValueError('mutation incorrectly accepted: '+name)
    A_bad = copy.deepcopy(blocks[0])
    A_bad[0][0] = -1
    reject('indefinite_SPD_input', lambda: need(inertia(A_bad) == (r, 0, 0), 'SPD'))
    G_bad = copy.deepcopy(G0)
    G_bad[0][0] += 1
    reject('altered_pseudoinverse_entry', lambda: need(mul(L0, G_bad) == add(eye(N), P, -1), 'inverse'))
    B_bad = copy.deepcopy(compare)
    B_bad[0][0] -= 1
    reject('false_inverse_comparison', lambda: need(psd(B_bad), 'comparison'))
    reject('dropped_volume_normalization', lambda: need(C2 == 1, 'normalization'))
    reject('signed_defect_omitted', lambda: need(N <= h, 'negative/zero family'))
    need(len(rejected) == 5, 'exact mutation acceptance counter')
    return {'h': h, 'D': D, 'n': 2, 'field_dimension': N, 'SPD_counts': counts, 'trace_inverse_square': str(moment), 'Fourier_C_squared': str(C2), 'Fourier_weak': str(weak), 'signed': signed, 'mutations_rejected': rejected}


def main():
    need(sys.platform.startswith('linux'), 'Own Colab Linux execution only')
    need(inertia([[Q(0), Q(1)], [Q(1), Q(0)]]) == (1, 1, 0), 'two-pivot inertia control')
    need(inertia([[Q(0), Q(0)], [Q(0), Q(0)]]) == (0, 0, 2), 'zero inertia control')
    fixtures = [fixture(h) for h in (1, 2)]
    need(len(fixtures) == 2 and sum(len(x['mutations_rejected']) for x in fixtures) == 10, 'final explicit counter')
    result = {'status': 'EXACT_FINITE_DIAGNOSTICS_PASS', 'fixtures': fixtures, 'rejected_mutations': 10, 'universal_theorem_verified': False, 'new_Lean': False, 'independent_review': False}
    print(json.dumps(result, sort_keys=True, indent=2))


if __name__ == '__main__':
    main()
