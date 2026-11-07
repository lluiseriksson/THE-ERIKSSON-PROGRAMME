"""Full rational optimum replay; execute in this chat's own Colab Linux only."""
from fractions import Fraction as F
import itertools
import json


def require(ok, label):
    if not ok:
        raise ValueError(label)


points = list(itertools.product(range(2), repeat=3))


def dot(v, w):
    return sum((a*b for a, b in zip(v, w)), F(0))


def mv(a, v):
    return [dot(row, v) for row in a]


def actual(coupling=1, collapse=False):
    a = [[F(0) for _ in points] for _ in points]
    for ix, x in enumerate(points):
        weight = 6+coupling*(-1)**x[0]+4*(-1)**x[1]
        for direction in range(3):
            y = list(x)
            y[direction] ^= 1
            iy = points.index(tuple(y))
            if collapse and ix > iy:
                continue
            a[ix][ix] += weight
            a[iy][iy] += weight
            a[ix][iy] -= weight
            a[iy][ix] -= weight
    return a


columns = [[F((-1)**sum(x[i] for i in range(3) if s & (1 << i)))
            for x in points] for s in range(8)]


def walsh(a):
    return [[dot(columns[i], mv(a, columns[j]))/8 for j in range(8)]
            for i in range(8)]


def psd(a):
    """Exact symmetric Schur elimination, including singular PSD blocks."""
    b = [list(row) for row in a]
    require(all(b[i][j] == b[j][i] for i in range(len(b))
                for j in range(len(b))), 'symmetry')
    while b:
        pivot = b[0][0]
        if pivot < 0:
            return False
        if pivot == 0:
            if any(b[0][j] != 0 for j in range(1, len(b))):
                return False
            b = [row[1:] for row in b[1:]]
        else:
            b = [[b[i][j]-b[i][0]*b[0][j]/pivot
                  for j in range(1, len(b))] for i in range(1, len(b))]
    return True


def kernel(a):
    """Rational RREF null basis; independent of proposed penalty formula."""
    b = [list(row) for row in a]
    n = len(b)
    pivot_columns = []
    row = 0
    for col in range(n):
        candidates = [i for i in range(row, n) if b[i][col]]
        if not candidates:
            continue
        other = candidates[0]
        b[row], b[other] = b[other], b[row]
        scale = b[row][col]
        b[row] = [x/scale for x in b[row]]
        for i in range(n):
            if i != row:
                scale = b[i][col]
                b[i] = [x-scale*y for x, y in zip(b[i], b[row])]
        pivot_columns.append(col)
        row += 1
    result = []
    for free in range(n):
        if free in pivot_columns:
            continue
        v = [F(0)]*n
        v[free] = F(1)
        for i, col in enumerate(pivot_columns):
            v[col] = -b[i][free]
        require(mv(a, v) == [0]*n, 'RREF kernel readback')
        result.append(v)
    return result


obs = [0, 2, 4, 6]
ker = [1, 3, 5, 7]
projection = [[F(x[1:] == y[1:], 2) for y in points] for x in points]
pw = walsh(projection)
require(pw == [[F(i == j and i in obs) for j in range(8)]
               for i in range(8)], 'actual normalized bar projection')


def formula(delta, variant='correct'):
    c = 16-delta
    second = 16*(8+delta)/(delta*(40+delta))-8-delta
    if variant == 'lower_bound_only':
        second = F(16, 5)/delta-8-delta
    if variant == 'double_residue':
        second += F(16, 5)/delta
    if variant == 'omit_constant_floor':
        return max(F(0), second)
    if variant == 'nonminimal_extra_one':
        return max(c, second)+1
    return max(c, second)


def validate_candidate(l, delta, penalty):
    c = 16-delta
    h = [[l[i][j]-(c if i == j else 0)+penalty*pw[i][j]
          for j in range(8)] for i in range(8)]
    require(psd(h), 'full actual8x8 penalty infeasible')
    witnesses = [v for v in kernel(h) if dot(v, mv(pw, v)) > 0]
    require(bool(witnesses), 'penalty not certified minimal: no observed null vector')
    v = witnesses[0]
    observed = dot(v, mv(pw, v))
    require(dot(v, mv(h, v)) == 0 and observed > 0, 'optimum witness')
    # This exact identity excludes every strictly smaller penalty, not just
    # the displayed test decreases. Full PSD separately supplies sufficiency.
    for epsilon in (F(1), F(1, 1000000)):
        smaller = [[h[i][j]-epsilon*pw[i][j] for j in range(8)]
                   for i in range(8)]
        require(dot(v, mv(smaller, v)) == -epsilon*observed < 0,
                'strictly smaller penalty witness')
    return {'delta': str(delta), 'c': str(c), 'penalty': str(penalty),
            'null_witness': list(map(str, v)), 'observed_norm2': str(observed)}


def check_dictionary(l):
    a = [[l[i][j]-(16 if i == j else 0) for j in ker] for i in ker]
    b = [[l[i][j]-(16 if i == j else 0) for j in obs] for i in obs]
    x = [[l[i][j] for j in obs] for i in ker]
    require(a == [[8,16,0,0],[16,32,0,0],[0,0,32,32],[0,0,32,56]],
            'full actual kernel block')
    require(b == [[-16,0,0,0],[0,8,0,0],[0,0,8,16],[0,0,16,32]],
            'full actual observed block')
    require(x == [[0,0,0,0],[0,4,0,0],[0,0,4,0],[0,0,0,8]],
            'full actual cross block')


l = walsh(actual())
check_dictionary(l)
deltas = [F(1,64), F(1,16), F(1,8), F(27,200), F(17,125),
          F(1,4), F(1), F(8), F(15)]
cases = [validate_candidate(l, d, formula(d)) for d in deltas]
# These rational deltas bracket the irrational transition without rounding.
require(3*F(27,200)**2+118*F(27,200)-16 < 0 and
        3*F(17,125)**2+118*F(17,125)-16 > 0, 'transition bracket')
require(psd([[F(28),F(32)],[F(32),F(52)]]), 'A2 minus4I domination')
require(psd([[F(8),F(16)],[F(16),F(32)]]), 'B2 PSD')
# Rational critical-kernel projection residue, avoiding irrational eigenvectors.
pcrit = [[F(4,5),F(-2,5)],[F(-2,5),F(1,5)]]
require(dot([F(0),F(4)], mv(pcrit,[F(0),F(4)])) == F(16,5),
        'exact critical residue16/5')
residual = []
for d in (F(1,64),F(1,128),F(1,1024)):
    corrected = formula(d)-F(16,5)/d
    require(corrected == F(64,5)/(40+d)-8-d, 'exact remainder identity')
    residual.append({'delta':str(d),'finite_remainder':str(corrected)})

mutations = []
for label, operation in (
    ('lower_bound_misreported_as_optimum',
     lambda: validate_candidate(l,F(1,16),formula(F(1,16),'lower_bound_only'))),
    ('constant_floor_deleted',
     lambda: validate_candidate(l,F(1),formula(F(1),'omit_constant_floor'))),
    ('critical_residue_doubled',
     lambda: validate_candidate(l,F(1,16),formula(F(1,16),'double_residue'))),
    ('feasible_but_nonminimal_extra_penalty',
     lambda: validate_candidate(l,F(1,16),formula(F(1,16),'nonminimal_extra_one'))),
    ('actual_x1_coupling_erased',lambda: check_dictionary(walsh(actual(coupling=0)))),
    ('actual_parallel_rows_collapsed',lambda: check_dictionary(walsh(actual(collapse=True))))):
    try:
        operation()
    except ValueError as error:
        mutations.append({'mutation':label,'rejection':str(error)})
    else:
        raise ValueError('Mutation accepted: '+label)
require(len(cases) == 9 and len(mutations) == 6, 'explicit acceptance counters')
print(json.dumps({'status':'EXACT_RECTANGULAR_OPTIMUM_PASS','case_count':len(cases),
                  'cases':cases,'mutation_count':len(mutations),'mutations':mutations,
                  'residue':'16/5','residual':residual,'physical_replay_this_unit':False,
                  'universal_analytic_theorem_computationally_certified':False,
                  'independent_review':False,'Lean_verified':False},sort_keys=True))
