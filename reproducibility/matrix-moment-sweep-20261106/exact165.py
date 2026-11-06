"""Actual finite positive scalar torus and rectangular threshold; own Colab only."""
from fractions import Fraction as F
import itertools
import json


def require(ok, label):
    if not ok:
        raise ValueError(label)


points = list(itertools.product(range(2), repeat=3))
masks = list(range(8))


def chi(mask, x):
    return F((-1) ** sum(x[i] for i in range(3) if mask & (1 << i)))


def actual(t=1, half=False):
    # Unnormalized Walsh columns have norm^2=8. Matrix below uses their
    # normalized version, cancelling the common sqrt8 without rounding.
    mat = [[F(0) for _ in points] for _ in points]
    for ix, x in enumerate(points):
        a = 6 + t * (-1)**x[0] + 4 * (-1)**x[1]
        for direction in range(3):
            y = list(x)
            y[direction] ^= 1
            iy = points.index(tuple(y))
            if half and ix > iy:
                continue
            mat[ix][ix] += a
            mat[iy][iy] += a
            mat[ix][iy] -= a
            mat[iy][ix] -= a
    return mat


def mv(a, v):
    return [sum((x*y for x, y in zip(row, v)), F(0)) for row in a]


def dot(v, w):
    return sum((x*y for x, y in zip(v, w)), F(0))


cols = [[chi(s, x) for x in points] for s in masks]


def walsh(mat):
    return [[dot(cols[i], mv(mat, cols[j]))/8 for j in masks] for i in masks]


def verify(mat, c=16):
    l = walsh(mat)
    for s in masks:
        expected = [F(0) for _ in masks]
        expected[s] = 24*s.bit_count()
        expected[s ^ 1] += 4*(s.bit_count()-bool(s & 1))
        expected[s ^ 2] += 16*(s.bit_count()-bool(s & 2))
        require([l[i][s] for i in masks] == expected, 'actual Walsh dictionary')
    ker, obs = [1, 3, 5, 7], [0, 2, 4, 6]
    compressed = [[l[i][j]-(c if i == j else 0) for j in ker] for i in ker]
    require(compressed == [[8,16,0,0],[16,32,0,0],
                           [0,0,32,32],[0,0,32,56]], 'kernel threshold blocks')
    require(compressed[0][0] > 0 and
            compressed[0][0]*compressed[1][1]-compressed[0][1]**2 == 0,
            'first block PSD rank1')
    require(compressed[2][2] > 0 and
            compressed[2][2]*compressed[3][3]-compressed[2][3]**2 == 768,
            'second block positive definite')
    v = [F(0)]*8
    v[1], v[3] = F(-2), F(1)
    h = [[l[i][j]-(c if i == j else 0) for j in masks] for i in masks]
    hv = mv(h, v)
    require(hv == [0,0,4,0,0,0,0,0], 'nonzero invisible critical coupling')
    require(dot(v,v) == 5 and dot(v,hv) == 0 and h[2][2] == 8,
            'critical vector and observed ray')
    # Actual four rectangles: projection is pairwise arithmetic average.
    p = [[F(0) for _ in points] for _ in points]
    for i,x in enumerate(points):
        for j,y in enumerate(points):
            if x[1:] == y[1:]:
                p[i][j] = F(1,2)
    pw = walsh(p)
    require(pw == [[F(i==j and i in obs) for j in masks] for i in masks],
            'actual normalized rectangular projection')
    for delta in (F(1), F(1,2), F(1,8)):
        lower = F(16,5)/delta-8-delta
        determinant = delta*(8+delta+lower)-F(16,5)
        require(determinant == 0, 'exact penalty lower-bound determinant')
    for penalty in (F(0),F(1),F(100),F(10**6)):
        tau = -(8+penalty)/8-1
        require(8+8*tau+penalty == -8, 'finite penalty witness')
    return {'kernel_blocks': compressed, 'critical_coupling': hv,
            'kernel_best_constant': c, 'mean': 6,
            'rectangles': 4, 'vertices': 8, 'oriented_rows': 24}


payload = verify(actual())
mutations = []
for label, mat, c in (('erase_x1_coupling', actual(t=0), 16),
                      ('collapse_parallel_rows', actual(half=True), 16),
                      ('wrong_threshold', actual(), 15)):
    try:
        verify(mat,c)
    except ValueError as error:
        mutations.append({'mutation':label,'rejection':str(error)})
    else:
        raise ValueError('Mutation accepted: '+label)
require(len(mutations) == 3, 'mutation counter')
print(json.dumps({'status':'EXACT_RECTANGULAR_THRESHOLD_PASS',
                  'payload':payload,'mutations':mutations,'mutation_count':3,
                  'independent_review':False,'Lean_verified':False,
                  'asymptotic_rank_conjecture_refuted':False},
                 default=str,sort_keys=True))
