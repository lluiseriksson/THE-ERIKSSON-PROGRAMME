"""Actual finite trace-certificate dictionary; own Colab Linux execution only."""
from collections import Counter
from fractions import Fraction as F
import itertools
import json
import math


def require(ok, label):
    if not ok:
        raise ValueError(label)


def lap1(length, erase_wrap=False):
    a = [[F(0) for _ in range(length)] for _ in range(length)]
    edges = [(i, i+1) for i in range(length-1)]
    if length == 4 and not erase_wrap:
        edges.append((3, 0))
    for i, j in edges:
        a[i][i] += 1
        a[j][j] += 1
        a[i][j] -= 1
        a[j][i] -= 1
    return a


def rank(a):
    b = [list(row) for row in a]
    r = 0
    for col in range(len(b[0])):
        candidates = [i for i in range(r, len(b)) if b[i][col]]
        if not candidates:
            continue
        i = candidates[0]
        b[r], b[i] = b[i], b[r]
        scale = b[r][col]
        b[r] = [x/scale for x in b[r]]
        for i in range(len(b)):
            if i != r:
                scale = b[i][col]
                b[i] = [x-scale*y for x, y in zip(b[i], b[r])]
        r += 1
        if r == len(b):
            break
    return r


def inverse(a):
    n = len(a)
    b = [list(row)+[F(i == j) for j in range(n)] for i, row in enumerate(a)]
    for col in range(n):
        candidates = [i for i in range(col, n) if b[i][col]]
        require(bool(candidates), 'inverse pivot')
        i = candidates[0]
        b[col], b[i] = b[i], b[col]
        scale = b[col][col]
        b[col] = [x/scale for x in b[col]]
        for i in range(n):
            if i != col:
                scale = b[i][col]
                b[i] = [x-scale*y for x, y in zip(b[i], b[col])]
    require(all(b[i][j] == F(i == j) for i in range(n) for j in range(n)),
            'inverse left identity')
    inv = [row[n:] for row in b]
    require(all(sum((a[i][k]*inv[k][j] for k in range(n)), F(0)) == F(i == j)
                for i in range(n) for j in range(n)), 'inverse product readback')
    return inv


expected = {1:{0:1}, 2:{0:1,2:1}, 3:{0:1,1:1,3:1}, 4:{0:1,2:2,4:1}}


def actual_spectrum(length, erase_wrap=False):
    a = lap1(length, erase_wrap)
    spectrum = {}
    for value in range(5):
        shifted = [[a[i][j]-F(value if i == j else 0)
                    for j in range(length)] for i in range(length)]
        multiplicity = length-rank(shifted)
        if multiplicity:
            spectrum[value] = multiplicity
    require(spectrum == expected[length], 'actual1D spectral multiplicities')
    require(sum(spectrum.values()) == length, 'complete actual1D eigenspaces')
    return spectrum


spectra = {length:actual_spectrum(length) for length in range(1,5)}


def product_spectrum(shape, one_d=spectra):
    result = Counter({0:1})
    for length in shape:
        next_result = Counter()
        for a, ma in result.items():
            for b, mb in one_d[length].items():
                next_result[a+b] += ma*mb
        result = next_result
    require(sum(result.values()) == math.prod(shape), 'spectral dimension')
    require(result[0] == 1, 'exactly one constant zero mode')
    return result


def budget(spectrum, include_zero=False):
    total = F(0)
    for value, multiplicity in spectrum.items():
        if value == 0 and not include_zero:
            continue
        require(value > 0, 'inverse trace must exclude the constant mode')
        # c=mu=16, so the scale cancels exactly; eigenvalues are mu*value.
        total += F(multiplicity, value*value)
    return total


def actual_graph(shape):
    """Actual internal edges, including wrap only on full length4 axes."""
    vertices = list(itertools.product(*(range(n) for n in shape)))
    edges = []
    for x in vertices:
        for d, length in enumerate(shape):
            if x[d]+1 < length or length == 4:
                y = list(x)
                y[d] = (y[d]+1) % length
                edges.append((x,tuple(y)))
    index = {x:i for i,x in enumerate(vertices)}
    a = Counter()
    for x,y in edges:
        i,j = index[x],index[y]
        for key, value in (((i,i),16),((j,j),16),((i,j),-16),((j,i),-16)):
            a[key] += value
    return vertices, {key:value for key,value in a.items() if value}


def tensor_dictionary(shape):
    vertices = list(itertools.product(*(range(n) for n in shape)))
    index = {x:i for i,x in enumerate(vertices)}
    a = Counter()
    for i,x in enumerate(vertices):
        for d,length in enumerate(shape):
            local = lap1(length)
            for j in range(length):
                if local[x[d]][j]:
                    y = list(x)
                    y[d] = j
                    a[i,index[tuple(y)]] += 16*local[x[d]][j]
    return {key:value for key,value in a.items() if value}


shape_records = []
accepted = []
for shape in itertools.product(range(1,5), repeat=4):
    spec = product_spectrum(shape)
    b = budget(spec)
    _, actual = actual_graph(shape)
    require(actual == tensor_dictionary(shape), 'actual Cartesian stencil')
    row = {'shape':shape,'volume':math.prod(shape),'budget':str(b),'accepted':b<=1}
    shape_records.append(row)
    if b<=1:
        accepted.append(row)
require(len(shape_records) == 256 and len(accepted) == 31, 'shape counters')
max_volume = max(row['volume'] for row in accepted)
require(max_volume == 8, 'maximum certified volume')
require(budget(product_spectrum((4,2,1,1))) == F(139,144), 'K3 actual trace')
require(budget(product_spectrum((2,2,2,2))) == F(865,576), 'K4 actual trace')
require(budget(product_spectrum((3,1,1,1))) == F(10,9), 'length3 fails')

# A second route: true mean-zero pseudoinverse of selected full matrices,
# with exact inverse product checked, rather than the multiplicity formula.
direct_checks = []
for shape in ((1,1,1,1),(2,1,1,1),(3,1,1,1),(4,1,1,1),(4,2,1,1),(2,2,2,2)):
    vertices, entries = actual_graph(shape)
    m = len(vertices)
    a = [[F(entries.get((i,j),0)) for j in range(m)] for i in range(m)]
    inv = inverse([[a[i][j]+F(1,m) for j in range(m)] for i in range(m)])
    green = [[inv[i][j]-F(1,m) for j in range(m)] for i in range(m)]
    require(all(sum(row,F(0)) == 0 for row in green), 'Green annihilates constants')
    require(all(sum((a[i][k]*green[k][j] for k in range(m)),F(0))
                == F(i==j)-F(1,m) for i in range(m) for j in range(m)),
            'actual pseudoinverse projection')
    direct = 256*sum((green[i][j]*green[j][i]
                     for i in range(m) for j in range(m)),F(0))
    require(direct == budget(product_spectrum(shape)), 'direct full inverse-square trace')
    direct_checks.append({'shape':shape,'budget':str(direct)})

# Actual32-cell tiling and normalized-mean projection by exact1/volume entries.
cells = []
for pair in ((0,1),(2,3)):
    for z,w in itertools.product(range(4),repeat=2):
        cells.append(list(itertools.product(range(4),pair,(z,),(w,))))
cover = Counter(x for cell in cells for x in cell)
require(len(cells)==32 and len(cover)==256 and set(cover.values())=={1},
        'actual disjoint complete tiling')
require(all(len(cell)==8 for cell in cells), 'tiling cell volumes')
require(all(sum(F(1,len(cell))*F(1,len(cell)) for _ in cell)==F(1,len(cell))
            for cell in cells), 'actual block-average projection idempotence')
require(sum(F(len(cell),len(cell)) for cell in cells)==32, 'mean projection trace/rank')
require(256//max_volume==32, 'all-partition lower bound and attained count')
global_spec = product_spectrum((4,4,4,4))
require(min(16*value for value in global_spec if value>0)==32>=16,
        'actual global mean coercivity gap')
require(global_spec[0]==1 and sum(global_spec.values())==256, 'global scalar dimension')
require(budget(global_spec)>1, 'whole cell really fails strong-trace certificate')


def normalized_trace_shortcut():
    # Actual two-site interval with u=(1,-1), not the global torus.
    energy, variance, trace, volume = F(4*16), F(2), F(1,2*16), F(2)
    require(variance <= (trace/volume)*energy, 'normalized trace variance bound fails')


def insufficient_cells():
    require(31*max_volume>=256, '31 cells cannot cover with certified maximum volume')


def false_acceptance():
    require(budget(product_spectrum((2,2,2,2)))<=1, 'K4 certificate not acceptable')


def lost_multiplicity():
    bad = {length:dict(spec) for length,spec in spectra.items()}
    bad[4][2] = 1
    product_spectrum((4,4,4,4),bad)


mutations = []
for label, operation in (
    ('erase_actual_cycle_wrap',lambda:actual_spectrum(4,True)),
    ('collapse_cycle_eigenvalue_multiplicity',lost_multiplicity),
    ('invert_constant_zero_mode',lambda:budget(global_spec,True)),
    ('normalize_inverse_trace_by_volume',normalized_trace_shortcut),
    ('claim31_certificate_cells',insufficient_cells),
    ('accept_K4_trace_budget',false_acceptance)):
    try:
        operation()
    except ValueError as error:
        mutations.append({'mutation':label,'rejection':str(error)})
    else:
        raise ValueError('Mutation accepted: '+label)
require(len(mutations)==6 and len(direct_checks)==6, 'explicit final counters')
print(json.dumps({'status':'EXACT_TRACE_CERTIFICATE_PASS','shape_count':256,
                  'accepted_shape_count':len(accepted),'max_certified_volume':max_volume,
                  'minimum_certificate_cells':32,'actual_sufficient_cells':1,
                  'actual_global_gap':32,'direct_full_pseudoinverse_cases':direct_checks,
                  'shape_records':shape_records,'mutations':mutations,'mutation_count':6,
                  'asymptotic_theorem_computationally_certified':False,
                  'physical_replay_this_unit':False,'independent_review':False,
                  'Lean_verified':False},sort_keys=True))
