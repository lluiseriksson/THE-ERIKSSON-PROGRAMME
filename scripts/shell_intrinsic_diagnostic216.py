"""Finite rational D=3 checks; not an all-field/all-D proof. Colab only."""
from fractions import Fraction as F
from itertools import product
import json
import hashlib

def require(ok, message):
    if not ok:
        raise ValueError(message)

def edges(points):
    s = set(points)
    out = []
    for x in sorted(s):
        for i in range(3):
            y = tuple(x[j] + (j == i) for j in range(3))
            if y in s:
                out.append((x, y, i))
    return out

def mean(values):
    require(bool(values), 'Empty mean')
    return sum(values, F(0)) / len(values)

def variance(points, field):
    m = mean([field[x] for x in points])
    return sum(((field[x] - m) ** 2 for x in points), F(0))

def run():
    records = []
    fields_checked = 0
    transport_checks = 0
    slab_checks = 0
    negative_controls = 0
    for R in range(1, 5):
        L = 2 * R + 1
        for r in range(R):
            t = R - r
            points = [x for x in product(range(-R, R + 1), repeat=3)
                      if max(map(abs, x)) > r]
            ee = edges(points)
            N = len(points)
            require(N == L ** 3 - (L - 2 * t) ** 3, 'Volume identity')
            require(2 * t * L ** 2 <= N <= 6 * t * L ** 2, 'Volume bracket')
            slabs = [[x for x in points if sign * x[i] > r]
                     for i in range(3) for sign in (1, -1)]
            require(set().union(*map(set, slabs)) == set(points), 'Cover')
            require(all(len(b) == t * L ** 2 for b in slabs), 'Slab volume')
            x0 = (R, R, 0)
            weak = {x0} | {tuple(x0[j] - (j == i) for j in range(3))
                           for i in range(3)}
            require(weak <= set(points) and len(weak) == 4, 'Actual weak star')
            eps = F(4, N)
            a = {x: eps if x in weak else F(1) for x in points}
            inv = sum((1 / a[x] for x in points), F(0))
            require(inv / N == 2 - F(4, N), 'Exact inverse moment')
            data = [
                {x: F(x == x0) for x in points},
                {x: F(x[0] + 2*x[1] - x[2]) for x in points},
                {x: F((-1) ** sum(x)) for x in points},
                {x: F((3*x[0]**2 + x[1]*x[2] + 5) % 11, 7)
                 for x in points},
            ]
            for fi, f in enumerate(data):
                grad = sum((abs(f[y]-f[x]) for x, y, i in ee), F(0))
                energy = sum((a[x]*(f[y]-f[x])**2 for x, y, i in ee), F(0))
                edge_inv = sum((1/a[x] for x, y, i in ee), F(0))
                var = variance(points, f)
                require(var <= 120 * grad**2, 'D3 shell Sobolev')
                require(grad**2 <= energy*edge_inv, 'Original-edge Holder')
                require(edge_inv <= 3*inv, 'Site-edge multiplicity')
                require(var <= 360*inv*energy, 'D3 weighted endpoint')
                for bi, b in enumerate(slabs):
                    eb = edges(b)
                    gb = sum((abs(f[y]-f[x]) for x, y, i in eb), F(0))
                    require(variance(b, f) <= 4*gb**2, 'Slab q1 estimate')
                    slab_checks += 1
                    for bj, other in enumerate(slabs):
                        if bi // 2 == bj // 2:
                            continue
                        overlap = set(b) & set(other)
                        m1 = mean([f[x] for x in b])
                        mi = mean([f[x] for x in overlap])
                        directional = sum((abs(f[y]-f[x]) for x, y, i in eb
                                           if i == bj // 2), F(0))
                        require(abs(m1-mi) <= directional/F(t*L),
                                'Actual intersection fiber transport')
                        transport_checks += 1
                if fi == 0:
                    require(var == F(N-1, N), 'Indicator variance')
                    require(energy == 4*eps, 'All incoming starts weakened')
                    naive = {x: eps if x == x0 else F(1) for x in points}
                    naive_energy = sum((naive[x]*(f[y]-f[x])**2
                                        for x, y, i in ee), F(0))
                    require(naive_energy == 3+eps and naive_energy > 4*eps,
                            'Missing-incoming-site negative control')
                    negative_controls += 1
                fields_checked += 1
            records.append({'R': R, 'r': r, 'vertices': N, 'edges': len(ee),
                            'epsilon': str(eps), 'moment': str(inv/N),
                            'indicator_energy': str(4*eps)})
    require(len(records) == 10 and fields_checked == 40, 'Acceptance counts')
    require(slab_checks == 240 and transport_checks == 960
            and negative_controls == 10, 'Mechanism counts')
    encoded = json.dumps(records, sort_keys=True, separators=(',', ':')).encode()
    return {'status': 'FINITE_RATIONAL_DIAGNOSTICS_CHECKED', 'geometries': 10,
            'fields': fields_checked, 'slab_checks': slab_checks,
            'transport_checks': transport_checks,
            'missing_incoming_negative_controls': negative_controls,
            'cases_sha256': hashlib.sha256(encoded).hexdigest(),
            'cases': records, 'all_D_or_all_field_proof': False,
            'formal_verification': False}

if __name__ == '__main__':
    print(json.dumps(run(), sort_keys=True))
