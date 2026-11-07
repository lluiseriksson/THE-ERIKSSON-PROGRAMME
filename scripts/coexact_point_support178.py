"""Exact integer-scaled finite checks for the analytical coexact pinning adapter.

Run on Linux/Colab, not on the owner's Windows desktop. No all-size theorem,
Lean verification or independent review follows from these finite fixtures.
"""
import argparse
from fractions import Fraction
import itertools
import json
from pathlib import Path


def require(condition, message):
    if not condition:
        raise ValueError(message)


def distance(x, y, n):
    return max(min((a-b) % n, (b-a) % n) for a, b in zip(x, y))


def clusters(points, n):
    remaining = set(points)
    out = []
    while remaining:
        part = {min(remaining)}
        remaining -= part
        frontier = list(part)
        while frontier:
            x = frontier.pop()
            near = {y for y in remaining if distance(x, y, n) <= 4}
            part |= near
            remaining -= near
            frontier.extend(sorted(near))
        out.append(sorted(part))
    return out


def primitive(n):
    f = [n - 4*min(t, n-t) for t in range(n)]
    F = [0]
    for t in range(1, n):
        F.append(F[-1]-f[t])
    require(sum(f) == 0, 'triangular mean')
    require(all(F[(t-1) % n]-F[t] == f[t] for t in range(n)), 'periodic primitive')
    require(all(abs(f[(t+1) % n]-f[t]) == 4 for t in range(n)), 'triangular slope')
    return f, F


def replay(n, points, mutation=None):
    D = 3
    c, mu = 384, n*n
    grid = list(itertools.product(range(n), repeat=D))
    index = {x: k for k, x in enumerate(grid)}
    N = len(grid)
    f, F = primitive(n)
    plus, minus = [], []
    for j in range(D):
        plus.append([index[tuple((a+1) % n if i == j else a for i, a in enumerate(x))] for x in grid])
        minus.append([index[tuple((a-1) % n if i == j else a for i, a in enumerate(x))] for x in grid])
    parts = clusters(points, n)
    if mutation == 'split_adjacent_cluster':
        parts = [[p] for p in sorted(points)]
    require(all(distance(x, y, n) > 4 for i, a in enumerate(parts)
                for b in parts[i+1:] for x in a for y in b), 'sample components not separated')
    U0 = [[0]*N, [f[x[0]] for x in grid], [0]*N]
    eta = [[0]*N for _ in range(D)]
    totalG = [0]*N
    occupied = set()
    cluster_mass = 0
    for part in parts:
        size = len(part)
        cluster_mass += size**3
        center = F[part[0][0]]
        radius = 0 if mutation == 'chi_only_on_S' else 1
        G = [F[x[0]]-center if min(distance(x, p, n) for p in part) <= radius else 0 for x in grid]
        require(max(map(abs, G), default=0) <= 4*size*n, 'primitive centre amplitude')
        support = {k for k, x in enumerate(grid) if min(distance(x, p, n) for p in part) <= 2}
        require(len(support) <= 5**D*size, 'support volume')
        require(not (occupied & support), 'expanded cluster supports overlap')
        occupied |= support
        neighbor = plus if mutation == 'forward_adjoint' else minus
        local = [[-(G[neighbor[1][k]]-G[k]) for k in range(N)],
                 [G[neighbor[0][k]]-G[k] for k in range(N)], [0]*N]
        if mutation == 'omit_eta_component1':
            local[0] = [0]*N
        for j in range(D):
            require(all(local[j][k] == 0 for k in range(N) if k not in support), 'adjoint support')
            eta[j] = [a+b for a, b in zip(eta[j], local[j])]
        totalG = [a+b for a, b in zip(totalG, G)]
    U = [[a-b for a, b in zip(U0[j], eta[j])] for j in range(D)]
    require(all(U[j][index[x]] == 0 for x in points for j in range(D)), 'pin values')
    div = [sum(U[j][k]-U[j][minus[j][k]] for j in range(D)) for k in range(N)]
    require(all(v == 0 for v in div), 'actual backward divergence')
    # Independent total-potential comparison: U=d_1*(B0-sum G).
    potential = [F[x[0]]-g for x, g in zip(grid, totalG)]
    expected = [[-(potential[minus[1][k]]-potential[k]) for k in range(N)],
                [potential[minus[0][k]]-potential[k] for k in range(N)], [0]*N]
    require(U == expected, 'actual coexact potential dictionary')
    require(all(U[j][k] == U0[j][k] for k in range(N) if k not in occupied for j in range(D)), 'off-support field')
    require(all(sum(v) == 0 for v in U), 'coexact mean zero')
    norm0 = sum(v*v for component in U0 for v in component)
    if mutation == 'average_norm':
        norm0 = Fraction(norm0, N)
    require(3*norm0 == N*(n*n+8), 'counting norm of triangular field')
    norm = sum(v*v for component in U for v in component)
    etanorm = sum(v*v for component in eta for v in component)
    require(etanorm <= 128*5**D*n*n*cluster_mass, 'correction norm bound')
    require(3*norm >= n*n*N-3*n*n*5**D*len(points), 'witness norm bound')
    pairs = [(i, j) for i in range(D) for j in range(i+1, D)]
    if mutation == 'drop_positive_pair':
        pairs.remove((0, 1))
    curl = sum((U[j][plus[i][k]]-U[j][k]-U[i][plus[j][k]]+U[i][k])**2
               for i, j in pairs for k in range(N))
    gradient = sum((U[j][plus[i][k]]-U[j][k])**2 for i in range(D) for j in range(D) for k in range(N))
    require(curl+sum(v*v for v in div) == gradient, 'Hodge forward-gradient identity')
    energy = mu*curl
    require(energy <= 32*mu*N+1024*D*5**D*mu*n*n*cluster_mass, 'energy bound')
    return {'n': n, 'samples': [list(x) for x in sorted(points)], 'cluster_sizes': [len(p) for p in parts],
            'norm_squared_integer_scaled': norm, 'energy_integer_scaled': energy,
            'target_defect_integer_scaled': energy-c*norm,
            'rayleigh': str(Fraction(energy, norm)) if norm else None,
            'nonzero': bool(norm), 'checked': True}


def no_center_fixture(omit):
    n = 64
    _, F = primitive(n)
    p = n//4
    values = [F[(p+d) % n]-(0 if omit else F[p]) for d in (-1, 0, 1)]
    require(max(map(abs, values)) <= 4*n, 'primitive centre subtraction missing')


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    cases = []
    for n in (4, 8, 16):
        sets = [[], [(0, 0, 0)], [(0, 0, 0), (n-1, 0, 0)],
                [(0, 0, 0), (1, 0, 0), (2, 0, 0)]]
        if n == 4:
            sets.append(list(itertools.product(range(n), repeat=3)))
        else:
            sets.append([(0, 0, 0), (n//2, n//2, n//2)])
        if n == 16:
            sets.extend([[(0, 0, 0), (4, 0, 0)], [(0, 0, 0), (5, 0, 0)]])
        for points in sets:
            cases.append(replay(n, points))
    require(len(cases) == 17, 'original case count')
    no_center_fixture(False)
    rejected = []
    mutations = ('forward_adjoint', 'omit_eta_component1', 'chi_only_on_S',
                 'split_adjacent_cluster', 'drop_positive_pair', 'average_norm', 'no_primitive_center')
    for mutation in mutations:
        try:
            if mutation == 'no_primitive_center':
                no_center_fixture(True)
            else:
                points = [(0, 0, 0), (1, 0, 0)] if mutation == 'split_adjacent_cluster' else [(0, 0, 0)]
                replay(8, points, mutation)
        except ValueError as exc:
            rejected.append({'mutation': mutation, 'rejection': str(exc)})
        else:
            raise ValueError('Mutation was accepted: '+mutation)
    require(len(rejected) == len(mutations), 'mutation count')
    result = {'unit': 178, 'cases': cases, 'case_count': len(cases), 'mutations': rejected,
              'mutation_count': len(rejected), 'arithmetic': 'exact integers, fields scaled by n',
              'all_size_theorem_computationally_certified': False, 'Lean_verified': False,
              'independent_review': False}
    raw = (json.dumps(result, sort_keys=True, indent=2)+'\n').encode()
    args.output.write_bytes(raw)
    print('FINITE_ADAPTER_CHECKS_COMPLETE cases=17 rejected_mutations=7')


if __name__ == '__main__':
    main()
