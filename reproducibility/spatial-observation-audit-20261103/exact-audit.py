"""Finite diagnostics only. Execute in this chat's own Colab Linux runtime.

No Python assert controls acceptance. These checks do not prove the general
rectangular theorem, certify Lean, or constitute an independent review.
"""
import copy
import itertools
import json
import pathlib
import sys
from fractions import Fraction as F


def need(ok, message):
    if not ok:
        raise ValueError(message)


def energy(u, edges, weights):
    need(len(edges) == len(weights), "edge/weight length")
    return sum((w * (u[b] - u[a]) ** 2
                for (a, b), w in zip(edges, weights)), F(0))


def base_cycle():
    return dict(edges=[(0, 1), (1, 2), (2, 3), (3, 0)],
                weights=list(map(F, [1, 6, 4, 1])),
                blocks=[[0, 1], [2, 3]],
                u=[F(x, 14) for x in [19, -9, -5, -5]], c=F(19, 5),
                expected_energy=F(52, 7), expected_norm=F(123, 49),
                expected_observed=F(25, 49), expected_defect=F(-6, 35))


def cycle(case):
    u, edges, w, blocks, c = (case[k] for k in
                              ["u", "edges", "weights", "blocks", "c"])
    need(edges == [(0, 1), (1, 2), (2, 3), (3, 0)], "actual cycle edges")
    need(sorted(x for block in blocks for x in block) == list(range(4)),
         "disjoint exhaustive blocks")
    need(blocks == [[0, 1], [2, 3]], "prescribed partition")
    need(len(w) == 4 and min(w) >= 1, "positive actual coefficients")
    m = sum(w) / 4
    need(m == 3 and max(w) <= 2 * m, "exact mean and scalar cap")
    e = energy(u, edges, w)
    norm = sum(x*x for x in u)
    observed = sum(sum(u[x] for x in block)**2 / len(block)
                   for block in blocks)
    defect = e + c * observed - c * norm
    for name, actual in [("energy", e), ("norm", norm),
                         ("observed", observed), ("defect", defect)]:
        need(actual == case["expected_" + name], "actual " + name)
    need(c == F(19, 5) and defect < 0, "fixed-penalty failure")
    b1, b2 = [F(x) for x in [1, -1, 0, 0]], [F(x) for x in [0, 0, 1, -1]]
    q11 = energy(b1, edges, w) - c * sum(x*x for x in b1)
    q22 = energy(b2, edges, w) - c * sum(x*x for x in b2)
    q12 = (energy([x+y for x, y in zip(b1, b2)], edges, w)
           - energy(b1, edges, w) - energy(b2, edges, w)) / 2
    need((q11, q12, q22) == (F(17, 5), F(7), F(77, 5)), "kernel Gram")
    det = q11*q22-q12*q12
    need(q11 > 0 and det == F(84, 25) and det > 0, "kernel positive")
    return dict(energy=str(e), norm=str(norm), observed=str(observed),
                defect=str(defect), kernel_determinant=str(det))


class Q85:
    """Exact a+b sqrt(85), with sign decided by rational comparisons."""
    def __init__(self, a=0, b=0):
        self.a, self.b = F(a), F(b)

    @staticmethod
    def of(x):
        return x if isinstance(x, Q85) else Q85(x)

    def __add__(self, other):
        t = self.of(other)
        return Q85(self.a+t.a, self.b+t.b)

    __radd__ = __add__

    def __neg__(self):
        return Q85(-self.a, -self.b)

    def __sub__(self, other):
        return self + (-self.of(other))

    def __rsub__(self, other):
        return self.of(other) + (-self)

    def __mul__(self, other):
        t = self.of(other)
        return Q85(self.a*t.a+85*self.b*t.b, self.a*t.b+self.b*t.a)

    __rmul__ = __mul__

    def __pow__(self, k):
        need(k == 2, "only exact square is used")
        return self*self

    def __eq__(self, other):
        t = self.of(other)
        return self.a == t.a and self.b == t.b

    def sign(self):
        a, b = self.a, self.b
        if b == 0:
            return (a > 0)-(a < 0)
        if a == 0:
            return (b > 0)-(b < 0)
        if a > 0 and b > 0:
            return 1
        if a < 0 and b < 0:
            return -1
        cmp = (a*a > 85*b*b)-(a*a < 85*b*b)
        return cmp if a > 0 else -cmp

    def pair(self):
        return [str(self.a), str(self.b)]


def algebraic_cycle():
    edges, weights = base_cycle()["edges"], base_cycle()["weights"]
    s = Q85(0, 1)
    need(s*s == 85 and (s-6).sign() > 0, "quadratic field relation")
    c = Q85(F(17, 2), F(-1, 2))
    x, y = Q85(7), 6-s
    v = [x, -x, y, -y]
    e = energy(v, edges, weights)
    norm = sum((z*z for z in v), Q85())
    need(e-c*norm == 0, "actual kernel equality")
    h = list(map(F, [F(1, 2), F(1, 2), F(-1, 2), F(-1, 2)]))
    # Actual edge polarization supplies the delta-linear coefficient.
    mixed = sum((2*w*(v[b]-v[a])*(h[b]-h[a])
                 for (a, b), w in zip(edges, weights)), Q85())
    r = x+y
    need(r.sign() > 0 and mixed == -10*r, "nonzero equality coupling")
    need(energy(h, edges, weights) == 7 and sum(z*z for z in h) == 1,
         "actual mean perturbation")
    need((7-c).sign() > 0 and mixed.sign() < 0, "every finite K obstruction")
    # For K>=0 the exact defect polynomial is (7+K-c)delta²+mixed*delta.
    return dict(c=c.pair(), r=r.pair(), linear=mixed.pair(),
                constant_quadratic=(7-c).pair(), every_finite_K=True)


def grid(n, d, sampled):
    vertices = list(itertools.product(range(n), repeat=d))
    need(n >= 2 and d >= 3 and sampled <= set(vertices), "fixture domain")
    m, vol, size = n*n, n**d, len(sampled)

    def shift(x, i, step=1):
        y = list(x)
        y[i] = (y[i]+step) % n
        return tuple(y)

    f = {x: int(x not in sampled) for x in vertices}
    norm = sum(v*v for v in f.values())
    e = m*sum((f[shift(x, i)]-f[x])**2 for x in vertices for i in range(d))
    need(norm == vol-size and e <= 2*d*m*size, "scalar edge-boundary bound")
    transverse = {x[1:] for x in sampled}
    field = {x: int(x[1:] not in transverse) for x in vertices}
    need(all(field[x] == 0 for x in sampled), "physical sample annihilation")
    need(all(field[x]-field[shift(x, 0, -1)] == 0 for x in vertices),
         "actual backward divergence of occupied component")
    physical_norm = sum(v*v for v in field.values())
    physical_e = m*sum((field[shift(x, i)]-field[x])**2
                       for x in vertices for i in range(d))
    t = len(transverse)
    need(physical_norm == n*(n**(d-1)-t), "line-field norm")
    need(physical_e <= 2*(d-1)*m*n*t, "line-field energy bound")
    return dict(n=n, d=d, samples=size, transverse=t, scalar_norm=norm,
                scalar_energy=e, physical_norm=physical_norm,
                physical_energy=physical_e, critical_moment=1)


def main():
    need(sys.platform.startswith("linux"), "Colab Linux only; do not run on Windows")
    # Authenticate the exact source-note context before accepting fixtures.
    import hashlib
    folder = pathlib.Path(__file__).resolve().parents[1] / "mean-budget-order-20261101"
    hashes = {
        "interblock-shorted-energy.md": "820383dc270cd9b71807af29ed278de3248c14fc976a2a7992e336d8121320bd",
        "mean-penalty-slack-criterion.md": "92f4ad3e8616a80c4e937f3aff6c9fa451290aa78cfa7d4ab1327083e9974486",
        "sparse-point-observation-obstruction.md": "24332d43d615f966972923641d020e55ce055b5e592d175175acc0124bb42065",
    }
    for name, expected in hashes.items():
        need(hashlib.sha256((folder/name).read_bytes()).hexdigest() == expected,
             "frozen note hash " + name)
    rows = [cycle(base_cycle()), algebraic_cycle()]
    for n, d in [(2, 3), (4, 3), (4, 4), (8, 4)]:
        all_vertices = set(itertools.product(range(n), repeat=d))
        for sampled in [set(), {(0,)*d}, {(i,)*d for i in range(n)}, all_vertices]:
            rows.append(grid(n, d, sampled))
    mutations = []
    for label, change in [
        ("wrong_weight", lambda q: q["weights"].__setitem__(1, F(5))),
        ("lost_edge", lambda q: q["edges"].pop()),
        ("duplicate_edge", lambda q: q["edges"].__setitem__(3, (1, 2))),
        ("overlap_partition", lambda q: q["blocks"].__setitem__(1, [1, 3])),
        ("wrong_witness", lambda q: q["u"].__setitem__(0, q["u"][0]+1)),
        ("wrong_norm", lambda q: q.__setitem__("expected_norm", F(3))),
        ("wrong_observation", lambda q: q.__setitem__("expected_observed", F(0))),
        ("wrong_defect_sign", lambda q: q.__setitem__("expected_defect", F(6, 35))),
    ]:
        q = copy.deepcopy(base_cycle())
        change(q)
        try:
            cycle(q)
        except ValueError:
            mutations.append(label)
        else:
            raise RuntimeError("Real mutation accepted: " + label)
    need(len(rows) == 18 and len(mutations) == 8, "explicit acceptance counters")
    print(json.dumps(dict(status="FINITE_DIAGNOSTICS_ACCEPTED", accepted=18,
                          real_mutations_rejected=8, mutation_names=mutations,
                          optimized=not __debug__, fixtures=rows, note_hashes=hashes,
                          general_theorem_verified=False, new_lean_run=False,
                          independent_review=False), sort_keys=True, indent=2))


if __name__ == "__main__":
    main()
