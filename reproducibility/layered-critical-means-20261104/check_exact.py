"""Finite exact-arithmetic diagnostics. Run ONLY in this chat's Colab Linux.

Not a Lean proof, universal certificate, novelty test or independent review.
No assertions control acceptance. Deliberate false claims must be rejected.
"""
from fractions import Fraction as F
from itertools import product
from collections import Counter
from math import isqrt
import hashlib
import json
import platform
import resource
import time


def require(condition, message):
    if not condition:
        raise ValueError(message)


def half_power(value, dimension):
    value = F(value)
    result = value ** (dimension // 2)
    if dimension % 2:
        a, b = isqrt(value.numerator), isqrt(value.denominator)
        require(a * a == value.numerator and b * b == value.denominator,
                "fixture requires exact rational square root")
        result *= F(a, b)
    return result


def psd(matrix):
    """Exact symmetric Schur elimination, including zero-pivot rejection."""
    q = [[F(x) for x in row] for row in matrix]
    n = len(q)
    require(all(len(row) == n for row in q), "matrix not square")
    require(all(q[i][j] == q[j][i] for i in range(n) for j in range(n)),
            "matrix not symmetric")
    for k in range(n):
        pivot = q[k][k]
        if pivot < 0:
            return False
        if pivot == 0:
            if any(q[k][j] != 0 for j in range(k + 1, n)):
                return False
            continue
        for i in range(k + 1, n):
            for j in range(i, n):
                q[i][j] -= q[i][k] * q[k][j] / pivot
                q[j][i] = q[i][j]
    return True


def block_matrix(alpha, sides, rejected=False):
    points = list(product(*(range(side) for side in sides)))
    lookup = {x: i for i, x in enumerate(points)}
    size, length = len(points), len(alpha)
    require(sides[0] == length, "normal length mismatch")
    lap = [[F(0) for _ in points] for _ in points]
    for x in points:
        for k, side in enumerate(sides):
            if x[k] + 1 < side:
                y = list(x)
                y[k] += 1
                i, j = lookup[x], lookup[tuple(y)]
                weight = F(alpha[x[0]])
                lap[i][i] += weight
                lap[j][j] += weight
                lap[i][j] -= weight
                lap[j][i] -= weight
    harmonic = sum((1 / F(a) for a in alpha), F(0)) / length
    constant = F(length * (length - 1 if rejected else length), 4) * harmonic
    return [[constant * lap[i][j] - F(i == j) + F(1, size)
             for j in range(size)] for i in range(size)]


def partition(alpha, dimension, c):
    n, r = len(alpha), dimension - 1
    bad, leaves, terminal = [], [], []

    def visit(lo, hi):
        length = hi - lo
        harmonic = sum((1 / F(a) for a in alpha[lo:hi]), F(0)) / length
        if length == 1 or F(c, 4) * length * length * harmonic <= 1:
            leaves.append((lo, hi))
            return False
        node = (lo, hi)
        bad.append(node)
        mid = lo + length // 2
        left_bad, right_bad = visit(lo, mid), visit(mid, hi)
        if not left_bad and not right_bad:
            terminal.append(node)
        return True

    visit(0, n)
    require(sorted(x for lo, hi in leaves for x in range(lo, hi)) == list(range(n)),
            "normal leaves do not partition root")
    w = lambda nodes: sum((F(1, (hi - lo) ** r) for lo, hi in nodes), F(0))
    rho = F(2, 3) ** r
    require(w(bad) <= w(terminal) / (1 - rho), "bad/terminal tree bound")
    require(w(leaves) <= F(1, n ** r) + (2 * 3 ** r - 1) * w(bad),
            "leaf increment bound")
    inverse_mass = sum((1 / half_power(a, dimension) for a in alpha), F(0))
    kappa = half_power(F(c, 4), dimension)
    for lo, hi in bad:
        mass = sum((1 / half_power(a, dimension) for a in alpha[lo:hi]), F(0))
        require(kappa * mass > F(1, (hi - lo) ** r), "bad mass charge")
    require(w(terminal) <= kappa * inverse_mass, "terminal disjoint charge")
    count = sum(((n + hi - lo - 1) // (hi - lo)) ** r for lo, hi in leaves)
    factor = F(2 * 3 ** r - 1) / (1 - rho)
    bound = 2 ** r * (1 + factor * kappa * n ** r * inverse_mass)
    require(count <= bound, "critical rectangle count")
    # Construct actual boxes and verify discrete coverage, not only a count.
    boxes = []
    for lo, hi in leaves:
        length = hi - lo
        tiles = [(s, min(s + length, n)) for s in range(0, n, length)]
        for transverse in product(tiles, repeat=r):
            boxes.append(((lo, hi),) + transverse)
    require(len(boxes) == count, "actual box count")
    coverage = Counter()
    for box in boxes:
        for x in product(*(range(lo, hi) for lo, hi in box)):
            coverage[x] += 1
    require(len(coverage) == n ** dimension and all(v == 1 for v in coverage.values()),
            "actual boxes overlap or leave holes")
    return {"n": n, "D": dimension, "c": c, "normal_leaves": len(leaves),
            "rectangles": count, "bad_nodes": len(bad),
            "bound_exact": str(bound)}


def routing(n, dimension, weak):
    require(n >= 3 and dimension >= 3, "routing domain")
    occupancy = Counter()
    for x in sorted(weak):
        for i in range(dimension):
            j = (i + 1) % dimension
            tail = list(x)
            tail[j] = (tail[j] - 1) % n
            tail = tuple(tail)
            last = list(tail)
            last[i] = (last[i] + 1) % n
            last = tuple(last)
            require(tail not in weak and last not in weak, "detour weak tail")
            occupancy[(tail, j)] += 1
            occupancy[(tail, i)] += 1
            occupancy[(last, j)] += 1
    return max(occupancy.values(), default=0)


def main():
    require(platform.system() == "Linux", "Linux Colab only; no Windows execution")
    start = time.perf_counter()
    local = 0
    for dimension in (3, 4):
        for alpha in ([1, 100], [100, 1], [1, 4, 100], [100, 1, 9], [9, 4, 1]):
            sides = (len(alpha),) + (2,) * (dimension - 1)
            require(psd(block_matrix(alpha, sides)), "safe local block PSD failed")
            local += 1
    require(not psd(block_matrix([1, 100], (2, 1, 1), rejected=True)),
            "false L(L-1) coefficient was accepted")
    # Mutation that must never be accepted: a zero diagonal with nonzero row.
    require(not psd([[0, 1], [1, 0]]), "zero-pivot indefinite matrix accepted")
    partition_cases = []
    for dimension in (3, 4):
        for n in (1, 2, 3, 5, 6, 9):
            fixtures = [[1] * n, [n * n] * n,
                        [1 if s == n // 2 else n * n for s in range(n)],
                        [(1, 4, 100)[s % 3] for s in range(n)]]
            for alpha in fixtures:
                for c in (1, 4, 9):
                    partition_cases.append(partition(alpha, dimension, c))
    routes = []
    for dimension in (3, 4):
        for n in (3, 6):
            weak = set(product(range(0, n, 3), repeat=dimension))
            congestion = routing(n, dimension, weak)
            require(congestion <= 1, "separated congestion exceeds one")
            routes.append({"profile": "period3", "n": n, "D": dimension,
                           "congestion": congestion})
        for n in (3, 5, 7):
            weak = {(s,) * dimension for s in range(n)}
            congestion = routing(n, dimension, weak)
            require(congestion <= 3, "diagonal congestion exceeds three")
            routes.append({"profile": "diagonal", "n": n, "D": dimension,
                           "congestion": congestion})
    star = {(0, 0, 0), (5, 0, 0), (0, 5, 0), (0, 0, 5)}
    rejected = False
    try:
        routing(6, 3, star)
    except ValueError as error:
        rejected = str(error) == "detour weak tail"
    require(rejected, "invalid incoming-star routing accepted")
    report = {"status": "finite_exact_checks_passed", "local_PSD_cases": local,
              "partition_cases": len(partition_cases), "routing_cases": len(routes),
              "mutation_rejections": ["false local constant", "zero-pivot indefinite",
                                      "incoming-star weak detour"],
              "arithmetic": "fractions.Fraction; exact rational Schur complements",
              "routes": routes, "partitions": partition_cases,
              "source_scope": "unit124/125 restricted analytic claims only",
              "not_claimed": ["universal proof", "Lean verification", "novelty",
                              "independent review", "general rectangular solution"],
              "elapsed_seconds": time.perf_counter() - start,
              "peak_rss_KiB": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
              "platform": platform.platform()}
    payload = json.dumps(report, sort_keys=True, separators=(",", ":"))
    print("REPORT_JSON_BEGIN")
    print(payload)
    print("REPORT_JSON_END")
    print("REPORT_SHA256", hashlib.sha256(payload.encode()).hexdigest())


if __name__ == "__main__":
    main()
