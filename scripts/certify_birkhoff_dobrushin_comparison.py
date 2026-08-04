#!/usr/bin/env python3
"""Exact finite certificates for the Birkhoff--Dobrushin wall paper.

The script intentionally uses only the Python standard library and exact
fractions.  It is a regression certificate, not a replacement for the proofs.
"""

from __future__ import annotations

import itertools
import json
import time
from fractions import Fraction


Vector = tuple[Fraction, ...]
Matrix = tuple[Vector, ...]


def tv(p: Vector, q: Vector) -> Fraction:
    return sum((abs(a - b) for a, b in zip(p, q)), Fraction()) / 2


def ratio_extrema(p: Vector, q: Vector) -> tuple[Fraction, Fraction]:
    ratios = tuple(a / b for a, b in zip(p, q))
    return min(ratios), max(ratios)


def support(p: Vector) -> frozenset[int]:
    return frozenset(i for i, mass in enumerate(p) if mass > 0)


def restricted_ratio_extrema(p: Vector, q: Vector) -> tuple[Fraction, Fraction]:
    common_support = support(p)
    require(common_support == support(q), "restricted ratios require a common face")
    ratios = tuple(p[i] / q[i] for i in common_support)
    return min(ratios), max(ratios)


def rational_envelope(p: Vector, q: Vector) -> Fraction:
    m, big_m = ratio_extrema(p, q)
    if m == big_m:
        return Fraction()
    return (big_m - 1) * (1 - m) / (big_m - m)


def extended_hilbert_bound_holds(p: Vector, q: Vector) -> bool:
    """Check TV <= tanh(d_H/4) exactly, without approximating square roots."""
    if support(p) != support(q):
        return tv(p, q) <= 1
    m, big_m = restricted_ratio_extrema(p, q)
    distance = tv(p, q)
    # distance <= (sqrt(M)-sqrt(m))/(sqrt(M)+sqrt(m)) iff the
    # following inequality holds; both sides before squaring are nonnegative.
    return (1 - distance) ** 2 * big_m >= (1 + distance) ** 2 * m


def extended_hilbert_equality_holds(p: Vector, q: Vector) -> bool:
    """Check TV = tanh(d_H/4) using the same exact squared identity."""
    if support(p) != support(q):
        return tv(p, q) == 1
    m, big_m = restricted_ratio_extrema(p, q)
    distance = tv(p, q)
    return (1 - distance) ** 2 * big_m == (1 + distance) ** 2 * m


def closed_simplex_equality_classification(p: Vector, q: Vector) -> bool:
    """Claimed iff classification for equality in the extended bound."""
    support_p = support(p)
    support_q = support(q)
    if support_p != support_q:
        return support_p.isdisjoint(support_q)
    if p == q:
        return True
    m, big_m = restricted_ratio_extrema(p, q)
    ratios = {p[i] / q[i] for i in support_p}
    return m * big_m == 1 and ratios == {m, big_m}


def theta(matrix: Matrix) -> Fraction:
    rows = range(len(matrix))
    cols = range(len(matrix[0]))
    return max(
        matrix[x][y] * matrix[xp][yp]
        / (matrix[x][yp] * matrix[xp][y])
        for x, xp, y, yp in itertools.product(rows, rows, cols, cols)
    )


def tensor(a: Matrix, b: Matrix) -> Matrix:
    return tuple(
        tuple(a_row[i] * b_row[j] for i in range(len(a_row)) for j in range(len(b_row)))
        for a_row in a
        for b_row in b
    )


def dobrushin(matrix: Matrix) -> Fraction:
    return max(tv(p, q) for p in matrix for q in matrix)


def apply(matrix: Matrix, values: Vector) -> Vector:
    return tuple(sum((a * b for a, b in zip(row, values)), Fraction()) for row in matrix)


def osc(values: Vector) -> Fraction:
    return max(values) - min(values)


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def main() -> None:
    start = time.perf_counter()

    equality_pairs = (
        ((Fraction(3, 4), Fraction(1, 4)), (Fraction(1, 4), Fraction(3, 4))),
        (
            (Fraction(2, 5), Fraction(2, 5), Fraction(1, 10), Fraction(1, 10)),
            (Fraction(1, 10), Fraction(1, 10), Fraction(2, 5), Fraction(2, 5)),
        ),
    )
    equality_records = []
    for p, q in equality_pairs:
        bound = rational_envelope(p, q)
        require(tv(p, q) == bound, "reciprocal two-block equality failed")
        m, big_m = ratio_extrema(p, q)
        require(m * big_m == 1, "equality pair is not reciprocal")
        equality_records.append(
            {"tv": str(tv(p, q)), "m": str(m), "M": str(big_m), "F": str(bound)}
        )

    # Three atoms are needed to make the chord step itself strict: with two
    # atoms every likelihood ratio is automatically an endpoint.
    strict_p = (Fraction(1, 12), Fraction(1, 4), Fraction(2, 3))
    strict_q = (Fraction(1, 3), Fraction(1, 3), Fraction(1, 3))
    strict_tv = tv(strict_p, strict_q)
    strict_bound = rational_envelope(strict_p, strict_q)
    require(strict_tv < strict_bound, "strict chord example unexpectedly saturated")

    grid_pairs_checked = 0
    for denominator in range(3, 18):
        probabilities = tuple(
            (Fraction(k, denominator), Fraction(denominator - k, denominator))
            for k in range(1, denominator)
        )
        for p in probabilities:
            for q in probabilities:
                require(tv(p, q) <= rational_envelope(p, q), "pairwise envelope failed")
                grid_pairs_checked += 1

    closed_simplex_pairs_checked = 0
    closed_simplex_equality_pairs = 0
    for denominator in range(1, 13):
        probabilities_3 = tuple(
            (Fraction(i, denominator), Fraction(j, denominator),
             Fraction(denominator - i - j, denominator))
            for i in range(denominator + 1)
            for j in range(denominator - i + 1)
        )
        for p in probabilities_3:
            for q in probabilities_3:
                equality = extended_hilbert_equality_holds(p, q)
                predicted = closed_simplex_equality_classification(p, q)
                require(
                    extended_hilbert_bound_holds(p, q),
                    "closed-simplex Hilbert envelope failed",
                )
                require(
                    equality == predicted,
                    "closed-simplex equality classification failed",
                )
                closed_simplex_pairs_checked += 1
                closed_simplex_equality_pairs += int(equality)

    a: Matrix = (
        (Fraction(3, 4), Fraction(1, 4)),
        (Fraction(1, 4), Fraction(3, 4)),
    )
    b: Matrix = (
        (Fraction(2, 3), Fraction(1, 3)),
        (Fraction(1, 3), Fraction(2, 3)),
    )
    ab = tensor(a, b)
    require(theta(ab) == theta(a) * theta(b), "tensor cross-ratio law failed")

    tensor_records = []
    power = a
    for length in range(1, 5):
        expected = theta(a) ** length
        require(theta(power) == expected, f"theta tensor power failed at L={length}")
        tensor_records.append({"L": length, "theta": str(theta(power))})
        if length < 4:
            power = tensor(power, a)

    witness = (Fraction(1), Fraction(0))
    image = apply(a, witness)
    require(osc(image) == dobrushin(a) * osc(witness), "one-site oscillation did not saturate")

    # A function depending only on the first coordinate saturates the local
    # inequality for the two-site product.
    local_witness = (Fraction(1), Fraction(1), Fraction(0), Fraction(0))
    local_image = apply(tensor(a, a), local_witness)
    input_local_osc = max(
        abs(local_witness[2 * x + y] - local_witness[2 * xp + y])
        for x, xp, y in itertools.product(range(2), repeat=3)
    )
    output_local_osc = max(
        abs(local_image[2 * x + y] - local_image[2 * xp + y])
        for x, xp, y in itertools.product(range(2), repeat=3)
    )
    require(
        output_local_osc == dobrushin(a) * input_local_osc,
        "two-site coordinate oscillation did not saturate",
    )

    elapsed = time.perf_counter() - start
    report = {
        "status": "pass",
        "arithmetic": "fractions.Fraction",
        "grid_pairs_checked": grid_pairs_checked,
        "closed_simplex": {
            "pairs_checked": closed_simplex_pairs_checked,
            "equality_pairs": closed_simplex_equality_pairs,
            "classification": (
                "common face: identical or reciprocal two-block ratios; "
                "different faces: equality iff supports are disjoint"
            ),
        },
        "equality_examples": equality_records,
        "strict_example": {
            "tv": str(strict_tv),
            "rational_envelope": str(strict_bound),
        },
        "tensor_examples": {
            "theta_A": str(theta(a)),
            "theta_B": str(theta(b)),
            "theta_A_tensor_B": str(theta(ab)),
            "powers": tensor_records,
        },
        "local_saturation": {
            "delta": str(dobrushin(a)),
            "input_osc": str(input_local_osc),
            "output_osc": str(output_local_osc),
        },
        "elapsed_seconds": round(elapsed, 6),
    }
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
