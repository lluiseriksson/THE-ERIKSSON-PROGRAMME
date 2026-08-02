"""Precommitted exact gate for the finite vacuum root-product endpoint.

This gate licenses exactly one prospective Lean result: the paired periodic
and antiperiodic product identities, together with their strict order under
the printed hypotheses L >= 1 and 0 < x < 1.  It does not license the
Stieltjes/log-mixture identity or either spatial spectral-sector estimate.

All arithmetic is exact over ``Fraction``.  Verdict checks are explicit and
remain active under ``python -O``; no ``assert`` is used.
"""

from __future__ import annotations

from fractions import Fraction
import hashlib
import json
import sys
from typing import NoReturn


LENGTHS = tuple(range(1, 65))
X_VALUES = (
    Fraction(1, 100),
    Fraction(1, 10),
    Fraction(1, 4),
    Fraction(1, 2),
    Fraction(3, 4),
    Fraction(9, 10),
    Fraction(99, 100),
)


def fail(message: str, payload: object | None = None) -> NoReturn:
    print(f"RESULT: FAIL: {message}", file=sys.stderr)
    if payload is not None:
        print(json.dumps(payload, sort_keys=True), file=sys.stderr)
    raise SystemExit(1)


def polynomial_reciprocal_evaluation(coefficients: tuple[int, ...], x: Fraction) -> Fraction:
    """Return x^degree P(1/x), without division or floating-point arithmetic."""

    degree = len(coefficients) - 1
    return sum(
        (Fraction(coefficient) * x ** (degree - exponent) for exponent, coefficient in enumerate(coefficients)),
        start=Fraction(0),
    )


def root_polynomial(length: int, constant: int) -> tuple[int, ...]:
    if length < 1:
        fail("root-polynomial length hypothesis violated", {"length": length})
    return (constant,) + (0,) * (length - 1) + (1,)


def fraction_text(value: Fraction) -> str:
    return f"{value.numerator}/{value.denominator}"


def main() -> None:
    identity_rows = 0
    order_rows = 0
    mutation_attempts = {
        "periodic_sign": 0,
        "antiperiodic_sign": 0,
        "periodic_exponent": 0,
        "reversed_order": 0,
    }
    mutation_rejections = {name: 0 for name in mutation_attempts}
    transcript = []

    for length in LENGTHS:
        periodic_polynomial = root_polynomial(length, -1)  # z^L - 1
        antiperiodic_polynomial = root_polynomial(length, 1)  # z^L + 1
        for x in X_VALUES:
            if not (length >= 1 and 0 < x < 1):
                fail("printed front-door hypotheses failed", {"length": length, "x": fraction_text(x)})

            periodic = polynomial_reciprocal_evaluation(periodic_polynomial, x)
            antiperiodic = polynomial_reciprocal_evaluation(antiperiodic_polynomial, x)
            expected_periodic = 1 - x ** length
            expected_antiperiodic = 1 + x ** length

            if periodic != expected_periodic:
                fail("periodic reciprocal/product identity failed", {
                    "length": length,
                    "x": fraction_text(x),
                    "observed": fraction_text(periodic),
                    "expected": fraction_text(expected_periodic),
                })
            if antiperiodic != expected_antiperiodic:
                fail("antiperiodic reciprocal/product identity failed", {
                    "length": length,
                    "x": fraction_text(x),
                    "observed": fraction_text(antiperiodic),
                    "expected": fraction_text(expected_antiperiodic),
                })
            identity_rows += 2

            if not (0 < periodic < antiperiodic):
                fail("strict finite-product order failed", {
                    "length": length,
                    "x": fraction_text(x),
                    "periodic": fraction_text(periodic),
                    "antiperiodic": fraction_text(antiperiodic),
                })
            order_rows += 1

            mutations = {
                "periodic_sign": 1 + x ** length,
                "antiperiodic_sign": 1 - x ** length,
                "periodic_exponent": 1 - x ** (length + 1),
                "reversed_order": antiperiodic < periodic,
            }
            accepted = {
                "periodic_sign": mutations["periodic_sign"] == periodic,
                "antiperiodic_sign": mutations["antiperiodic_sign"] == antiperiodic,
                "periodic_exponent": mutations["periodic_exponent"] == periodic,
                "reversed_order": bool(mutations["reversed_order"]),
            }
            for name in mutation_attempts:
                mutation_attempts[name] += 1
                if accepted[name]:
                    fail("known mutation was accepted", {
                        "family": name,
                        "length": length,
                        "x": fraction_text(x),
                    })
                mutation_rejections[name] += 1

            transcript.append(
                f"L={length};x={fraction_text(x)};P={fraction_text(periodic)};NS={fraction_text(antiperiodic)}"
            )

    if mutation_attempts != mutation_rejections:
        fail("mutation counters disagree", {
            "attempts": mutation_attempts,
            "rejections": mutation_rejections,
        })

    transcript_sha256 = hashlib.sha256(("\n".join(transcript) + "\n").encode("utf-8")).hexdigest()
    print(json.dumps({
        "status": "PASS",
        "classification": "exact rational finite-root-product gate only",
        "printed_hypotheses": ["1 <= L", "0 < x", "x < 1"],
        "length_min": min(LENGTHS),
        "length_max": max(LENGTHS),
        "x_values": [fraction_text(x) for x in X_VALUES],
        "identity_rows": identity_rows,
        "strict_order_rows": order_rows,
        "mutation_attempts": mutation_attempts,
        "mutation_rejections": mutation_rejections,
        "transcript_sha256": transcript_sha256,
    }, sort_keys=True))


if __name__ == "__main__":
    main()
