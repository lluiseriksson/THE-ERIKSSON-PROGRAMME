"""Exact gate for one theorem: fold a flip-odd action over orbit representatives.

For a configuration ring of positive size, every global-flip orbit has one
representative whose first spin is zero.  If ``u`` is odd under the global
flip, then for every kernel ``K`` (no positivity or invariance required),

    sum_tau K(sigma,tau) u(tau)
      = sum_rho (K(sigma,rho) - K(sigma,flip(rho))) u(rho),

where ``rho`` ranges over the zero-headed representatives.  This gate checks
that purely combinatorial identity with exact rational arithmetic for sizes
1,...,7 and rejects three known orbit/sign mutations.

This licenses only the orbit-folding identity.  It is not a spectral
classification, an operator-norm estimate, a fermionic transform, either
sector bound, or progress on the uniform spatial-ring inequality.
"""

from __future__ import annotations

import itertools
import json
import sys
from fractions import Fraction


def fail(message: str, payload: object | None = None) -> "NoReturn":
    print(f"RESULT: FAIL: {message}", file=sys.stderr)
    if payload is not None:
        print(payload, file=sys.stderr)
    raise SystemExit(1)


def bit_code(bits: tuple[int, ...]) -> int:
    return sum(bit << index for index, bit in enumerate(bits))


def flip(bits: tuple[int, ...]) -> tuple[int, ...]:
    return tuple(1 - bit for bit in bits)


def kernel(
    length: int, sigma: tuple[int, ...], tau: tuple[int, ...]
) -> Fraction:
    """A positive exact test kernel, injective in ``tau`` for fixed ``sigma``."""

    numerator = (bit_code(sigma) + 1) * 10_000 + bit_code(tau) + length + 1
    return Fraction(numerator, 9_973)


def representative_value(tail: tuple[int, ...]) -> Fraction:
    return Fraction(2 * bit_code(tail) + 3, len(tail) + 2)


def odd_value(tau: tuple[int, ...]) -> Fraction:
    if tau[0] == 0:
        return representative_value(tau[1:])
    return -representative_value(flip(tau)[1:])


def main() -> None:
    action_rows = 0
    paired_summands = 0
    sign_mutations_rejected = 0
    omission_mutations_rejected = 0
    head_only_flip_mutations_rejected = 0

    for length in range(1, 8):
        configurations = list(itertools.product((0, 1), repeat=length))
        tails = list(itertools.product((0, 1), repeat=length - 1))

        for tau in configurations:
            if odd_value(flip(tau)) != -odd_value(tau):
                fail("constructed observable is not flip-odd", {"tau": tau})

        for sigma in configurations:
            full_action = sum(
                (kernel(length, sigma, tau) * odd_value(tau)
                 for tau in configurations),
                Fraction(0),
            )
            folded_action = Fraction(0)

            for tail in tails:
                representative = (0,) + tail
                flipped = flip(representative)
                value = representative_value(tail)
                positive_term = kernel(length, sigma, representative) * value
                negative_term = kernel(length, sigma, flipped) * (-value)
                folded_term = (
                    kernel(length, sigma, representative)
                    - kernel(length, sigma, flipped)
                ) * value

                if positive_term + negative_term != folded_term:
                    fail(
                        "paired orbit identity failed",
                        {"length": length, "sigma": sigma, "tail": tail},
                    )

                plus_sign_mutation = (
                    kernel(length, sigma, representative)
                    + kernel(length, sigma, flipped)
                ) * value
                if plus_sign_mutation == folded_term:
                    fail(
                        "gate accepted the odd-minus to plus mutation",
                        {"length": length, "sigma": sigma, "tail": tail},
                    )
                sign_mutations_rejected += 1

                omission_mutation = kernel(length, sigma, representative) * value
                if omission_mutation == folded_term:
                    fail(
                        "gate accepted omission of the flipped kernel entry",
                        {"length": length, "sigma": sigma, "tail": tail},
                    )
                omission_mutations_rejected += 1

                if length > 1:
                    head_only_flip = (1,) + tail
                    head_only_mutation = (
                        kernel(length, sigma, representative)
                        - kernel(length, sigma, head_only_flip)
                    ) * value
                    if head_only_mutation == folded_term:
                        fail(
                            "gate accepted flipping only the distinguished spin",
                            {"length": length, "sigma": sigma, "tail": tail},
                        )
                    head_only_flip_mutations_rejected += 1

                folded_action += folded_term
                paired_summands += 1

            if full_action != folded_action:
                fail(
                    "full action did not equal its odd orbit fold",
                    {
                        "length": length,
                        "sigma": sigma,
                        "full_action": str(full_action),
                        "folded_action": str(folded_action),
                    },
                )
            action_rows += 1

    expected_rows = sum(2**length for length in range(1, 8))
    expected_pairs = sum(2 ** (2 * length - 1) for length in range(1, 8))
    expected_head_only = expected_pairs - 2
    if action_rows != expected_rows:
        fail("wrong action-row count", {"actual": action_rows, "expected": expected_rows})
    if paired_summands != expected_pairs:
        fail(
            "wrong paired-summand count",
            {"actual": paired_summands, "expected": expected_pairs},
        )
    if sign_mutations_rejected != expected_pairs:
        fail("wrong sign-mutation count")
    if omission_mutations_rejected != expected_pairs:
        fail("wrong omission-mutation count")
    if head_only_flip_mutations_rejected != expected_head_only:
        fail("wrong head-only-flip mutation count")

    print(json.dumps({
        "status": "PASS",
        "classification": "exact flip-odd orbit-folding gate only",
        "ring_sizes": list(range(1, 8)),
        "action_rows_checked": action_rows,
        "paired_summands_checked": paired_summands,
        "sign_mutations_rejected": sign_mutations_rejected,
        "omission_mutations_rejected": omission_mutations_rejected,
        "head_only_flip_mutations_rejected": head_only_flip_mutations_rejected,
    }, sort_keys=True))


if __name__ == "__main__":
    main()
