"""PRE-REGISTERED decision gate for the finite Ising sector-vacuum ratio.

Committed and pushed before its first execution.

For beta > 0, put

    a = -log(tanh(beta)) / 2,
    epsilon(k) = acosh(cosh(2a) cosh(2gamma)
                       - sinh(2a) sinh(2gamma) cos(k)).

For a ring of length L, the periodic and antiperiodic momentum grids are

    P_L = {2 pi j / L},       A_L = {2 pi (j + 1/2) / L},  0 <= j < L.

The finite vacuum quotient to be measured is

    R_L = exp((sum_{P_L} epsilon - sum_{A_L} epsilon) / 2).

PRE-REGISTERED PREDICTION (the verdict): for every L = 2,...,16, both
parities, beta in {0.125, 0.25, 0.5, 1, 2}, and gamma/a in
{0.75, 0.90, 0.99}, hence q = tanh(beta) exp(2 gamma) < 1,

    R_L <= 1  and  1 - R_L >= 1e-8.

The positive margin, not merely R_L <= 1, is the decision threshold.  Cells
gamma/a in {1.01, 1.10, 1.25} are measured outside q < 1, and gamma = 0 is
checked as the exact-decoupled control R_L = 1, but neither group can rescue a
failed inside-window verdict.

Two mutations must be rejected in every verdict cell: reversing the quotient,
and replacing the antiperiodic grid by the periodic grid.  The computation uses
100 decimal digits and explicit conditionals, so python -O removes no check.

A PASS licenses only an attempt to formalize the scalar vacuum-product
comparison needed by the finite fermionic classification.  It proves no
classification, no Jordan--Wigner theorem, neither sector bound, and no part of
the uniform spatial-ring inequality.
"""

from __future__ import annotations

import json
import sys

import mpmath as mp


mp.mp.dps = 100

BETAS = tuple(mp.mpf(x) for x in ("0.125", "0.25", "0.5", "1", "2"))
INSIDE_FRACTIONS = tuple(mp.mpf(x) for x in ("0.75", "0.90", "0.99"))
OUTSIDE_FRACTIONS = tuple(mp.mpf(x) for x in ("1.01", "1.10", "1.25"))
LENGTHS = tuple(range(2, 17))
MARGIN_FLOOR = mp.mpf("1e-8")
ROUNDING_TOL = mp.mpf("1e-80")


def fail(message: str, payload: object | None = None) -> "NoReturn":
    print(f"RESULT: FAIL: {message}", file=sys.stderr)
    if payload is not None:
        print(json.dumps(payload, sort_keys=True), file=sys.stderr)
    raise SystemExit(1)


def decimal(x: mp.mpf, digits: int = 50) -> str:
    return mp.nstr(x, digits, strip_zeros=False)


def dual_coupling(beta: mp.mpf) -> mp.mpf:
    return -mp.log(mp.tanh(beta)) / 2


def one_particle_energy(a: mp.mpf, gamma: mp.mpf, momentum: mp.mpf) -> mp.mpf:
    argument = (
        mp.cosh(2 * a) * mp.cosh(2 * gamma)
        - mp.sinh(2 * a) * mp.sinh(2 * gamma) * mp.cos(momentum)
    )
    if argument < 1 and 1 - argument <= ROUNDING_TOL:
        argument = mp.mpf(1)
    if argument < 1:
        fail("acosh argument below one", {"argument": decimal(argument)})
    return mp.acosh(argument)


def momentum_sums(length: int, a: mp.mpf, gamma: mp.mpf) -> tuple[mp.mpf, mp.mpf]:
    periodic = mp.fsum(
        one_particle_energy(a, gamma, 2 * mp.pi * j / length)
        for j in range(length)
    )
    antiperiodic = mp.fsum(
        one_particle_energy(a, gamma, 2 * mp.pi * (mp.mpf(j) + mp.mpf("0.5")) / length)
        for j in range(length)
    )
    return periodic, antiperiodic


def vacuum_ratio(length: int, a: mp.mpf, gamma: mp.mpf) -> mp.mpf:
    periodic, antiperiodic = momentum_sums(length, a, gamma)
    return mp.exp((periodic - antiperiodic) / 2)


def main() -> None:
    verdict_cells = 0
    even_lengths = 0
    odd_lengths = 0
    reversed_mutations_rejected = 0
    grid_mutations_rejected = 0
    outside_cells = 0
    outside_crossings = 0
    endpoint_cells = 0
    min_margin = mp.inf
    min_margin_cell: dict[str, object] | None = None
    outside_min = mp.inf
    outside_max = mp.mpf(0)

    for beta in BETAS:
        a = dual_coupling(beta)
        dual_error = abs(mp.exp(-2 * a) - mp.tanh(beta))
        if dual_error > ROUNDING_TOL:
            fail("dual-coupling identity failed", {"beta": decimal(beta), "error": decimal(dual_error)})

        for length in LENGTHS:
            endpoint_ratio = vacuum_ratio(length, a, mp.mpf(0))
            if abs(endpoint_ratio - 1) > ROUNDING_TOL:
                fail(
                    "gamma=0 vacuum quotient was not one",
                    {"beta": decimal(beta), "length": length, "ratio": decimal(endpoint_ratio)},
                )
            endpoint_cells += 1

        for fraction in INSIDE_FRACTIONS:
            gamma = fraction * a
            q = mp.tanh(beta) * mp.exp(2 * gamma)
            if not q < 1:
                fail("inside cell did not satisfy q < 1", {"beta": decimal(beta), "fraction": decimal(fraction), "q": decimal(q)})

            for length in LENGTHS:
                ratio = vacuum_ratio(length, a, gamma)
                margin = 1 - ratio
                if ratio > 1 + ROUNDING_TOL:
                    fail(
                        "periodic/antiperiodic vacuum quotient exceeded one",
                        {"beta": decimal(beta), "fraction": decimal(fraction), "length": length, "ratio": decimal(ratio)},
                    )
                if margin < MARGIN_FLOOR:
                    fail(
                        "pre-registered vacuum margin floor failed",
                        {"beta": decimal(beta), "fraction": decimal(fraction), "length": length, "ratio": decimal(ratio), "margin": decimal(margin), "floor": decimal(MARGIN_FLOOR)},
                    )
                if margin < min_margin:
                    min_margin = margin
                    min_margin_cell = {
                        "beta": decimal(beta),
                        "gamma_over_a": decimal(fraction),
                        "length": length,
                        "parity": "even" if length % 2 == 0 else "odd",
                        "q": decimal(q),
                        "ratio": decimal(ratio),
                    }

                reversed_ratio = 1 / ratio
                if reversed_ratio <= 1 + ROUNDING_TOL:
                    fail("gate accepted reversed quotient mutation", {"length": length})
                reversed_mutations_rejected += 1

                periodic, _ = momentum_sums(length, a, gamma)
                same_grid_ratio = mp.exp((periodic - periodic) / 2)
                if 1 - same_grid_ratio >= MARGIN_FLOOR:
                    fail("gate accepted periodic-for-antiperiodic grid mutation", {"length": length})
                grid_mutations_rejected += 1

                verdict_cells += 1
                if length % 2 == 0:
                    even_lengths += 1
                else:
                    odd_lengths += 1

        for fraction in OUTSIDE_FRACTIONS:
            gamma = fraction * a
            q = mp.tanh(beta) * mp.exp(2 * gamma)
            if not q > 1:
                fail("outside control did not satisfy q > 1", {"beta": decimal(beta), "fraction": decimal(fraction), "q": decimal(q)})
            for length in LENGTHS:
                ratio = vacuum_ratio(length, a, gamma)
                outside_min = min(outside_min, ratio)
                outside_max = max(outside_max, ratio)
                if ratio > 1 + ROUNDING_TOL:
                    outside_crossings += 1
                outside_cells += 1

    expected_verdict = len(BETAS) * len(INSIDE_FRACTIONS) * len(LENGTHS)
    expected_outside = len(BETAS) * len(OUTSIDE_FRACTIONS) * len(LENGTHS)
    expected_endpoint = len(BETAS) * len(LENGTHS)
    if verdict_cells != expected_verdict:
        fail("wrong verdict-cell count", {"actual": verdict_cells, "expected": expected_verdict})
    if outside_cells != expected_outside:
        fail("wrong outside-cell count", {"actual": outside_cells, "expected": expected_outside})
    if endpoint_cells != expected_endpoint:
        fail("wrong endpoint-cell count", {"actual": endpoint_cells, "expected": expected_endpoint})
    if reversed_mutations_rejected != expected_verdict:
        fail("wrong reversed-mutation count")
    if grid_mutations_rejected != expected_verdict:
        fail("wrong grid-mutation count")
    if min_margin_cell is None:
        fail("no minimum-margin cell was recorded")

    print(json.dumps({
        "status": "PASS",
        "classification": "finite sector-vacuum decision gate only",
        "precision_decimal_digits": mp.mp.dps,
        "lengths": [LENGTHS[0], LENGTHS[-1]],
        "beta_values": [decimal(beta, 8) for beta in BETAS],
        "inside_gamma_over_a": [decimal(x, 8) for x in INSIDE_FRACTIONS],
        "outside_gamma_over_a": [decimal(x, 8) for x in OUTSIDE_FRACTIONS],
        "margin_floor": decimal(MARGIN_FLOOR, 8),
        "verdict_cells": verdict_cells,
        "even_length_verdict_cells": even_lengths,
        "odd_length_verdict_cells": odd_lengths,
        "minimum_margin": decimal(min_margin),
        "minimum_margin_cell": min_margin_cell,
        "reversed_quotient_mutations_rejected": reversed_mutations_rejected,
        "same_grid_mutations_rejected": grid_mutations_rejected,
        "endpoint_gamma_zero_cells": endpoint_cells,
        "outside_cells": outside_cells,
        "outside_ratio_min": decimal(outside_min),
        "outside_ratio_max": decimal(outside_max),
        "outside_crossings_above_one": outside_crossings,
    }, sort_keys=True))


if __name__ == "__main__":
    main()
