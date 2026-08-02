"""PRE-REGISTERED gate for the scalar Stieltjes/log-mixture identity.

Committed and pushed before its first execution.

For real parameters with the printed hypotheses

    1 < c,    0 < B,    0 <= s,

the prospective Lean theorem is the single identity

    acosh(c + B*s) - acosh(c)
      = (1/(2*pi)) * integral_0^(2*pi)
          log(1 + B*s/(c - cos(theta))) dtheta.

This is the arcsine Stieltjes/log mixture after pushing the arcsine measure
forward from uniform angular measure.  The physical application has

    a = -log(tanh(beta))/2,
    c = cosh(2*(a-gamma)),
    B = sinh(2*a)*sinh(2*gamma),

and its later front door must print the active assumptions

    0 < beta,    0 < gamma,    gamma < a.

The gate samples beta in {0.125, 0.5, 2}, gamma/a in {0.25, 0.75, 0.99},
and s in {0.125, 0.5, 1, 1.5, 2}.  At 120 decimal digits it predicts an
absolute residual at most 1e-70 in every one of the 45 cells.  The value s=0
is checked separately as an exact control.

Three mutations must be rejected in every positive-s cell: dividing the
angular average by two, omitting the base subtraction acosh(c), and omitting
the factor B inside the logarithm.  Verdicts use explicit branches rather
than assert, and normal/python -O outputs must be byte-identical.

A PASS licenses only an attempt to prove the displayed generic identity in
Lean.  It does not license the physical dispersion corollary, the finite
vacuum-product comparison, either spectral block, the beta=0 endpoint, or the
uniform spatial-ring bound.
"""

from __future__ import annotations

import json
import sys

import mpmath as mp


mp.mp.dps = 120

BETAS = tuple(mp.mpf(value) for value in ("0.125", "0.5", "2"))
FRACTIONS = tuple(mp.mpf(value) for value in ("0.25", "0.75", "0.99"))
S_VALUES = tuple(mp.mpf(value) for value in ("0.125", "0.5", "1", "1.5", "2"))
RESIDUAL_CEILING = mp.mpf("1e-70")
MUTATION_FLOOR = mp.mpf("1e-30")


def fail(message: str, payload: object | None = None) -> "NoReturn":
    print(f"RESULT: FAIL: {message}", file=sys.stderr)
    if payload is not None:
        print(json.dumps(payload, sort_keys=True), file=sys.stderr)
    raise SystemExit(1)


def decimal(value: mp.mpf, digits: int = 80) -> str:
    return mp.nstr(value, digits, strip_zeros=False)


def angular_average(c: mp.mpf, B: mp.mpf, s: mp.mpf, *, scale: mp.mpf | None = None) -> mp.mpf:
    active_scale = B if scale is None else scale

    def integrand(theta: mp.mpf) -> mp.mpf:
        denominator = c - mp.cos(theta)
        if not denominator > 0:
            fail("nonpositive angular denominator", {"denominator": decimal(denominator)})
        argument = 1 + active_scale * s / denominator
        if not argument > 0:
            fail("nonpositive logarithm argument", {"argument": decimal(argument)})
        return mp.log(argument)

    # The integrand is even and 2*pi-periodic.  Integrating over [0, pi]
    # avoids duplicating the endpoint peak near the disordered boundary.
    return mp.quad(integrand, [0, mp.pi]) / mp.pi


def parameters(beta: mp.mpf, fraction: mp.mpf) -> tuple[mp.mpf, mp.mpf, mp.mpf, mp.mpf]:
    a = -mp.log(mp.tanh(beta)) / 2
    gamma = fraction * a
    if not beta > 0:
        fail("beta hypothesis failed", {"beta": decimal(beta)})
    if not gamma > 0:
        fail("gamma hypothesis failed", {"gamma": decimal(gamma)})
    if not gamma < a:
        fail(
            "disordered-region hypothesis gamma < a failed",
            {"gamma": decimal(gamma), "a": decimal(a)},
        )
    c = mp.cosh(2 * (a - gamma))
    B = mp.sinh(2 * a) * mp.sinh(2 * gamma)
    if not c > 1:
        fail("generic hypothesis 1 < c failed", {"c": decimal(c)})
    if not B > 0:
        fail("generic hypothesis 0 < B failed", {"B": decimal(B)})
    return a, gamma, c, B


def main() -> None:
    cells = 0
    endpoint_controls = 0
    half_mutations_rejected = 0
    base_mutations_rejected = 0
    scale_mutations_rejected = 0
    max_residual = mp.mpf(0)
    min_mutation_gap = mp.inf
    worst_cell: dict[str, str] | None = None

    for beta in BETAS:
        for fraction in FRACTIONS:
            a, gamma, c, B = parameters(beta, fraction)

            endpoint_lhs = mp.acosh(c + B * 0) - mp.acosh(c)
            endpoint_rhs = angular_average(c, B, mp.mpf(0))
            if endpoint_lhs != 0 or endpoint_rhs != 0:
                fail(
                    "s=0 control was not exact",
                    {"lhs": decimal(endpoint_lhs), "rhs": decimal(endpoint_rhs)},
                )
            endpoint_controls += 1

            for s in S_VALUES:
                lhs = mp.acosh(c + B * s) - mp.acosh(c)
                rhs = angular_average(c, B, s)
                residual = abs(lhs - rhs)
                if residual > RESIDUAL_CEILING:
                    fail(
                        "Stieltjes/log-mixture residual exceeded ceiling",
                        {
                            "beta": decimal(beta),
                            "gamma_over_a": decimal(fraction),
                            "s": decimal(s),
                            "residual": decimal(residual),
                            "ceiling": decimal(RESIDUAL_CEILING),
                        },
                    )
                if residual > max_residual:
                    max_residual = residual
                    worst_cell = {
                        "beta": decimal(beta, 20),
                        "gamma_over_a": decimal(fraction, 20),
                        "s": decimal(s, 20),
                    }

                mutations = (
                    ("half_average", rhs / 2, "half"),
                    ("missing_base", mp.acosh(c + B * s), "base"),
                    ("missing_B", angular_average(c, B, s, scale=mp.mpf(1)), "scale"),
                )
                for name, mutated, family in mutations:
                    gap = abs(lhs - mutated)
                    if gap <= MUTATION_FLOOR:
                        fail(
                            f"{name} mutation survived",
                            {
                                "beta": decimal(beta),
                                "gamma_over_a": decimal(fraction),
                                "s": decimal(s),
                                "gap": decimal(gap),
                                "floor": decimal(MUTATION_FLOOR),
                            },
                        )
                    min_mutation_gap = min(min_mutation_gap, gap)
                    if family == "half":
                        half_mutations_rejected += 1
                    elif family == "base":
                        base_mutations_rejected += 1
                    else:
                        scale_mutations_rejected += 1
                cells += 1

    expected_cells = len(BETAS) * len(FRACTIONS) * len(S_VALUES)
    expected_controls = len(BETAS) * len(FRACTIONS)
    if cells != expected_cells:
        fail("cell counter mismatch", {"observed": cells, "expected": expected_cells})
    if endpoint_controls != expected_controls:
        fail(
            "endpoint-control counter mismatch",
            {"observed": endpoint_controls, "expected": expected_controls},
        )
    for name, count in (
        ("half", half_mutations_rejected),
        ("base", base_mutations_rejected),
        ("scale", scale_mutations_rejected),
    ):
        if count != expected_cells:
            fail(f"{name} mutation counter mismatch", {"observed": count, "expected": expected_cells})

    payload = {
        "claim": "arcosh(c+B*s)-arcosh(c)=average log(1+B*s/(c-cos(theta)))",
        "generic_hypotheses": ["1 < c", "0 < B", "0 <= s"],
        "physical_hypotheses": ["0 < beta", "0 < gamma", "gamma < a"],
        "precision_digits": mp.mp.dps,
        "residual_ceiling": decimal(RESIDUAL_CEILING, 20),
        "mutation_floor": decimal(MUTATION_FLOOR, 20),
        "cells": cells,
        "endpoint_controls": endpoint_controls,
        "half_mutations_rejected": half_mutations_rejected,
        "base_mutations_rejected": base_mutations_rejected,
        "scale_mutations_rejected": scale_mutations_rejected,
        "max_residual": decimal(max_residual),
        "min_mutation_gap": decimal(min_mutation_gap),
        "worst_cell": worst_cell,
        "status": "PASS",
    }
    print(json.dumps(payload, sort_keys=True, separators=(",", ":")))


if __name__ == "__main__":
    main()
