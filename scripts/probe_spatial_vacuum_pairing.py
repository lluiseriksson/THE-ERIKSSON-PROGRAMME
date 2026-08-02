"""PRE-COMMITTED precision and termwise-pairing reconnaissance.

This is NOT a gate and licenses no theorem.  It answers two audit questions
raised after ``probe_spatial_vacuum_ratio_trend.py``:

1. Is the printed margin near 3e-51 a binary64 cancellation artefact?
2. Can the periodic/antiperiodic vacuum quotient be proved by pairing every
   individual periodic factor with an adjacent antiperiodic factor whose
   quotient is at most one?

The precision audit recomputes the extreme cell beta=2, gamma/a=0.10, L=48
at 100, 160, and 220 decimal digits, then evaluates it once with mpmath interval
arithmetic and requires the entire interval for 1-R_L to lie strictly above
zero.  The point computations remain numerical observations; the interval is
reported as an instrumental enclosure, not a Lean certificate.

The pairing audit uses 160 digits at beta=2, gamma/a=0.75 for every
L=2,...,16 and L in {20,24,32,48}.  It checks both the literal ordered adjacent
pairing P_j=2*pi*j/L with A_j=(2*j+1)*pi/L and the strongest possible
factorwise pairing test obtained by sorting both multisets of one-mode
energies.  A violation after sorting rules out every bijection whose individual
periodic/antiperiodic factor ratios are all at most one.  Product identities
are rechecked independently of the individual-factor verdicts.

Output status is OBSERVED, never PASS.  Explicit conditionals are used instead
of assertions so optimized Python cannot remove checks.
"""

from __future__ import annotations

import json
import sys

import mpmath as mp


PRECISIONS = (100, 160, 220)
PAIRING_DPS = 160
PAIRING_LENGTHS = tuple(range(2, 17)) + (20, 24, 32, 48)
EXTREME_BETA = "2"
EXTREME_FRACTION = "0.10"
EXTREME_LENGTH = 48
PAIRING_BETA = "2"
PAIRING_FRACTION = "0.75"


def fail(message: str, payload: object | None = None) -> "NoReturn":
    print(f"RESULT: FAIL: {message}", file=sys.stderr)
    if payload is not None:
        print(json.dumps(payload, sort_keys=True), file=sys.stderr)
    raise SystemExit(1)


def decimal(x: mp.mpf, digits: int = 80) -> str:
    return mp.nstr(x, digits, strip_zeros=False)


def dual_coupling(beta: mp.mpf) -> mp.mpf:
    return -mp.log(mp.tanh(beta)) / 2


def energy(a: mp.mpf, gamma: mp.mpf, momentum: mp.mpf) -> mp.mpf:
    argument = (
        mp.cosh(2 * a) * mp.cosh(2 * gamma)
        - mp.sinh(2 * a) * mp.sinh(2 * gamma) * mp.cos(momentum)
    )
    tolerance = mp.power(10, -(mp.mp.dps - 15))
    if argument < 1 and 1 - argument <= tolerance:
        argument = mp.mpf(1)
    if argument < 1:
        fail("point acosh argument below one", {"argument": decimal(argument)})
    return mp.acosh(argument)


def energy_lists(length: int, beta: mp.mpf, fraction: mp.mpf) -> tuple[list[mp.mpf], list[mp.mpf]]:
    a = dual_coupling(beta)
    gamma = fraction * a
    periodic = [
        energy(a, gamma, 2 * mp.pi * j / length)
        for j in range(length)
    ]
    antiperiodic = [
        energy(a, gamma, 2 * mp.pi * (mp.mpf(j) + mp.mpf("0.5")) / length)
        for j in range(length)
    ]
    return periodic, antiperiodic


def point_ratio(length: int, beta: mp.mpf, fraction: mp.mpf) -> tuple[mp.mpf, mp.mpf]:
    periodic, antiperiodic = energy_lists(length, beta, fraction)
    log_ratio = (mp.fsum(periodic) - mp.fsum(antiperiodic)) / 2
    value = mp.exp(log_ratio)
    return value, 1 - value


def interval_extreme() -> dict[str, str]:
    iv = mp.iv
    iv.dps = 100

    def iv_cosh(x):
        return (iv.exp(x) + iv.exp(-x)) / 2

    def iv_sinh(x):
        return (iv.exp(x) - iv.exp(-x)) / 2

    def iv_acosh(x):
        return iv.log(x + iv.sqrt(x * x - 1))

    beta = iv.mpf(EXTREME_BETA)
    fraction = iv.mpf(EXTREME_FRACTION)
    # mpmath 1.3.0's interval context exposes no hyperbolic methods.  Keep the
    # exact same formulas through interval-supported exp/log/sqrt primitives.
    tanh_beta = iv_sinh(beta) / iv_cosh(beta)
    a = -iv.log(tanh_beta) / 2
    gamma = fraction * a
    periodic = []
    antiperiodic = []
    for j in range(EXTREME_LENGTH):
        p = 2 * iv.pi * j / EXTREME_LENGTH
        ap = 2 * iv.pi * (iv.mpf(j) + iv.mpf("0.5")) / EXTREME_LENGTH
        common = iv_cosh(2 * a) * iv_cosh(2 * gamma)
        scale = iv_sinh(2 * a) * iv_sinh(2 * gamma)
        periodic.append(iv_acosh(common - scale * iv.cos(p)))
        antiperiodic.append(iv_acosh(common - scale * iv.cos(ap)))
    log_ratio = (sum(periodic, iv.mpf(0)) - sum(antiperiodic, iv.mpf(0))) / 2
    ratio = iv.exp(log_ratio)
    margin = 1 - ratio
    if not (margin > 0):
        fail("interval margin was not strictly positive", {"margin_interval": str(margin)})
    return {
        "ratio_interval": str(ratio),
        "margin_interval": str(margin),
        "strictly_positive_boolean": True,
    }


def pairing_record(length: int) -> dict[str, object]:
    beta = mp.mpf(PAIRING_BETA)
    fraction = mp.mpf(PAIRING_FRACTION)
    periodic, antiperiodic = energy_lists(length, beta, fraction)
    direct_log_ratio = (mp.fsum(periodic) - mp.fsum(antiperiodic)) / 2

    adjacent_logs = [(left - right) / 2 for left, right in zip(periodic, antiperiodic)]
    adjacent_violations = [index for index, value in enumerate(adjacent_logs) if value > 0]

    sorted_periodic = sorted(periodic)
    sorted_antiperiodic = sorted(antiperiodic)
    sorted_logs = [(left - right) / 2 for left, right in zip(sorted_periodic, sorted_antiperiodic)]
    sorted_violations = [index for index, value in enumerate(sorted_logs) if value > 0]

    adjacent_product_log = mp.fsum(adjacent_logs)
    sorted_product_log = mp.fsum(sorted_logs)
    tolerance = mp.power(10, -(PAIRING_DPS - 20))
    if abs(adjacent_product_log - direct_log_ratio) > tolerance:
        fail("adjacent factors did not reconstruct the quotient", {"length": length})
    if abs(sorted_product_log - direct_log_ratio) > tolerance:
        fail("sorted factors did not reconstruct the quotient", {"length": length})

    return {
        "length": length,
        "parity": "even" if length % 2 == 0 else "odd",
        "vacuum_ratio": decimal(mp.exp(direct_log_ratio), 60),
        "margin": decimal(1 - mp.exp(direct_log_ratio), 60),
        "adjacent_pair_violations": len(adjacent_violations),
        "first_adjacent_violation_index": adjacent_violations[0] if adjacent_violations else None,
        "max_adjacent_factor_ratio": decimal(mp.exp(max(adjacent_logs)), 60),
        "sorted_pair_violations": len(sorted_violations),
        "first_sorted_violation_index": sorted_violations[0] if sorted_violations else None,
        "max_sorted_factor_ratio": decimal(mp.exp(max(sorted_logs)), 60),
        "any_termwise_bijection_possible": not sorted_violations,
    }


def main() -> None:
    precision_records = []
    for digits in PRECISIONS:
        mp.mp.dps = digits
        value, margin = point_ratio(
            EXTREME_LENGTH,
            mp.mpf(EXTREME_BETA),
            mp.mpf(EXTREME_FRACTION),
        )
        if margin <= 0:
            fail("point margin was not positive", {"digits": digits, "margin": decimal(margin)})
        precision_records.append({
            "decimal_digits": digits,
            "ratio": decimal(value, min(digits - 10, 120)),
            "margin": decimal(margin, min(digits - 10, 120)),
        })

    interval_record = interval_extreme()

    mp.mp.dps = PAIRING_DPS
    pairing_records = [pairing_record(length) for length in PAIRING_LENGTHS]
    print(json.dumps({
        "status": "OBSERVED",
        "classification": "precision and termwise-pairing reconnaissance only; not a gate",
        "extreme_cell": {
            "beta": EXTREME_BETA,
            "gamma_over_a": EXTREME_FRACTION,
            "length": EXTREME_LENGTH,
        },
        "point_precision_records": precision_records,
        "interval_precision_decimal_digits": 100,
        "interval_record": interval_record,
        "pairing_cell": {"beta": PAIRING_BETA, "gamma_over_a": PAIRING_FRACTION},
        "pairing_precision_decimal_digits": PAIRING_DPS,
        "pairing_records": pairing_records,
        "lengths_with_adjacent_violations": sum(
            1 for record in pairing_records if int(record["adjacent_pair_violations"]) > 0
        ),
        "lengths_with_no_possible_termwise_bijection": sum(
            1 for record in pairing_records if not bool(record["any_termwise_bijection_possible"])
        ),
    }, sort_keys=True))


if __name__ == "__main__":
    main()
