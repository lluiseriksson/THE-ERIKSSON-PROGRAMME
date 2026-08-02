"""PRE-COMMITTED reconnaissance of the finite sector-vacuum quotient trend.

This is deliberately NOT a gate: it has no predicted threshold and licenses
no theorem or implementation decision.  It measures the trend that must be
understood before a scalar vacuum-product inequality is preregistered.

The quotient and one-particle dispersion are exactly those used by
``judge_spatial_vacuum_ratio.py``.  The reconnaissance has three parts:

1. the previously worst cell beta=2, gamma/a=0.75 over every L=2,...,16 and
   L in {20,24,32,48};
2. the beta direction at gamma/a=0.75 and L in {16,32,48};
3. the gamma/a direction at beta=2 and L in {16,32,48}.

It reports margins, monotonicity (overall and separately by parity), and
finite-difference log slopes.  ``status = OBSERVED`` is not PASS.  The script
uses explicit integrity checks and no assertions, so optimized Python cannot
silently remove them.
"""

from __future__ import annotations

import json
import sys

import mpmath as mp


mp.mp.dps = 100
ROUNDING_TOL = mp.mpf("1e-80")
LENGTH_TREND = tuple(range(2, 17)) + (20, 24, 32, 48)
SLICE_LENGTHS = (16, 32, 48)
BETA_SCAN = tuple(mp.mpf(x) for x in ("0.125", "0.25", "0.5", "1", "2", "4", "8"))
FRACTION_SCAN = tuple(mp.mpf(x) for x in ("0.10", "0.25", "0.50", "0.75", "0.90", "0.99"))


def fail(message: str, payload: object | None = None) -> "NoReturn":
    print(f"RESULT: FAIL: {message}", file=sys.stderr)
    if payload is not None:
        print(json.dumps(payload, sort_keys=True), file=sys.stderr)
    raise SystemExit(1)


def decimal(x: mp.mpf, digits: int = 50) -> str:
    return mp.nstr(x, digits, strip_zeros=False)


def dual_coupling(beta: mp.mpf) -> mp.mpf:
    return -mp.log(mp.tanh(beta)) / 2


def energy(a: mp.mpf, gamma: mp.mpf, momentum: mp.mpf) -> mp.mpf:
    argument = (
        mp.cosh(2 * a) * mp.cosh(2 * gamma)
        - mp.sinh(2 * a) * mp.sinh(2 * gamma) * mp.cos(momentum)
    )
    if argument < 1 and 1 - argument <= ROUNDING_TOL:
        argument = mp.mpf(1)
    if argument < 1:
        fail("acosh argument below one", {"argument": decimal(argument)})
    return mp.acosh(argument)


def ratio(length: int, beta: mp.mpf, fraction: mp.mpf) -> tuple[mp.mpf, mp.mpf]:
    a = dual_coupling(beta)
    gamma = fraction * a
    periodic = mp.fsum(
        energy(a, gamma, 2 * mp.pi * j / length)
        for j in range(length)
    )
    antiperiodic = mp.fsum(
        energy(a, gamma, 2 * mp.pi * (mp.mpf(j) + mp.mpf("0.5")) / length)
        for j in range(length)
    )
    value = mp.exp((periodic - antiperiodic) / 2)
    q = mp.tanh(beta) * mp.exp(2 * gamma)
    if not 0 < value:
        fail("nonpositive vacuum quotient", {"length": length})
    if not q < 1:
        fail(
            "reconnaissance cell left q < 1",
            {"length": length, "beta": decimal(beta), "gamma_over_a": decimal(fraction), "q": decimal(q)},
        )
    return value, q


def decreasing(entries: list[dict[str, object]]) -> bool:
    margins = [mp.mpf(str(entry["margin_raw"])) for entry in entries]
    return all(right <= left for left, right in zip(margins, margins[1:]))


def log_slopes(entries: list[dict[str, object]]) -> list[dict[str, object]]:
    slopes: list[dict[str, object]] = []
    for left, right in zip(entries, entries[1:]):
        left_margin = mp.mpf(str(left["margin_raw"]))
        right_margin = mp.mpf(str(right["margin_raw"]))
        delta = int(right["length"]) - int(left["length"])
        if left_margin <= 0 or right_margin <= 0:
            fail("nonpositive margin in log slope", {"left": left, "right": right})
        slopes.append({
            "from_length": left["length"],
            "to_length": right["length"],
            "log_margin_slope_per_site": decimal((mp.log(right_margin) - mp.log(left_margin)) / delta, 30),
        })
    return slopes


def point(length: int, beta: mp.mpf, fraction: mp.mpf) -> dict[str, object]:
    value, q = ratio(length, beta, fraction)
    margin = 1 - value
    if margin <= 0:
        fail(
            "vacuum quotient was not below one",
            {"length": length, "beta": decimal(beta), "gamma_over_a": decimal(fraction), "ratio": decimal(value)},
        )
    return {
        "length": length,
        "parity": "even" if length % 2 == 0 else "odd",
        "beta": decimal(beta, 20),
        "gamma_over_a": decimal(fraction, 20),
        "q": decimal(q, 30),
        "ratio": decimal(value, 50),
        "margin": decimal(margin, 50),
        "margin_raw": decimal(margin, 100),
    }


def strip_raw(entries: list[dict[str, object]]) -> list[dict[str, object]]:
    return [{key: value for key, value in entry.items() if key != "margin_raw"} for entry in entries]


def main() -> None:
    worst_beta = mp.mpf("2")
    worst_fraction = mp.mpf("0.75")
    length_entries = [point(length, worst_beta, worst_fraction) for length in LENGTH_TREND]
    even_entries = [entry for entry in length_entries if entry["parity"] == "even"]
    odd_entries = [entry for entry in length_entries if entry["parity"] == "odd"]

    beta_entries = [
        point(length, beta, worst_fraction)
        for length in SLICE_LENGTHS
        for beta in BETA_SCAN
    ]
    fraction_entries = [
        point(length, worst_beta, fraction)
        for length in SLICE_LENGTHS
        for fraction in FRACTION_SCAN
    ]

    tail_entries = [entry for entry in length_entries if int(entry["length"]) >= 16]
    result = {
        "status": "OBSERVED",
        "classification": "reconnaissance only; not a gate",
        "precision_decimal_digits": mp.mp.dps,
        "length_trend_cell": {"beta": "2", "gamma_over_a": "0.75"},
        "length_trend": strip_raw(length_entries),
        "margin_monotone_decreasing_all_sampled_lengths": decreasing(length_entries),
        "margin_monotone_decreasing_even_subsequence": decreasing(even_entries),
        "margin_monotone_decreasing_odd_subsequence": decreasing(odd_entries),
        "tail_log_slopes": log_slopes(tail_entries),
        "beta_scan_fixed_gamma_over_a": "0.75",
        "beta_scan": strip_raw(beta_entries),
        "fraction_scan_fixed_beta": "2",
        "fraction_scan": strip_raw(fraction_entries),
    }
    print(json.dumps(result, sort_keys=True))


if __name__ == "__main__":
    main()
