"""PRE-COMMITTED curvature and complex-singularity reconnaissance.

This is NOT a gate and licenses no theorem.  It audits the proposed mechanism
for the finite periodic/antiperiodic vacuum quotient before any Lean work.

For

    f(k) = epsilon(k)/2,
    cosh(epsilon(k)) = A - B cos(k),

direct differentiation gives the sign of f'' from

    cos(k) * ((A - B cos(k))^2 - 1)
      - B * (A - B cos(k)) * sin(k)^2.

The script checks the endpoint signs and samples the curvature on (0,pi).  A
positive sign at zero and negative sign at pi rejects global convexity and
global concavity; this is an observed corroboration of the displayed exact
formula, not its proof.

The nearest acosh branch point is predicted at imaginary distance

    d = acosh((A - 1)/B).

FALSIFIABLE NUMERICAL PREDICTION COMMITTED BEFORE EXECUTION for beta=2 and
gamma/a=0.75:

    0.287 <= d <= 0.291  (central prediction approximately 0.2887),

and the effective decay exponent from the vacuum margins at L=96 and L=128
must differ from d by at most 0.008.  Margins are evaluated as
``-expm1(log_ratio)`` at 160 decimal digits, avoiding subtraction of two nearby
numbers.  A 100-decimal interval encloses d and must lie inside the committed
band.  Failure exits nonzero.  Success is still reported as OBSERVED, never
PASS, and licenses no inequality, Fourier theorem, sector bound, or Clifford
infrastructure.
"""

from __future__ import annotations

import json
import sys

import mpmath as mp


mp.mp.dps = 160
BETAS = tuple(mp.mpf(x) for x in ("0.125", "0.5", "2", "8"))
FRACTIONS = tuple(mp.mpf(x) for x in ("0.10", "0.50", "0.75", "0.99"))
CURVATURE_SAMPLES = 512
TARGET_BETA = mp.mpf("2")
TARGET_FRACTION = mp.mpf("0.75")
TARGET_LENGTHS = (48, 64, 80, 96, 128)
PREDICTED_D_LOWER = mp.mpf("0.287")
PREDICTED_D_UPPER = mp.mpf("0.291")
EXPONENT_TOLERANCE = mp.mpf("0.008")


def fail(message: str, payload: object | None = None) -> "NoReturn":
    print(f"RESULT: FAIL: {message}", file=sys.stderr)
    if payload is not None:
        print(json.dumps(payload, sort_keys=True), file=sys.stderr)
    raise SystemExit(1)


def decimal(x: mp.mpf, digits: int = 80) -> str:
    return mp.nstr(x, digits, strip_zeros=False)


def dual_coupling(beta: mp.mpf) -> mp.mpf:
    return -mp.log(mp.tanh(beta)) / 2


def dispersion_parameters(beta: mp.mpf, fraction: mp.mpf) -> tuple[mp.mpf, mp.mpf, mp.mpf, mp.mpf]:
    a = dual_coupling(beta)
    gamma = fraction * a
    A = mp.cosh(2 * a) * mp.cosh(2 * gamma)
    B = mp.sinh(2 * a) * mp.sinh(2 * gamma)
    if not B > 0:
        fail("dispersion coefficient B was not positive", {"beta": decimal(beta), "fraction": decimal(fraction)})
    return a, gamma, A, B


def epsilon(A: mp.mpf, B: mp.mpf, momentum: mp.mpf) -> mp.mpf:
    argument = A - B * mp.cos(momentum)
    if argument < 1:
        fail("acosh argument below one", {"argument": decimal(argument)})
    return mp.acosh(argument)


def curvature_numerator(A: mp.mpf, B: mp.mpf, momentum: mp.mpf) -> mp.mpf:
    x = A - B * mp.cos(momentum)
    return mp.cos(momentum) * (x * x - 1) - B * x * mp.sin(momentum) ** 2


def log_ratio_and_margin(length: int, A: mp.mpf, B: mp.mpf) -> tuple[mp.mpf, mp.mpf]:
    periodic = mp.fsum(
        epsilon(A, B, 2 * mp.pi * j / length)
        for j in range(length)
    )
    antiperiodic = mp.fsum(
        epsilon(A, B, 2 * mp.pi * (mp.mpf(j) + mp.mpf("0.5")) / length)
        for j in range(length)
    )
    log_ratio = (periodic - antiperiodic) / 2
    if not log_ratio < 0:
        fail("vacuum log quotient was not negative", {"length": length, "log_ratio": decimal(log_ratio)})
    margin = -mp.expm1(log_ratio)
    if not margin > 0:
        fail("stable vacuum margin was not positive", {"length": length, "margin": decimal(margin)})
    return log_ratio, margin


def interval_distance() -> tuple[str, bool]:
    iv = mp.iv
    iv.dps = 100

    def iv_cosh(x):
        return (iv.exp(x) + iv.exp(-x)) / 2

    def iv_sinh(x):
        return (iv.exp(x) - iv.exp(-x)) / 2

    def iv_acosh(x):
        return iv.log(x + iv.sqrt(x * x - 1))

    beta = iv.mpf("2")
    fraction = iv.mpf("0.75")
    tanh_beta = iv_sinh(beta) / iv_cosh(beta)
    a = -iv.log(tanh_beta) / 2
    gamma = fraction * a
    A = iv_cosh(2 * a) * iv_cosh(2 * gamma)
    B = iv_sinh(2 * a) * iv_sinh(2 * gamma)
    distance = iv_acosh((A - 1) / B)
    inside_band = bool(distance > iv.mpf("0.287") and distance < iv.mpf("0.291"))
    if not inside_band:
        fail("interval singularity distance left preregistered band", {"distance": str(distance)})
    return str(distance), inside_band


def main() -> None:
    curvature_records = []
    for beta in BETAS:
        for fraction in FRACTIONS:
            _, _, A, B = dispersion_parameters(beta, fraction)
            at_zero = curvature_numerator(A, B, mp.mpf(0))
            at_pi = curvature_numerator(A, B, mp.pi)
            if not at_zero > 0:
                fail("curvature numerator was not positive at zero", {"beta": decimal(beta), "fraction": decimal(fraction)})
            if not at_pi < 0:
                fail("curvature numerator was not negative at pi", {"beta": decimal(beta), "fraction": decimal(fraction)})
            signs = []
            first_negative_index = None
            for index in range(1, CURVATURE_SAMPLES):
                value = curvature_numerator(A, B, mp.pi * index / CURVATURE_SAMPLES)
                sign = 1 if value > 0 else -1 if value < 0 else 0
                signs.append(sign)
                if sign < 0 and first_negative_index is None:
                    first_negative_index = index
            if first_negative_index is None:
                fail("curvature scan found no negative sample", {"beta": decimal(beta), "fraction": decimal(fraction)})
            curvature_records.append({
                "beta": decimal(beta, 20),
                "gamma_over_a": decimal(fraction, 20),
                "endpoint_zero_sign": "positive",
                "endpoint_pi_sign": "negative",
                "positive_samples": signs.count(1),
                "negative_samples": signs.count(-1),
                "zero_samples": signs.count(0),
                "first_negative_k_over_pi": decimal(mp.mpf(first_negative_index) / CURVATURE_SAMPLES, 30),
            })

    _, _, target_A, target_B = dispersion_parameters(TARGET_BETA, TARGET_FRACTION)
    distance = mp.acosh((target_A - 1) / target_B)
    if not (PREDICTED_D_LOWER <= distance <= PREDICTED_D_UPPER):
        fail("point singularity distance left preregistered band", {"distance": decimal(distance)})
    distance_interval, interval_inside = interval_distance()

    margins = []
    for length in TARGET_LENGTHS:
        log_ratio, margin = log_ratio_and_margin(length, target_A, target_B)
        margins.append({
            "length": length,
            "log_ratio": decimal(log_ratio, 100),
            "margin": decimal(margin, 100),
            "log_margin": decimal(mp.log(margin), 100),
        })

    slopes = []
    for left, right in zip(margins, margins[1:]):
        delta = int(right["length"]) - int(left["length"])
        slope = (mp.mpf(str(right["log_margin"])) - mp.mpf(str(left["log_margin"]))) / delta
        slopes.append({
            "from_length": left["length"],
            "to_length": right["length"],
            "slope": decimal(slope, 60),
            "effective_distance": decimal(-slope, 60),
            "distance_error": decimal(abs(-slope - distance), 60),
        })
    final_error = mp.mpf(str(slopes[-1]["distance_error"]))
    if final_error > EXPONENT_TOLERANCE:
        fail(
            "late effective exponent missed singularity prediction",
            {"distance": decimal(distance), "error": decimal(final_error), "tolerance": decimal(EXPONENT_TOLERANCE)},
        )

    print(json.dumps({
        "status": "OBSERVED",
        "classification": "curvature and singularity reconnaissance only; not a gate",
        "precision_decimal_digits": mp.mp.dps,
        "curvature_records": curvature_records,
        "all_cells_change_curvature_sign": True,
        "target_cell": {"beta": "2", "gamma_over_a": "0.75"},
        "predicted_distance_band": [decimal(PREDICTED_D_LOWER, 10), decimal(PREDICTED_D_UPPER, 10)],
        "singularity_distance": decimal(distance, 100),
        "singularity_distance_interval": distance_interval,
        "interval_inside_predicted_band": interval_inside,
        "margins": margins,
        "effective_slopes": slopes,
        "late_exponent_tolerance": decimal(EXPONENT_TOLERANCE, 10),
        "late_exponent_prediction_met": True,
    }, sort_keys=True))


if __name__ == "__main__":
    main()
