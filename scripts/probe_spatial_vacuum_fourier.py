"""PRE-COMMITTED Fourier-sign and closed-parameter reconnaissance.

This is NOT a gate and licenses no theorem.  It evaluates the proposed global
Fourier mechanism only after the termwise-pairing and global-curvature routes
were rejected.

For the even 2*pi-periodic function

    f(k) = epsilon(k)/2,
    cosh(epsilon(k)) = A - B cos(k),

we use the complex/cosine coefficient convention

    fhat(n) = (1/(2*pi)) integral_0^(2*pi) f(k) exp(-i*n*k) dk
            = (1/pi) integral_0^pi f(k) cos(n*k) dk.

With this convention the exact grid-aliasing identity is

    sum_P f - sum_NS f = 2*L*sum_(m odd in Z) fhat(m*L)
                       = 4*L*sum_(m odd >= 1) fhat(m*L).

Thus fhat(n) <= 0 for every n >= 1 would give the required vacuum-quotient
sign.  The probe estimates fhat(1),...,fhat(40) at 120 decimal digits on two
independent periodic quadrature grids, N=2048 and N=4096, over eight cells in
q<1.  It reports every sign and the cross-resolution discrepancy; it does not
turn a finite sign sample into a theorem.

There is also an exact scalar simplification.  If u=tanh(a), v=tanh(gamma),
then

    (A-1)/B = (u^2+v^2)/(2*u*v) = cosh(log(u/v)).

Since a>gamma>0 in the nontrivial region,

    d = log(u/v),     x = exp(-d) = v/u = tanh(gamma)/tanh(a).

The target cell beta=2, gamma/a=0.75 is used to compare the observed
coefficients with the proposed exact ansatz -x^n/n.  No fit threshold is fixed
in this reconnaissance: its measured discrepancy, if the signs survive, is
the number that must be preregistered in a later gate.  Output is OBSERVED,
never PASS.  Explicit checks use no assertions.
"""

from __future__ import annotations

import json
import sys

import mpmath as mp


mp.mp.dps = 120
MAX_MODE = 40
GRIDS = (2048, 4096)
CELLS = (
    ("0.125", "0.10"),
    ("0.125", "0.75"),
    ("0.125", "0.99"),
    ("0.5", "0.50"),
    ("2", "0.10"),
    ("2", "0.75"),
    ("2", "0.99"),
    ("8", "0.75"),
)
TARGET_CELL = ("2", "0.75")


def fail(message: str, payload: object | None = None) -> "NoReturn":
    print(f"RESULT: FAIL: {message}", file=sys.stderr)
    if payload is not None:
        print(json.dumps(payload, sort_keys=True), file=sys.stderr)
    raise SystemExit(1)


def decimal(x: mp.mpf, digits: int = 80) -> str:
    return mp.nstr(x, digits, strip_zeros=False)


def parameters(beta: mp.mpf, fraction: mp.mpf) -> tuple[mp.mpf, mp.mpf, mp.mpf, mp.mpf, mp.mpf]:
    a = -mp.log(mp.tanh(beta)) / 2
    gamma = fraction * a
    if not (0 < gamma < a):
        fail("cell was not in 0 < gamma < a", {"beta": decimal(beta), "fraction": decimal(fraction)})
    A = mp.cosh(2 * a) * mp.cosh(2 * gamma)
    B = mp.sinh(2 * a) * mp.sinh(2 * gamma)
    x = mp.tanh(gamma) / mp.tanh(a)
    distance = mp.acosh((A - 1) / B)
    identity_error = abs(mp.exp(-distance) - x)
    if identity_error > mp.mpf("1e-105"):
        fail("closed x=exp(-d) identity failed numerically", {"error": decimal(identity_error)})
    return a, gamma, A, B, x


def f_value(A: mp.mpf, B: mp.mpf, k: mp.mpf) -> mp.mpf:
    argument = A - B * mp.cos(k)
    if argument < 1:
        fail("acosh argument below one", {"argument": decimal(argument)})
    return mp.acosh(argument) / 2


def discrete_coefficients(A: mp.mpf, B: mp.mpf, grid: int) -> list[mp.mpf]:
    sums = [mp.mpf(0) for _ in range(MAX_MODE + 1)]
    for index in range(grid):
        k = 2 * mp.pi * index / grid
        value = f_value(A, B, k)
        cos_k = mp.cos(k)
        previous = mp.mpf(1)
        current = cos_k
        sums[0] += value
        sums[1] += value * current
        for mode in range(2, MAX_MODE + 1):
            following = 2 * cos_k * current - previous
            sums[mode] += value * following
            previous, current = current, following
    return [entry / grid for entry in sums]


def cell_record(beta_text: str, fraction_text: str) -> tuple[dict[str, object], list[mp.mpf], mp.mpf]:
    beta = mp.mpf(beta_text)
    fraction = mp.mpf(fraction_text)
    _, gamma, A, B, x = parameters(beta, fraction)
    coarse = discrete_coefficients(A, B, GRIDS[0])
    fine = discrete_coefficients(A, B, GRIDS[1])
    mode_records = []
    positive_modes = []
    zero_modes = []
    max_abs_discrepancy = mp.mpf(0)
    max_relative_discrepancy = mp.mpf(0)
    for mode in range(1, MAX_MODE + 1):
        coefficient = fine[mode]
        discrepancy = abs(fine[mode] - coarse[mode])
        relative = discrepancy / abs(coefficient) if coefficient != 0 else mp.inf
        max_abs_discrepancy = max(max_abs_discrepancy, discrepancy)
        max_relative_discrepancy = max(max_relative_discrepancy, relative)
        if coefficient > 0:
            positive_modes.append(mode)
        elif coefficient == 0:
            zero_modes.append(mode)
        mode_records.append({
            "mode": mode,
            "coefficient": decimal(coefficient, 90),
            "coarse_fine_abs_difference": decimal(discrepancy, 40),
            "coarse_fine_relative_difference": decimal(relative, 40),
        })
    return ({
        "beta": beta_text,
        "gamma_over_a": fraction_text,
        "gamma": decimal(gamma, 50),
        "x_exact": decimal(x, 80),
        "positive_modes": positive_modes,
        "zero_modes": zero_modes,
        "all_modes_strictly_negative": not positive_modes and not zero_modes,
        "max_abs_resolution_difference": decimal(max_abs_discrepancy, 50),
        "max_relative_resolution_difference": decimal(max_relative_discrepancy, 50),
        "modes": mode_records,
    }, fine, x)


def main() -> None:
    records = []
    target_coefficients = None
    target_x = None
    for beta_text, fraction_text in CELLS:
        record, coefficients, x = cell_record(beta_text, fraction_text)
        records.append(record)
        if (beta_text, fraction_text) == TARGET_CELL:
            target_coefficients = coefficients
            target_x = x
    if target_coefficients is None or target_x is None:
        fail("target cell was not measured")

    selected_modes = (1, 2, 5, 10, 20, 30, 40)
    fit_records = []
    for mode in selected_modes:
        coefficient = target_coefficients[mode]
        if not coefficient < 0:
            fit_records.append({"mode": mode, "fit_available": False})
            continue
        exact_ansatz = -(target_x ** mode) / mode
        scaled_amplitude = (-mode * coefficient) / (target_x ** mode)
        root_x_fit = (-mode * coefficient) ** (mp.mpf(1) / mode)
        fit_records.append({
            "mode": mode,
            "fit_available": True,
            "coefficient": decimal(coefficient, 90),
            "minus_x_pow_n_over_n": decimal(exact_ansatz, 90),
            "coefficient_over_ansatz": decimal(coefficient / exact_ansatz, 70),
            "scaled_amplitude": decimal(scaled_amplitude, 70),
            "root_x_fit": decimal(root_x_fit, 70),
            "root_x_fit_error": decimal(abs(root_x_fit - target_x), 70),
        })

    positive_total = sum(len(record["positive_modes"]) for record in records)
    zero_total = sum(len(record["zero_modes"]) for record in records)
    print(json.dumps({
        "status": "OBSERVED",
        "classification": "finite Fourier-sign and fit reconnaissance only; not a gate",
        "precision_decimal_digits": mp.mp.dps,
        "quadrature_grids": list(GRIDS),
        "max_mode": MAX_MODE,
        "cells": records,
        "positive_coefficient_count": positive_total,
        "zero_coefficient_count": zero_total,
        "all_sampled_coefficients_strictly_negative": positive_total == 0 and zero_total == 0,
        "target_cell": {"beta": TARGET_CELL[0], "gamma_over_a": TARGET_CELL[1]},
        "target_x_exact": decimal(target_x, 100),
        "target_fit_records": fit_records,
    }, sort_keys=True))


if __name__ == "__main__":
    main()
