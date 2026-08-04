"""Kill-test for the proposed Wronskian kernel/parabolic route.

This is a high-precision diagnostic, not an interval certificate.  The exact
identities tested here are written and proved on paper in
``docs/WRONSKIAN-REDUCTION-51-RESULT.md``.  The numerical job is deliberately
small: it checks normalizations, measures the parity loss at t=pi, and tests a
finite-support perturbation that a structurally bounded barrier must reject.
"""

from __future__ import annotations

from dataclasses import dataclass
from math import ceil, sqrt
import platform

import mpmath as mp


@dataclass
class BesselData:
    beta: mp.mpf
    modes: int
    values: list[mp.mpf]
    a: list[mp.mpf]
    b: list[mp.mpf]


def make_data(beta_value: int | str | mp.mpf, extra: int = 80) -> BesselData:
    beta = mp.mpf(beta_value)
    modes = max(20, ceil(float(beta) + 12 * sqrt(float(beta)) + extra))
    values = [mp.besseli(m, beta) for m in range(modes + 2)]
    a = [mp.mpf("0")] * (modes + 1)
    b = [mp.mpf("0")] * (modes + 1)
    for m in range(1, modes + 1):
        im = values[m]
        a[m] = im**2 * (
            (m - 1) * values[m - 1] ** 2
            + (m + 1) * values[m + 1] ** 2
        )
        b[m] = m * im**4
    return BesselData(beta, modes, values, a, b)


def fourier(data: BesselData, t: mp.mpf) -> tuple[mp.mpf, ...]:
    fa = mp.fsum(data.a[m] * mp.sin(m * t) for m in range(1, data.modes + 1))
    fb = mp.fsum(data.b[m] * mp.sin(m * t) for m in range(1, data.modes + 1))
    fap = mp.fsum(
        m * data.a[m] * mp.cos(m * t) for m in range(1, data.modes + 1)
    )
    fbp = mp.fsum(
        m * data.b[m] * mp.cos(m * t) for m in range(1, data.modes + 1)
    )
    return fa, fb, fap, fbp


def wronskian(data: BesselData, t: mp.mpf) -> mp.mpf:
    fa, fb, fap, fbp = fourier(data, t)
    return 2 * (fap * fb - fa * fbp)


def endpoint_quantities(data: BesselData) -> tuple[mp.mpf, ...]:
    c_terms = [
        mp.mpf(m * (m + 1) * (2 * m + 1))
        * data.values[m] ** 2
        * data.values[m + 1] ** 2
        / 6
        for m in range(1, data.modes + 1)
    ]
    b_terms = [
        mp.mpf(m * m) * data.values[m] ** 4
        for m in range(1, data.modes + 1)
    ]
    c3 = mp.fsum(
        (1 if m % 2 else -1) * c_terms[m - 1]
        for m in range(1, data.modes + 1)
    )
    bpi = mp.fsum(
        (1 if m % 2 else -1) * b_terms[m - 1]
        for m in range(1, data.modes + 1)
    )
    return c3, mp.fsum(c_terms), bpi, mp.fsum(b_terms)


def check_graf_kernel() -> None:
    data = make_data(8, extra=60)
    worst = mp.mpf("0")
    for phi in (mp.mpf("0.2"), mp.mpf("1.1"), mp.mpf("2.7")):
        plus = data.values[0] ** 2 + 2 * mp.fsum(
            data.values[m] ** 2 * mp.cos(m * phi)
            for m in range(1, data.modes + 1)
        )
        minus = data.values[0] ** 2 + 2 * mp.fsum(
            (-1) ** m * data.values[m] ** 2 * mp.cos(m * phi)
            for m in range(1, data.modes + 1)
        )
        exact_plus = mp.besseli(0, 2 * data.beta * mp.cos(phi / 2))
        exact_minus = mp.besseli(0, 2 * data.beta * mp.sin(phi / 2))
        worst = max(worst, abs(plus - exact_plus), abs(minus - exact_minus))
    print("KERNEL_GRAF_SANITY residual_max=" + mp.nstr(worst, 8))


def check_small_beta_anchor() -> None:
    print("SMALL_BETA_ANCHOR target=(-4096/beta^10)W -> 4 sin(t)^3")
    for beta in ("0.05", "0.02", "0.01"):
        data = make_data(beta, extra=20)
        ratios = []
        for t in (mp.mpf("0.7"), mp.mpf("1.4"), mp.mpf("2.4")):
            scaled = -mp.mpf(4096) * wronskian(data, t) / data.beta**10
            ratios.append(scaled / (4 * mp.sin(t) ** 3))
        print(
            "  beta=%s ratios=%s"
            % (beta, ",".join(mp.nstr(value, 12) for value in ratios))
        )


def normalized_j(beta: mp.mpf, u: mp.mpf) -> mp.mpf:
    """The signed c3 integrand divided by f(y) f(z) beta^3."""
    y = 2 * beta * mp.sin(u)
    z = 2 * beta * mp.cos(u)
    f = lambda x: mp.besseli(1, x) / 2
    fp = lambda x: (mp.besseli(0, x) + mp.besseli(2, x)) / 4
    fpp = lambda x: (3 * mp.besseli(1, x) + mp.besseli(3, x)) / 8
    j_value = (
        -(z**2) * fp(y) * fp(z)
        + z * y**2 * fp(y) * fpp(z)
        + y * f(y) * fp(z)
    )
    return j_value / (f(y) * f(z) * beta**3)


def check_endpoint() -> None:
    rows = []
    print("ENDPOINT_CANCELLATION ratio=(c3/c3_abs)*(Bpi/Bpi_abs)")
    for beta in (8, 16, 32, 64):
        data = make_data(beta)
        c3, c3_abs, bpi, bpi_abs = endpoint_quantities(data)
        ratio = abs(c3 / c3_abs) * abs(bpi / bpi_abs)
        rows.append((beta, ratio, c3, bpi, data))
        print(
            "  beta=%d ratio=%s log_ratio=%s"
            % (beta, mp.nstr(ratio, 9), mp.nstr(mp.log(ratio), 12))
        )
    for left, right in zip(rows, rows[1:]):
        slope = -(mp.log(right[1]) - mp.log(left[1])) / (right[0] - left[0])
        print("  fitted_slope_%d_%d=%s" % (left[0], right[0], mp.nstr(slope, 12)))
    print("  asymptotic_slope=8-4sqrt(2)=" + mp.nstr(8 - 4 * mp.sqrt(2), 12))

    beta, _, c3, bpi, data = rows[2]
    d = mp.mpf("1e-4")
    endpoint_limit = -4 * c3 * bpi
    quotient = wronskian(data, mp.pi - d) / d**3
    print(
        "ENDPOINT_IDENTITY beta=%d [W(pi-d)/d^3]/[-4c3Bpi]=%s"
        % (beta, mp.nstr(quotient / endpoint_limit, 14))
    )

    # p=(2,1,0,...) has zero alternating first moment and cubic coefficient 1.
    # A -> A-2*c3*p therefore flips c3 while leaving B and its kernel fixed.
    perturbed = list(data.a)
    perturbed[1] -= 4 * c3
    perturbed[2] -= 2 * c3
    original_ratios = [data.a[m] / data.b[m] for m in range(1, 8)]
    perturbed_ratios = [perturbed[m] / data.b[m] for m in range(1, 8)]
    positive = all(perturbed[m] > 0 for m in range(1, 8))
    increasing = all(
        perturbed_ratios[m] < perturbed_ratios[m + 1]
        for m in range(len(perturbed_ratios) - 1)
    )
    print(
        "STRUCTURAL_PERTURBATION beta=32 c3_over_A1=%s positive=%s ratio_increasing=%s"
        % (mp.nstr(c3 / data.a[1], 10), positive, increasing)
    )
    assert all(
        original_ratios[m] < original_ratios[m + 1]
        for m in range(len(original_ratios) - 1)
    )
    assert positive and increasing

    for beta_value in (1, 8, 32, 125):
        beta_mpf = mp.mpf(beta_value)
        samples = [
            normalized_j(beta_mpf, mp.pi * j / 400)
            for j in range(1, 200)
        ]
        negative = sum(value < 0 for value in samples)
        print(
            "C3_KERNEL_SIGN beta=%d negative_samples=%d/199 min=%s max=%s"
            % (
                beta_value,
                negative,
                mp.nstr(min(samples), 8),
                mp.nstr(max(samples), 8),
            )
        )
        assert negative > 0 and negative < len(samples)


def main() -> int:
    mp.mp.dps = 180
    print("WRONSKIAN_ENDPOINT_KILL_TEST")
    print("python=" + platform.python_version() + " mpmath=" + mp.__version__)
    check_graf_kernel()
    check_small_beta_anchor()
    check_endpoint()
    print("VERDICT FB_KERNEL_PASS; GLOBAL_PARABOLIC_ROUTE_FAILS_ENDPOINT_KILL_TEST")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
