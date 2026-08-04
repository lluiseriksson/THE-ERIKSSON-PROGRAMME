"""Adversarial numerical checks for audit (49).

This is diagnostic evidence only, never a proof.  It uses mpmath directly,
not the earlier 392-point grid or the C4 arb recurrence.
"""

from __future__ import annotations

import random
import time

import mpmath as mp


SEED = 490060
CASES = 800


def rho(order: mp.mpf, x: mp.mpf) -> mp.mpf:
    return mp.besseli(order + 1, x) / mp.besseli(order, x)


def valid_domain_sweep() -> None:
    mp.mp.dps = 70
    rng = random.Random(SEED)
    least_lower = (mp.inf, None)
    least_upper = (mp.inf, None)
    started = time.perf_counter()

    for index in range(CASES):
        # Log-uniform stress: near-zero and large orders, nearly coincident
        # orders, and x across seventeen decades.  Every seventeenth case
        # pins the lower order exactly at the C4 endpoint mu = 0.
        mu = (
            mp.mpf("0")
            if index % 17 == 0
            else mp.power(10, rng.uniform(-10, 3)) * mp.mpf(rng.random())
        )
        delta = mp.power(10, rng.uniform(-12, 2))
        nu = mu + delta
        x = mp.power(10, rng.uniform(-10, 7))

        difference = rho(mu, x) - rho(nu, x)
        barrier = delta / x
        upper_slack = barrier - difference
        lower_relative = difference / barrier
        upper_relative = upper_slack / barrier
        record = (mu, nu, x, difference, barrier, upper_slack)

        if lower_relative < least_lower[0]:
            least_lower = (lower_relative, record)
        if upper_relative < least_upper[0]:
            least_upper = (upper_relative, record)
        if not (difference > 0 and upper_slack > 0):
            raise AssertionError((index, record))

    print(f"valid-domain cases: PASS ({CASES}, seed={SEED})")
    print(f"elapsed seconds: {time.perf_counter() - started:.6f}")
    for label, result in (
        ("min (rho_mu-rho_nu)/barrier", least_lower),
        ("min upper_slack/barrier", least_upper),
    ):
        print(label, mp.nstr(result[0], 25))
        print("  mu nu x difference barrier upper_slack")
        print(" ".join(mp.nstr(value, 25) for value in result[1]))


def unrestricted_order_witness() -> None:
    mp.mp.dps = 100
    mu = mp.mpf("-0.8")
    nu = mp.mpf("-0.4")
    x = mp.mpf("10")
    rho_mu = rho(mu, x)
    rho_nu = rho(nu, x)
    difference = rho_mu - rho_nu
    barrier = (nu - mu) / x

    print("unrestricted-real-order witness")
    for label, value in (
        ("mu", mu),
        ("nu", nu),
        ("x", x),
        ("rho_mu", rho_mu),
        ("rho_nu", rho_nu),
        ("difference", difference),
        ("barrier", barrier),
        ("excess", difference - barrier),
    ):
        print(f"{label}: {mp.nstr(value, 60)}")
    if not difference > barrier:
        raise AssertionError("registered witness did not violate the upper bound")


if __name__ == "__main__":
    valid_domain_sweep()
    unrestricted_order_witness()
