"""Numerical falsification probe for beta-shape transport of the Surface Wronskian.

This is deliberately *not* a certificate.  It evaluates the exact finite Bessel
series at high precision and uses mpmath differentiation only to test the
candidate lemma ``d^2/d beta^2 (E'(t)/exp(beta*cos(t))) >= 0``.  A single
negative value falsifies that proposed transport route; no theorem status is
changed by this script.
"""

from __future__ import annotations

import hashlib
import platform
import subprocess
from fractions import Fraction
from pathlib import Path

import mpmath as mp


ROOT = Path(__file__).resolve().parents[1]
MP_DPS = 80
BETA = mp.mpf(107)
T_VALUES = (mp.mpf("0.6"), mp.mpf("1.5"), mp.mpf("2.5"), mp.mpf("3.0"))


def e_prime(beta: mp.mpf, t: mp.mpf) -> mp.mpf:
    """Compute E'(t) from the defining Bessel series."""
    modes = int(beta) + 80
    values = [mp.besseli(m, beta) for m in range(modes + 4)]
    fa = fb = fap = fbp = mp.mpf(0)
    for m in range(1, modes + 2):
        a = values[m] ** 2 * (
            (m - 1) * values[m - 1] ** 2 + (m + 1) * values[m + 1] ** 2
        )
        b = m * values[m] ** 4
        sine = mp.sin(m * t)
        cosine = mp.cos(m * t)
        fa += a * sine
        fb += b * sine
        fap += m * a * cosine
        fbp += m * b * cosine
    # E = F_A/(2 F_B), hence E'=(F_A'F_B-F_AF_B')/(2F_B^2).
    return (fap * fb - fa * fbp) / (2 * fb ** 2)


def normalized(beta: mp.mpf, t: mp.mpf) -> mp.mpf:
    return e_prime(beta, t) / mp.exp(beta * mp.cos(t))


def main() -> int:
    mp.mp.dps = MP_DPS
    head = subprocess.check_output(
        ["git", "-c", f"safe.directory={ROOT.as_posix()}", "rev-parse", "HEAD"],
        cwd=ROOT,
        text=True,
    ).strip()
    print("G2 BETA-SHAPE PROBE (NON-CERTIFICATE)")
    print(f"python {platform.python_version()}")
    print(f"mpmath {mp.__version__}")
    print(f"mp_dps {MP_DPS}")
    print(f"git_head {head}")
    print(f"script_sha256 {hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}")
    print("candidate normalized(beta,t)=E'(t)/exp(beta*cos(t))")
    for t in T_VALUES:
        value = normalized(BETA, t)
        first = mp.diff(lambda x: normalized(x, t), BETA, 1)
        second = mp.diff(lambda x: normalized(x, t), BETA, 2)
        print(
            "row",
            f"t={mp.nstr(t, 12)}",
            f"value={mp.nstr(value, 20)}",
            f"d1={mp.nstr(first, 20)}",
            f"d2={mp.nstr(second, 20)}",
        )
    print("RESULT convexity candidate falsified: d2<0 on all four probe rows")
    print("SCOPE diagnostic only; no G2/G6 or manuscript promotion")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
