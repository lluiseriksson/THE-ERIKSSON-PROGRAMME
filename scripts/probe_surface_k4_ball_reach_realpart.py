"""Go/no-go driver for the preregistered K4 real-part modulus."""

from __future__ import annotations

from fractions import Fraction
import hashlib
import platform
import subprocess

from flint import arb, ctx

from surface_remainder_k4_exponential_realpart_modulus import (
    exponent_real_upper,
    modulus_upper,
)


ROOT = __import__("pathlib").Path(__file__).resolve().parents[1]
T = Fraction(29, 10)
RHO = Fraction(7, 100)
RADIUS = Fraction(4)
PHI = Fraction(12566371, 1_000_000)
R_TARGET = Fraction(59, 2000)
HEADROOM_HALF = arb("0.5") * (1 - arb("0.2758"))


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def old_crude(mirror=False):
    t = arb(T.numerator) / arb(T.denominator)
    rho = arb(RHO.numerator) / arb(RHO.denominator)
    radius = arb(RADIUS.numerator) / arb(RADIUS.denominator)
    phi = arb(PHI.numerator) / arb(PHI.denominator)
    amplitude = (t / 4).sin() if mirror else (t / 4).cos()
    x = rho * radius**2 / 4
    sinc = (x.sqrt().sinh() / x.sqrt())**2
    p_abs = (radius**2 / 4 * sinc).upper()
    delta_a = (rho * (2 * p_abs + rho * p_abs**2 / amplitude**2)).upper()
    sqrt_mod = ((1 + delta_a).sqrt()).upper()
    s_abs = (2 * (rho.sqrt() * phi / 2).sinh()**2 / rho).upper()
    return (arb.pi() * phi * (4 * amplitude * sqrt_mod * s_abs).exp()).upper()


def tail(modulus, n):
    ratio = arb(R_TARGET.numerator) / arb(R_TARGET.denominator)
    return modulus * (n + 1) * (n + 2) * ratio**max(n - 1, 0) / (1 - ratio)


def main():
    ctx.prec = 140
    head = subprocess.check_output(
        ["git", "-c", f"safe.directory={ROOT.as_posix()}", "rev-parse", "HEAD"],
        cwd=ROOT, text=True).strip()
    print("K4 BALL REACH REALPART PROBE")
    print("python", platform.python_version())
    print("arb_bits", ctx.prec)
    print("git_head", head)
    print("config", "t", T, "rho", RHO, "R", RADIUS,
          "Phi", PHI, "r", R_TARGET, "N<=16")
    best = None
    for mirror in (False, True):
        name = "mirror" if mirror else "main"
        old = old_crude(mirror)
        exponent = exponent_real_upper(t=T, rho=RHO, radius=RADIUS,
                                        phi_max=PHI, mirror=mirror)
        new = modulus_upper(exponent, t=T, phi_max=PHI)
        print(name, "old_crude", old.str(30))
        print(name, "exponent_real_upper", exponent.str(30))
        print(name, "M_realpart", new.str(30))
        for n in range(17):
            value = tail(new, n)
            print(name, f"N={n}", "tail2", value.str(30))
            if best is None or value < best[1]:
                best = (name, n, value)
    assert best is not None
    status = "PASS" if best[2] < HEADROOM_HALF else "FAIL"
    print("headroom_half", HEADROOM_HALF.str(30))
    print("best", best[0], "N", best[1], "tail2", best[2].str(30))
    print("K4 BALL REACH REALPART", status)
    print("SCOPE design probe only; no K4/G6 promotion")
    return 0 if status == "PASS" else 1


if __name__ == "__main__":
    raise SystemExit(main())
