"""Go/no-go driver for the preregistered polar K4 modulus."""

from fractions import Fraction
import hashlib
import platform
import subprocess
from pathlib import Path

from flint import arb, ctx

from probe_surface_k4_ball_reach_realpart import old_crude, tail
from surface_remainder_k4_exponential_realpart_modulus import (
    exponent_real_upper_polar,
    modulus_upper,
)

ROOT = Path(__file__).resolve().parents[1]
T = Fraction(29, 10)
RHO = Fraction(7, 100)
RADIUS = Fraction(4)
PHI = Fraction(12566371, 1_000_000)
R_TARGET = Fraction(59, 2000)
HEADROOM_HALF = arb("0.5") * (1 - arb("0.2758"))


def main():
    ctx.prec = 140
    head = subprocess.check_output(
        ["git", "-c", f"safe.directory={ROOT.as_posix()}", "rev-parse", "HEAD"],
        cwd=ROOT, text=True).strip()
    print("K4 BALL REACH POLAR REALPART PROBE")
    print("python", platform.python_version())
    print("arb_bits", ctx.prec)
    print("git_head", head)
    print("config t", T, "rho", RHO, "R", RADIUS, "Phi", PHI,
          "r", R_TARGET, "radial 4 angular 16 spatial 2 phi 16 N<=16")
    best = None
    for mirror in (False, True):
        name = "mirror" if mirror else "main"
        exponent = exponent_real_upper_polar(
            t=T, rho=RHO, radius=RADIUS, phi_max=PHI,
            radial_splits=4, angular_splits=16, spatial_splits=2,
            phi_splits=16, mirror=mirror,
        )
        new = modulus_upper(exponent, t=T, phi_max=PHI)
        print(name, "old_crude", old_crude(mirror).str(30))
        print(name, "exponent_real_upper", exponent.str(30))
        print(name, "M_sector", new.str(30))
        for n in range(17):
            value = tail(new, n)
            print(name, f"N={n}", "tail2", value.str(30))
            if best is None or value < best[1]:
                best = (name, value)
    assert best is not None
    status = "PASS" if best[1] < HEADROOM_HALF else "FAIL"
    print("headroom_half", HEADROOM_HALF.str(30))
    print("best", best[0], "tail2", best[1].str(30))
    print("K4 BALL REACH POLAR REALPART", status)
    print("SCOPE design probe only; no K4/G6 promotion")
    return 0 if status == "PASS" else 1


if __name__ == "__main__":
    raise SystemExit(main())
