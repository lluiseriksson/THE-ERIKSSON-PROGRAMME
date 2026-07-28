"""Direct joint-remainder judge for the repaired main-saddle carrier.

The default run is a manifested design point at (t,beta)=(2.9,20).  It is
not a uniform G2 certificate; the terminal word deliberately says
DESIGN_POINT_PASS.
"""

from __future__ import annotations

import hashlib
from pathlib import Path
import platform
import subprocess
import sys

import flint
from flint import arb, ctx

from surface_remainder_y_integrator import sensitivity_centered_main_y


def closed_forms(t: arb) -> tuple[arb, arb, arb, arb]:
    c = (t / 4).cos()
    leading = (4*c**2-1)/(8*c**3)
    r2 = (-8*c**4+15*c**2-4)/(32*c**6)
    r3 = (-12*c**6-485*c**4+796*c**2-224)/(1024*c**9)
    theta3 = (arb(r3.abs_upper()) + arb("1.10")*leading/c**2
              + arb("0.5")/c**3 + arb("0.05"))
    return leading, r2, r3, theta3


def judge_value(y: arb, delta: arb, t: arb) -> dict[str, arb | bool]:
    leading, r2, r3, theta3 = closed_forms(t)
    model = leading+r2*delta
    residual = y-model
    residual_abs = arb(residual.abs_upper())
    budget = theta3*delta**2
    return {
        "leading": leading,
        "r2": r2,
        "r3": r3,
        "theta3": theta3,
        "model": model,
        "residual": residual,
        "residual_abs": residual_abs,
        "budget": budget,
        "margin": budget-residual_abs,
        "passed": bool(residual_abs < budget),
    }


def provenance() -> dict[str, str | int]:
    path = Path(__file__).resolve()
    root = path.parents[1]
    try:
        head = subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=root, text=True,
            stderr=subprocess.DEVNULL).strip()
    except Exception:
        head = "UNAVAILABLE"
    return {
        "script": str(path.relative_to(root)).replace("\\", "/"),
        "script_sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
        "git_head": head,
        "python": platform.python_version(),
        "python_flint": getattr(flint, "__version__", "UNKNOWN"),
        "arb_prec_bits": ctx.prec,
    }


def main() -> int:
    ctx.prec = 100
    beta = int(sys.argv[1]) if len(sys.argv) > 1 else 20
    cells = int(sys.argv[2]) if len(sys.argv) > 2 else 65536
    t = arb(sys.argv[3]) if len(sys.argv) > 3 else arb("2.9")
    for key, value in provenance().items():
        print(f"PROVENANCE {key}={value}", flush=True)
    print(f"CONFIG beta={beta} t={t.str(20)} target=c0 "
          f"pilot_cells=1024 max_cells={cells}", flush=True)
    delta = arb(1)/beta
    y, effective, calibration, _ = sensitivity_centered_main_y(
        delta, pilot_cells=1024, max_cells=cells, target="c0", t=t
    )
    result = judge_value(y.c0, delta, t)
    print(f"effective_cells={effective}", flush=True)
    print(f"calibration={calibration.str(30)}", flush=True)
    print(f"Y={y.c0.str(30)}", flush=True)
    for key in ("leading", "r2", "r3", "theta3", "model",
                "residual", "residual_abs", "budget", "margin"):
        print(f"{key}={result[key].str(30)}", flush=True)
    if result["passed"]:
        print("DESIGN_POINT_PASS: direct joint remainder at one point; "
              "G2 remains OPEN", flush=True)
        return 0
    print("DESIGN_POINT_FAIL: terminal for this point configuration", flush=True)
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
