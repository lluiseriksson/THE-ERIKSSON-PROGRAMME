"""Candidate-only local S2 t-jet probe.

This exercises the exact t-jets in ``surface_remainder_y_integrator`` at one
fixed stress point.  It is deliberately not a global S2/K2/G2 certificate:
the transcript records a single (beta,t) point and the candidate label.
"""

from __future__ import annotations

import hashlib
from pathlib import Path
import platform
import subprocess
import sys

import flint
from flint import arb, ctx

from surface_remainder_y_integrator import sensitivity_centered_main_y_t


def theta3(t: arb) -> arb:
    c = (t / 4).cos()
    leading = (4*c**2 - 1) / (8*c**3)
    r3 = (-12*c**6 - 485*c**4 + 796*c**2 - 224) / (1024*c**9)
    return (arb(r3.abs_upper()) + arb("1.10")*leading/c**2
            + arb("0.5")/c**3 + arb("0.05"))


def provenance() -> dict[str, str]:
    path = Path(__file__).resolve()
    root = path.parents[1]
    try:
        head = subprocess.check_output(
            ["git", "-c", "safe.directory=*", "rev-parse", "HEAD"],
            cwd=root, text=True,
            stderr=subprocess.DEVNULL).strip()
    except Exception:
        head = "UNAVAILABLE"
    return {
        "script": str(path.relative_to(root)).replace("\\", "/"),
        "script_sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
        "git_head": head,
        "python": platform.python_version(),
        "python_flint": getattr(flint, "__version__", "UNKNOWN"),
        "arb_prec_bits": str(ctx.prec),
    }


def main() -> int:
    ctx.prec = 120
    beta = int(sys.argv[1]) if len(sys.argv) > 1 else 20
    t = arb(sys.argv[2]) if len(sys.argv) > 2 else arb("2.9")
    pilot = int(sys.argv[3]) if len(sys.argv) > 3 else 256
    cells = int(sys.argv[4]) if len(sys.argv) > 4 else 2048
    seed_grid = int(sys.argv[5]) if len(sys.argv) > 5 else 4
    for key, value in provenance().items():
        print(f"PROVENANCE {key}={value}", flush=True)
    print(f"CONFIG beta={beta} t={t.str(24)} pilot_cells={pilot} "
          f"max_cells={cells} seed_grid={seed_grid} target=Y_t_second",
          flush=True)
    y, effective, calibration, _ = sensitivity_centered_main_y_t(
        arb(1)/beta, t=t, pilot_cells=pilot, max_cells=cells,
        target="c2", seed_grid=seed_grid,
    )
    budget = theta3(t)
    half_upper = y.c2.abs_upper() / 2
    print(f"effective_cells={effective}", flush=True)
    print(f"calibration={calibration.str(30)}", flush=True)
    print(f"Y_t0={y.c0.str(30)}", flush=True)
    print(f"Y_t1={y.c1.str(30)}", flush=True)
    print(f"Y_t2={y.c2.str(30)}", flush=True)
    print(f"theta3={budget.str(30)}", flush=True)
    print(f"half_abs_upper={half_upper.str(30)}", flush=True)
    print("CANDIDATE_LOCAL_PASS: exact t-jet enclosure at one point; "
          "no S2/K2/G2/S1'''/S2''' promotion", flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
