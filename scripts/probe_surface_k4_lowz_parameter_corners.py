"""Pointwise parameter-corner diagnostic for the low-z K4 candidate.

This deliberately reuses the candidate weighted smoke with a fixed spatial
cell budget and changes only ``delta`` and ``t``.  It is a sensitivity
diagnostic, not a parameter-box certificate: each point is evaluated
independently and no interval hull is formed.
"""

from __future__ import annotations

import argparse
import platform
import subprocess
from pathlib import Path

from flint import arb, ctx

import probe_surface_k4_lowz_dispatch_weighted_smoke as smoke


ROOT = Path(__file__).resolve().parents[1]


def git_head() -> str:
    return subprocess.check_output(
        ["git", "-c", "safe.directory=*", "rev-parse", "HEAD"],
        cwd=ROOT, text=True,
    ).strip()


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-cells", type=int, default=4096)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    ctx.prec = 100
    delta0 = arb(1) / 15
    t0 = arb("2.9")
    points = (
        ("center", delta0, t0),
        ("delta_lo", arb("0.06665"), t0),
        ("delta_hi", arb("0.0666833333333333"), t0),
        ("t_lo", delta0, arb("2.8999")),
        ("t_hi", delta0, arb("2.9001")),
    )
    lines = [
        "SURFACE K4 LOW-Z PARAMETER-CORNER DIAGNOSTIC",
        f"git_head {git_head()}",
        f"python {platform.python_version()}",
        "python_flint 0.9.0",
        f"arb_bits {ctx.prec}",
        f"max_cells {args.max_cells}",
        "SCOPE independent point evaluations; no interval-box promotion",
    ]
    for label, delta, t in points:
        smoke.DELTA, smoke.T = delta, t
        totals, cells, _ = smoke.run_lane(False, max_cells=args.max_cells)
        value = totals["nuD_main"].abs_upper()
        fraction = value / smoke.BUDGETS["nuD_main"]
        lines.append(
            f"point {label} delta {delta.str(24)} t {t.str(24)} "
            f"cells {cells} nuD_main {value.str(40)} "
            f"fraction {fraction.str(40)}"
        )
    text = "\n".join(lines) + "\n"
    if args.output:
        output = (ROOT / args.output).resolve()
        output.relative_to(ROOT)
        output.write_text(text, encoding="utf-8", newline="\n")
        print(f"WROTE {output.relative_to(ROOT)}")
    else:
        print(text, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
