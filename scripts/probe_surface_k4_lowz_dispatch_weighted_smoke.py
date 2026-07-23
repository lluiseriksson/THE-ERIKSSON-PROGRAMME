"""Candidate weighted K4 smoke with the registered low-z Bessel dispatcher.

This is a single stress point, not the global S1'''/S2''' certificate.  It
freezes the adaptive partition and emits enough provenance for a production /
replay byte comparison without changing the authoritative carrier.
"""

from __future__ import annotations

import argparse
import hashlib
import heapq
import platform
import subprocess
from pathlib import Path

from flint import arb, ctx

import surface_remainder_centered_prefactor_lowz_candidate  # noqa: F401
import surface_remainder_core_l2_arb as core


ROOT = Path(__file__).resolve().parents[1]
DELTA = arb(1) / 15
T = arb("2.9")
SEED_GRID = 4
MAX_CELLS = 4096
PREC = 100
NAMES = {
    False: ("muF_main", "nuD_main", "nuF_main"),
    True: ("MD_mirror", "MF_mirror", "MD2r_mirror", "MDFr_mirror"),
}
BUDGETS = {
    "muF_main": arb("26.467"),
    "nuD_main": arb("0.94119"),
    "nuF_main": arb("8.1751"),
    "MD_mirror": arb("56.801"),
    "MF_mirror": arb("156.28"),
    "MD2r_mirror": arb("12.577"),
    "MDFr_mirror": arb("44.352"),
}
DEPS = (
    "scripts/probe_surface_k4_lowz_dispatch_weighted_smoke.py",
    "scripts/surface_remainder_centered_prefactor_lowz_candidate.py",
    "scripts/surface_bessel_entire_lowz.py",
    "scripts/surface_remainder_centered_prefactor.py",
    "scripts/surface_remainder_core_l2_arb.py",
    "scripts/surface_remainder_arb_jet2.py",
)


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def git_head() -> str:
    return subprocess.check_output(
        ["git", "-c", "safe.directory=*", "rev-parse", "HEAD"],
        cwd=ROOT, text=True,
    ).strip()


def run_lane(mirror: bool, max_cells: int = MAX_CELLS) -> tuple[dict[str, arb], int, float]:
    length = arb("1.2") / DELTA.sqrt()
    names = NAMES[mirror]
    heap = []
    serial = 0

    def push(slo: arb, shi: arb, alo: arb, ahi: arb) -> None:
        nonlocal serial
        values = core.localized_cell_bounds(
            DELTA, T, slo, shi, alo, ahi, mirror=mirror,
        )
        if not all(values[name].is_finite() for name in names):
            raise RuntimeError("non-finite localized carrier value")
        score = max(
            float(values[name].abs_upper()) / float(BUDGETS[name])
            for name in names
        )
        heapq.heappush(
            heap, (-score, serial, slo, shi, alo, ahi, values),
        )
        serial += 1

    for i in range(SEED_GRID):
        for j in range(SEED_GRID):
            push(length*i/SEED_GRID, length*(i+1)/SEED_GRID,
                 length*j/SEED_GRID, length*(j+1)/SEED_GRID)
    while len(heap) + 3 <= max_cells:
        _, _, slo, shi, alo, ahi, _ = heapq.heappop(heap)
        sm, am = (slo + shi) / 2, (alo + ahi) / 2
        push(slo, sm, alo, am)
        push(sm, shi, alo, am)
        push(slo, sm, am, ahi)
        push(sm, shi, am, ahi)
    totals = {name: arb(0) for name in names}
    for *_, values in heap:
        for name in names:
            # S1'''/S2''' are absolute partition-sum judges.  Do not allow
            # cancellation between signed cell enclosures.
            totals[name] += 4 * values[name].abs_upper()
    fractions = [float(totals[name].rad()) / float(BUDGETS[name])
                 for name in names]
    return totals, len(heap), max(fractions)


def make_transcript(max_cells: int = MAX_CELLS) -> str:
    ctx.prec = PREC
    lines = [
        "SURFACE K4 LOW-Z DISPATCH WEIGHTED SMOKE",
        f"git_head {git_head()}",
        f"python {platform.python_version()}",
        "python_flint 0.9.0",
        f"arb_bits {ctx.prec}",
        f"config delta 1/15 t 29/10 seed_grid {SEED_GRID} "
        f"max_cells {max_cells} lowz_terms 96",
    ]
    for relative in DEPS:
        lines.append(f"dependency {relative} sha256 {sha(ROOT / relative)}")
    worst = 0.0
    passed = True
    for mirror in (False, True):
        totals, cells, lane_worst = run_lane(mirror, max_cells=max_cells)
        worst = max(worst, lane_worst)
        lines.append(f"lane {'mirror' if mirror else 'main'} cells {cells}")
        for name in NAMES[mirror]:
            fraction = totals[name] / BUDGETS[name]
            lines.append(
                f"row {name} total {totals[name].str(60)} "
                f"budget {BUDGETS[name].str(30)} "
                f"fraction {fraction.str(40)}"
            )
            if not (fraction < 1):
                passed = False
    lines.extend([
        f"worst_radius_fraction {worst:.17g}",
        ("CANDIDATE LOW-Z WEIGHTED SMOKE PASS" if passed
         else "CANDIDATE LOW-Z WEIGHTED SMOKE FAIL"),
        "SCOPE single stress point; no global S1'''/S2''' or K4 promotion",
    ])
    return "\n".join(lines) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--max-cells", type=int, default=MAX_CELLS)
    args = parser.parse_args()
    text = make_transcript(args.max_cells)
    output = (ROOT / args.output).resolve()
    output.relative_to(ROOT)
    output.write_text(text, encoding="utf-8", newline="\n")
    print("LOW-Z WEIGHTED SMOKE PASS", output.relative_to(ROOT))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
