"""Segmented, candidate-only runner for the registered delta-zero endpoint lane.

The frozen design contract is the 158 born t boxes from
``surface_remainder_delta0_series_cover_design`` and its grid ladder
``(96, 192)``.  This wrapper only makes the long campaign restartable; it does
not change the mathematical target or promote the endpoint lane.
"""

from __future__ import annotations

import argparse
import hashlib
from pathlib import Path
import platform
import subprocess

from flint import ctx

from surface_remainder_delta0_series_cover_design import (
    born_t_boxes, judge_box,
)


def provenance() -> dict[str, str]:
    path = Path(__file__).resolve()
    root = path.parents[1]
    try:
        head = subprocess.check_output(
            ["git", "-c", "safe.directory=*", "rev-parse", "HEAD"],
            cwd=root, text=True, stderr=subprocess.DEVNULL,
        ).strip()
    except Exception:
        head = "UNAVAILABLE"
    return {
        "script": str(path.relative_to(root)).replace("\\", "/"),
        "script_sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
        "git_head": head,
        "python": platform.python_version(),
        "arb_prec_bits": str(ctx.prec),
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--start", type=int, required=True)
    parser.add_argument("--stop", type=int, required=True,
                        help="exclusive born-box index")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    ctx.prec = 140
    boxes = list(born_t_boxes())
    if not 0 <= args.start < args.stop <= len(boxes):
        raise SystemExit(f"range must lie in [0,{len(boxes)}]")
    lines = []
    for key, value in provenance().items():
        lines.append(f"PROVENANCE {key}={value}")
    lines.append(f"CONFIG start={args.start} stop={args.stop} "
                 f"born_total={len(boxes)} grids=96,192 precision=140")
    for index in range(args.start, args.stop):
        lo, hi = boxes[index]
        grid, coefficient3, value_charge, margin = judge_box(lo, hi)
        lines.append(
            "ROW index=%d lo=%s hi=%s grid=%d Y3_abs=%s C_value=%s "
            "margin=%s margin_lower=%s margin_upper=%s" % (
                index, lo, hi, grid, coefficient3.str(30),
                value_charge.str(30), margin.str(30),
                margin.lower().str(30), margin.upper().str(30))
        )
        print(lines[-1], flush=True)
    lines.append("CANDIDATE_ENDPOINT_SEGMENT_PASS: nominal endpoint series "
                 "segment only; K2/G2/G6 remain open")
    text = "\n".join(lines) + "\n"
    if args.output:
        args.output.write_text(text, encoding="utf-8")
    print(lines[-1], flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
