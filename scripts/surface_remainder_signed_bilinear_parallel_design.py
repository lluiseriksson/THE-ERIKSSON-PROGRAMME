"""Parallel design campaign for the signed-bilinear K2 endpoint route.

This is intentionally not a production judge.  It uses the preregistered
charged bilinear formula and frozen t boxes, but emits only candidate/design
evidence.  The process pool is used solely to make the exploratory resolution
study tractable; no gate, manifest, or manuscript slot is changed here.
"""

from __future__ import annotations

import argparse
import json
from concurrent.futures import ProcessPoolExecutor
from fractions import Fraction
from pathlib import Path

from flint import ctx

from surface_remainder_signed_bilinear_cover_design import (
    born_t_boxes,
    judge_box,
)


def _judge(task: tuple[int, Fraction, Fraction, int]) -> dict:
    index, lo, hi, grid = task
    ctx.prec = 140
    row = judge_box(lo, hi, grid)
    row["index"] = index
    return row


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--grid", type=int, default=96)
    parser.add_argument("--workers", type=int, default=8)
    parser.add_argument("--limit", type=int)
    parser.add_argument(
        "--output",
        default="scripts/surface_remainder_signed_bilinear_parallel_design.json",
    )
    args = parser.parse_args()
    boxes = list(born_t_boxes())
    if args.limit is not None:
        boxes = boxes[: args.limit]
    tasks = [(i, lo, hi, args.grid) for i, (lo, hi) in enumerate(boxes)]
    with ProcessPoolExecutor(max_workers=args.workers) as pool:
        rows = list(pool.map(_judge, tasks))
    rows.sort(key=lambda row: row["index"])
    payload = {
        "grid": args.grid,
        "workers": args.workers,
        "rows": rows,
        "scope": "design-only; no K2 promotion",
        "passes": sum(bool(row["pass"]) for row in rows),
    }
    path = Path(args.output)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    print(
        "SIGNED-BILINEAR PARALLEL DESIGN rows=%d passes=%d grid=%d"
        % (len(rows), payload["passes"], args.grid),
        flush=True,
    )
    for row in rows:
        print(
            "index=%d t=[%s,%s] y3=%s margin=%s %s"
            % (
                row["index"],
                row["lo"],
                row["hi"],
                row["y3_abs"],
                row["margin"],
                "PASS" if row["pass"] else "FAIL",
            ),
            flush=True,
        )


if __name__ == "__main__":
    main()
