"""Parallel candidate runner for the preregistered signed-bilinear K2 route.

This preserves the frozen grid and exact born boxes while removing the
sequential runtime bottleneck.  It remains candidate evidence: it emits no
manifest and cannot promote K2 or G2.
"""

from __future__ import annotations

import hashlib
import importlib.metadata
import subprocess
import sys
from concurrent.futures import ProcessPoolExecutor
from pathlib import Path

from flint import ctx

from surface_remainder_signed_bilinear_cover_design import born_t_boxes, judge_box


ROOT = Path(__file__).resolve().parents[1]
GRID = 48
WORKERS = 8
SCRIPT_NAMES = (
    "run_surface_remainder_signed_bilinear_parallel_candidate.py",
    "surface_remainder_signed_bilinear_cover_design.py",
    "probe_surface_remainder_signed_bilinear_with_tails.py",
    "probe_surface_remainder_signed_bilinear_series.py",
    "surface_remainder_delta0_series_design.py",
    "surface_remainder_delta0_derivative_tail.py",
    "surface_remainder_delta0_companion_error.py",
    "surface_remainder_s2_direct_judge.py",
)


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _git_head() -> str:
    return subprocess.check_output(
        ["git", "-c", "safe.directory=*", "rev-parse", "HEAD"],
        cwd=ROOT, text=True,
    ).strip()


def _judge(task: tuple[int, object, object]) -> dict:
    index, lo, hi = task
    ctx.prec = 140
    row = judge_box(lo, hi, GRID)
    row["index"] = index
    return row


def run(output: Path) -> int:
    ctx.prec = 140
    boxes = list(born_t_boxes())
    rows = []
    with ProcessPoolExecutor(max_workers=WORKERS) as pool:
        for row in pool.map(_judge, [(i, lo, hi) for i, (lo, hi) in enumerate(boxes)]):
            rows.append(row)
    rows.sort(key=lambda row: row["index"])
    lines = [
        "SIGNED-BILINEAR K2 CANDIDATE PRODUCTION",
        "SCOPE=delta:[0,1/1000], t:[0,pi_hi], 158 boxes, grid=48",
        f"PYTHON={sys.version.replace(chr(10), ' ')}",
        "FLINT=" + importlib.metadata.version("python-flint"),
        "GIT_HEAD=" + _git_head(),
        f"WORKERS={WORKERS}",
    ]
    for name in SCRIPT_NAMES:
        lines.append(f"SHA256 scripts/{name}=" + _sha256(ROOT / "scripts" / name))
    for row in rows:
        lines.append(
            "ROW index=%d lo=%s hi=%s grid=%d y3=%s kd=%s value=%s margin=%s verdict=%s"
            % (row["index"], row["lo"], row["hi"], GRID, row["y3_abs"],
               row["kd_lower"], row["value_charge"], row["margin"],
               "PASS" if row["pass"] else "FAIL")
        )
    passed = len(rows) == 158 and all(row["pass"] for row in rows)
    lines += [f"ROWS={len(rows)}",
              "CANDIDATE_PRODUCTION_%s" % ("PASS" if passed else "FAIL"),
              "NO_G2_PROMOTION"]
    output.write_text("\n".join(lines) + "\n", encoding="utf-8")
    print("\n".join(lines))
    return 0 if passed else 1


if __name__ == "__main__":
    target = Path(sys.argv[1]) if len(sys.argv) > 1 else ROOT / "scripts" / "surface_remainder_signed_bilinear_parallel_candidate_transcript.txt"
    raise SystemExit(run(target))
