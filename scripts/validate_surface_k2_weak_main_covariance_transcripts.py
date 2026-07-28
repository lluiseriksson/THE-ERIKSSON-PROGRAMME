"""Validate the frozen near/far weak-main covariance transcript pairs."""

from __future__ import annotations

import ast
import argparse
from decimal import Decimal, getcontext
from fractions import Fraction
import hashlib
from pathlib import Path
import re


ROOT = Path(__file__).resolve().parents[1]
EXPECTED_HEAD = "150f439ba30ac1ee915fc92e93ec0b4d708f4349"
LANES = {
    "near": {
        "stem": "surface-k2-weak-main-covariance",
        "t_min": Fraction(21, 10),
        "t_max": Fraction(31_415_927, 10_000_000),
        "grids": (24, 48),
        "dependencies": 9,
    },
    "far": {
        "stem": "surface-k2-weak-main-covariance-far",
        "t_min": Fraction(0),
        "t_max": Fraction(21, 10),
        "grids": (24, 48, 96),
        "dependencies": 10,
    },
}
DELTA_MAX = Fraction(9, 1000)
T_MIN = Fraction(21, 10)
PI_UP = Fraction(31_415_927, 10_000_000)
DELTA_BOXES = 18
T_BOXES = 32
TARGET = Decimal(-1)/Decimal(20)
NUMBER = r"[+-]?[0-9]+(?:\.[0-9]+)?(?:e[+-]?[0-9]+)?"
BALL = re.compile(
    rf"^\[({NUMBER}) \+/- ({NUMBER})\]$",
    re.IGNORECASE,
)


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest().upper()


def endpoints(text: str) -> tuple[Decimal, Decimal]:
    """Return decimal endpoints from an Arb ``str`` ball or exact decimal."""

    match = BALL.fullmatch(text)
    if match is not None:
        midpoint = Decimal(match.group(1))
        radius = Decimal(match.group(2))
        if radius < 0:
            raise AssertionError(f"negative radius: {text!r}")
        return midpoint-radius, midpoint+radius
    exact = Decimal(text)
    return exact, exact


def split_ball_after(prefix: str, line: str, suffix: str) -> str:
    if not line.startswith(prefix) or not line.endswith(suffix):
        raise AssertionError(f"malformed line: {line!r}")
    return line[len(prefix):len(line)-len(suffix)]


def artifact_paths(lane_name: str) -> tuple[Path, Path, Path, Path]:
    stem = LANES[lane_name]["stem"]
    production = ROOT/"outputs"/f"{stem}-production-20260728.txt"
    replay = ROOT/"outputs"/f"{stem}-replay-20260728.txt"
    production_stderr = ROOT/"outputs"/f"{stem}-production-20260728.stderr.txt"
    replay_stderr = ROOT/"outputs"/f"{stem}-replay-20260728.stderr.txt"
    return production, replay, production_stderr, replay_stderr


def validate(lane_name: str = "near") -> dict[str, object]:
    getcontext().prec = 120
    lane = LANES[lane_name]
    production, replay, production_stderr, replay_stderr = artifact_paths(
        lane_name
    )
    if production.read_bytes() != replay.read_bytes():
        raise AssertionError("weak-main production/replay byte mismatch")
    if production_stderr.read_bytes() or replay_stderr.read_bytes():
        raise AssertionError("weak-main stderr is not empty")
    payload = production.read_bytes()
    lines = payload.decode("utf-8").splitlines()
    if not lines or lines[0] != f"PROVENANCE git_head {EXPECTED_HEAD}":
        raise AssertionError("unexpected or missing frozen head")
    python_line = next(
        line for line in lines if line.startswith("PROVENANCE python ")
    )
    if not python_line.startswith("PROVENANCE python 3.12."):
        raise AssertionError(f"unexpected Python: {python_line}")
    if "PROVENANCE python_flint 0.9.0" not in lines:
        raise AssertionError("python-flint 0.9.0 provenance missing")
    if "PROVENANCE arb_bits 180" not in lines:
        raise AssertionError("180-bit Arb provenance missing")
    if "PROVENANCE workers 12" not in lines:
        raise AssertionError("12-worker provenance missing")

    dependency_lines = [
        line.split() for line in lines if line.startswith("DEPENDENCY ")
    ]
    if len(dependency_lines) != lane["dependencies"]:
        raise AssertionError(
            f"expected {lane['dependencies']} dependency hashes, "
            f"found {len(dependency_lines)}"
        )
    for _, relative, recorded in dependency_lines:
        actual = sha256(ROOT/relative)
        if recorded != actual:
            raise AssertionError(
                f"dependency drift {relative}: {recorded} != {actual}"
            )

    if (
        f"WEAK MAIN TRUE-COMPANION COVARIANCE PASS {lane_name}"
        not in lines
    ):
        raise AssertionError("terminal certificate PASS line missing")
    grids_text = ",".join(str(grid) for grid in lane["grids"])
    expected_config = (
        f"CONFIG lane={lane_name} delta=0:9/1000:18 "
        f"t={lane['t_min']}:{lane['t_max']}:32 "
        f"side=12 grids={grids_text} companion_order=4 z0=20 workers=12"
    )
    if expected_config not in lines:
        raise AssertionError("frozen configuration line missing")

    rows = [line for line in lines if line.startswith("ROW ")]
    if len(rows) != DELTA_BOXES*T_BOXES:
        raise AssertionError(f"expected 576 rows, found {len(rows)}")
    delta_width = DELTA_MAX/DELTA_BOXES
    t_width = (lane["t_max"]-lane["t_min"])/T_BOXES
    grid_counts = {grid: 0 for grid in lane["grids"]}
    worst_lower = Decimal(1)
    for ordinal, line in enumerate(rows):
        # Arb balls contain spaces around "+/-"; reconstruct by markers rather
        # than relying on whitespace splitting.
        match = re.fullmatch(
            r"ROW (\d+) (\d+) (\S+) (\S+) grid (24|48) "
            r"KD (.+) XMAIN (.+)",
            line,
        )
        if match is None:
            raise AssertionError(f"malformed ROW: {line!r}")
        di = int(match.group(1))
        ti = int(match.group(2))
        if (di, ti) != divmod(ordinal, T_BOXES):
            raise AssertionError(f"row order mismatch at {ordinal}: {(di, ti)}")
        expected_delta = (
            f"{delta_width*di}:{delta_width*(di+1)}"
        )
        expected_t = (
            f"{lane['t_min']+t_width*ti}:"
            f"{lane['t_min']+t_width*(ti+1)}"
        )
        if match.group(3) != expected_delta or match.group(4) != expected_t:
            raise AssertionError(f"partition mismatch: {line!r}")
        grid = int(match.group(5))
        grid_counts[grid] += 1
        kd_lower, _ = endpoints(match.group(6))
        xmain_lower, _ = endpoints(match.group(7))
        if not kd_lower > 0:
            raise AssertionError(f"nonpositive printed KD lower: {line!r}")
        if not xmain_lower > TARGET:
            raise AssertionError(f"weak-main target not strict: {line!r}")
        worst_lower = min(worst_lower, xmain_lower)

    counts_line = next(
        line for line in lines if line.startswith("GRID_COUNTS ")
    )
    recorded_counts = ast.literal_eval(
        counts_line[len("GRID_COUNTS "):]
    )
    if recorded_counts != grid_counts or sum(grid_counts.values()) != 576:
        raise AssertionError((recorded_counts, grid_counts))
    if not any(
        line.startswith("WORST_LOWER ") and line.endswith("> -1/20")
        for line in lines
    ):
        raise AssertionError("terminal worst-lower line missing")
    if lines[-1] != (
        "SCOPE weak X_main premise only; "
        "terminal union and manuscript remain open"
    ):
        raise AssertionError("terminal scope line mismatch")
    return {
        "lane": lane_name,
        "sha256": hashlib.sha256(payload).hexdigest().upper(),
        "rows": len(rows),
        "grid_counts": grid_counts,
        "worst_printed_lower": worst_lower,
        "dependencies": len(dependency_lines),
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--lane", choices=tuple(LANES), default="near")
    args = parser.parse_args()
    result = validate(args.lane)
    print("WEAK MAIN COVARIANCE TRANSCRIPT VALIDATION PASS")
    for key, value in result.items():
        print(key, value)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
