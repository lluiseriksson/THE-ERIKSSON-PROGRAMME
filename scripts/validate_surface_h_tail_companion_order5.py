"""Validate order-five companion production/replay transcripts."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path

from flint import arb


ROOT = Path(__file__).resolve().parents[1]
DEPS = (
    "scripts/certify_surface_h_tail_companion_order5.py",
    "scripts/surface_remainder_companion_error_ordered.py",
    "scripts/surface_bessel_integral_remainder.py",
    "scripts/surface_remainder_delta0_companion_error.py",
)


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def parse(path: Path) -> None:
    lines = path.read_text(encoding="utf-8").splitlines()
    assert lines[0] == "H_TAIL COMPANION ORDER5 TRANSCRIPT"
    assert lines[-1] == "H_TAIL COMPANION ORDER5 PASS"
    assert any(line.startswith("PROVENANCE git_head ") for line in lines)
    assert any(line.startswith("PROVENANCE python ") for line in lines)
    assert "SCOPE candidate analytic input only; outer-tail, joint carrier, weighted S1'''/S2''' and global H_tail relay remain open" in lines
    deps = {line.split()[1]: line.split()[2] for line in lines
            if line.startswith("DEPENDENCY ")}
    assert deps == {relative: sha256(ROOT / relative) for relative in DEPS}
    ratio = arb(next(line.split(" ", 1)[1] for line in lines
                     if line.startswith("ORDER5_OVER_BUDGET ")))
    assert ratio < 1
    assert "ORDER5_COMPANION_ROUTE_PASSES_BUDGET_AUDIT" in lines


def main() -> int:
    import argparse
    parser = argparse.ArgumentParser()
    parser.add_argument("production", type=Path)
    parser.add_argument("replay", type=Path)
    args = parser.parse_args()
    production = (ROOT / args.production).resolve()
    replay = (ROOT / args.replay).resolve()
    production.relative_to(ROOT)
    replay.relative_to(ROOT)
    parse(production)
    parse(replay)
    assert production.read_bytes() == replay.read_bytes()
    print("ORDER5 COMPANION VALIDATION PASS", production.relative_to(ROOT))
    print("PRODUCTION/REPLAY BYTE EQUALITY PASS")
    print("CANDIDATE ONLY; NO H_TAIL/G2/G6 PROMOTION")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
