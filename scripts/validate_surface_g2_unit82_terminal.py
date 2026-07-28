"""Provenance-strict validator for the terminal unit-82 direct-sign slices."""

from __future__ import annotations

import argparse
import hashlib
from fractions import Fraction
from pathlib import Path

from flint import arb, ctx

ROOT = Path(__file__).resolve().parents[1]


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate(path: Path, lo: Fraction, hi: Fraction) -> int:
    lines = path.read_text(encoding="utf-8").splitlines()
    assert lines[0].startswith("SCALED BULK SIGN ROW UNIT82 TERMINAL ORDER30")
    assert any(line.startswith("SCOPE terminal direct-sign unit82") for line in lines)
    beta = next(line.split() for line in lines if line.startswith("beta_domain "))
    assert (Fraction(beta[1]), Fraction(beta[2])) == (lo, hi)
    t_domain = next(line.split() for line in lines if line.startswith("t_domain "))
    cursor = Fraction(t_domain[1])
    rows = []
    for line in lines:
        if not line.startswith("trow "):
            continue
        head, upper_text = line.split(" upper ", 1)
        _, index, left, right = head.split()
        left, right = Fraction(left), Fraction(right)
        upper = arb(upper_text)
        assert int(index) == len(rows)
        assert left == cursor and right > left and upper < 0
        rows.append((left, right))
        cursor = right
    assert rows and cursor == Fraction(t_domain[2])
    recorded = {
        line.split()[1]: line.split()[3]
        for line in lines if line.startswith("dependency ")
    }
    for relative, digest in recorded.items():
        assert sha(ROOT / relative) == digest
    return len(rows)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--production", type=Path, required=True)
    parser.add_argument("--replay", type=Path, required=True)
    parser.add_argument("--lo", required=True)
    parser.add_argument("--hi", required=True)
    args = parser.parse_args()
    ctx.prec = 240
    production = ROOT / args.production
    replay = ROOT / args.replay
    assert production.read_bytes() == replay.read_bytes()
    rows = validate(production, Fraction(args.lo), Fraction(args.hi))
    print("UNIT82 TERMINAL VALIDATION PASS", args.lo, args.hi,
          "rows", rows, "sha256", sha(production))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
