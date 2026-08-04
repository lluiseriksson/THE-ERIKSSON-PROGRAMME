"""Validate one post-1635 terminal rescue-300 transcript pair."""

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
    assert lines[0] == "SCALED BULK SIGN ROW POST1635 TERMINAL RESCUE300"
    assert "SCOPE terminal direct-sign post1635 gap; no H_tail promotion" in lines
    config = next(x for x in lines if x.startswith("config "))
    for token in ("CWIN 3/2", "beta_order 40", "t_order 50", "min_dt 1/100000", "prec 300"):
        assert token in config
    beta = next(x.split() for x in lines if x.startswith("beta_domain "))
    assert (Fraction(beta[1]), Fraction(beta[2])) == (lo, hi)
    tdom = next(x.split() for x in lines if x.startswith("t_domain "))
    cursor, rows = Fraction(tdom[1]), 0
    for line in lines:
        if not line.startswith("trow "):
            continue
        head, upper = line.split(" upper ", 1)
        _, index, left, right = head.split()
        left, right = Fraction(left), Fraction(right)
        assert int(index) == rows and left == cursor and right > left
        assert arb(upper) < 0
        cursor, rows = right, rows + 1
    assert rows and cursor == Fraction(tdom[2])
    for line in lines:
        if line.startswith("dependency "):
            fields = line.split()
            assert sha(ROOT / fields[1]) == fields[3]
    return rows


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--production", type=Path, required=True)
    parser.add_argument("--replay", type=Path, required=True)
    parser.add_argument("--lo", required=True)
    parser.add_argument("--hi", required=True)
    args = parser.parse_args()
    ctx.prec = 300
    production, replay = ROOT / args.production, ROOT / args.replay
    assert production.read_bytes() == replay.read_bytes()
    rows = validate(production, Fraction(args.lo), Fraction(args.hi))
    print("POST1635 TERMINAL RESCUE300 VALIDATION PASS", args.lo, args.hi,
          "rows", rows, "sha256", sha(production))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
