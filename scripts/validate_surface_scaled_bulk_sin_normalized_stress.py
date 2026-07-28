"""Validate the fixed sine-normalized stress transcript and its replay."""

from fractions import Fraction
import argparse
import hashlib
from pathlib import Path

from flint import arb


ROOT = Path(__file__).resolve().parents[1]


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate(path: Path) -> None:
    lines = path.read_text(encoding="utf-8").splitlines()
    assert lines[0] == "SIN-NORMALIZED STRESS TRANSCRIPT"
    config = next(line for line in lines if line.startswith("config "))
    for token in (
        "CWIN 3/2",
        "beta_order 40",
        "t_order 45",
        "prec 220",
        "common_scale J1^4",
        "t_scale sin(t)",
    ):
        assert token in config, (token, config)
    beta = next(line for line in lines if line.startswith("beta_domain ")).split()
    assert Fraction(beta[1]) == Fraction(1629, 16)
    assert Fraction(beta[2]) == Fraction(3259, 32)
    t = next(line for line in lines if line.startswith("t_domain ")).split()
    assert Fraction(t[1]) == Fraction(7817, 2500)
    assert Fraction(t[2]) == Fraction(156343, 50000)
    upper = arb(next(line for line in lines if line.startswith("W_upper "))[8:])
    lower = arb(next(line for line in lines if line.startswith("W_lower "))[8:])
    assert upper < 0
    assert lower < 0
    assert "STRICT_UPPER_NEGATIVE PASS" in lines
    assert "SCOPE candidate single stress box only; no G2/G6 promotion" in lines
    for line in lines:
        if line.startswith("dependency "):
            _, rel, _, digest = line.split()
            dep = (ROOT / rel).resolve()
            dep.relative_to(ROOT)
            assert sha256(dep) == digest, rel


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("production", type=Path)
    parser.add_argument("replay", type=Path)
    args = parser.parse_args()
    production = (ROOT / args.production).resolve()
    replay = (ROOT / args.replay).resolve()
    production.relative_to(ROOT)
    replay.relative_to(ROOT)
    assert production.read_bytes() == replay.read_bytes()
    validate(production)
    validate(replay)
    print("SIN-NORMALIZED STRESS VALIDATION PASS")
    print("CANDIDATE ONLY; NO G2/G6 PROMOTION")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
