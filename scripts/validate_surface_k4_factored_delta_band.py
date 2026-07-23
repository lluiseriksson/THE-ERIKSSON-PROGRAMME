"""Validator for the isolated factored-delta K4 smoke pair."""

from pathlib import Path
import argparse

ROOT = Path(__file__).resolve().parents[1]


def validate(path: Path) -> list[str]:
    lines = path.read_text(encoding="utf-8").splitlines()
    assert lines[0] == "SURFACE K4 FACTORED DELTA BAND SMOKE"
    assert "CANDIDATE FACTORED DELTA BAND PASS" in lines
    assert any(line.startswith("weight_formula ") for line in lines)
    rows = [line for line in lines if line.startswith("row ")]
    assert len(rows) == 7
    for row in rows:
        assert " total " in row and " fraction " in row
    assert lines[-1].startswith("SCOPE one low-z scaled core band;")
    return lines


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("production", type=Path)
    parser.add_argument("replay", type=Path)
    args = parser.parse_args()
    a = validate((ROOT / args.production).resolve())
    b = validate((ROOT / args.replay).resolve())
    assert a == b
    print("FACTORED DELTA BAND VALIDATION PASS; production/replay byte equality")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
