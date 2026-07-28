"""Independent parser/coverage validator for the signed-bilinear candidate."""

from __future__ import annotations

import hashlib
import json
import re
from decimal import Decimal, getcontext
from pathlib import Path

from run_record_archive import frozen_record_path

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = frozen_record_path(
    "surface-remainder-signed-bilinear-endpoint-candidate-20260722.json"
)
PI_UP = Decimal("3.1415926535897932384626433832795028841971693993751")
getcontext().prec = 80
ROW = re.compile(
    r"^ROW \[([^,]+),([^\]]+)\] grid=(\d+) .*?margin_lower=\[([0-9.eE+-]+) "
)


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def endpoint(text: str) -> Decimal:
    if "/" in text:
        numerator, denominator = text.split("/", 1)
        return Decimal(numerator) / Decimal(denominator)
    return Decimal(text)


def parse(path: Path):
    lines = path.read_text(encoding="utf-8").splitlines()
    assert lines[0] == "SIGNED BILINEAR K2 ENDPOINT CANDIDATE"
    assert lines[-2] == "CANDIDATE PASS; signed cancellation and order-five companion only"
    assert lines[-1] == "SCOPE no K2/G2/G6/S1'''/S2''' promotion"
    assert any(line.startswith("PROVENANCE git_head ") for line in lines)
    config = next(line for line in lines if line.startswith("CONFIG "))
    assert config == "CONFIG delta=[0,1/1000] grid=48 order5_companion=true"
    rows = []
    for line in lines:
        match = ROW.match(line)
        if match:
            rows.append((endpoint(match.group(1)), endpoint(match.group(2)),
                          int(match.group(3)), Decimal(match.group(4))))
    assert len(rows) == 158, len(rows)
    cursor = Decimal("0")
    for lo, hi, grid, margin in rows:
        assert lo == cursor, (lo, cursor)
        assert hi > lo and hi-lo <= Decimal("0.02")
        assert grid == 48
        assert margin > 0
        cursor = hi
    assert cursor == PI_UP
    coverage = next(line for line in lines if line.startswith("COVERAGE "))
    assert coverage == "COVERAGE boxes=158 passed=158"
    worst = next(line for line in lines if line.startswith("WORST_MARGIN_LOWER "))
    assert Decimal(worst.split("[", 1)[1].split(" ", 1)[0]) > 0
    return {"rows": len(rows), "sha256": sha256(path)}


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
    p = parse(production)
    r = parse(replay)
    assert production.read_bytes() == replay.read_bytes()
    manifest = json.loads(MANIFEST.read_text(encoding="utf-8"))
    assert manifest["status"] == "candidate_only"
    assert manifest["validator_result"]["rows"] == 158
    assert manifest["validator_result"]["production_replay_byte_identical"] is True
    paths = [manifest["provenance"]["driver"]["path"],
             manifest["provenance"]["validator"]["path"]]
    paths += [item["path"] for item in manifest["inputs"]]
    paths += [item["path"] for item in manifest["outputs"]]
    expected = {manifest["provenance"]["driver"]["path"]:
                manifest["provenance"]["driver"]["sha256"],
                manifest["provenance"]["validator"]["path"]:
                manifest["provenance"]["validator"]["sha256"]}
    expected.update({item["path"]: item["sha256"] for item in manifest["inputs"]})
    expected.update({item["path"]: item["sha256"] for item in manifest["outputs"]})
    for rel in paths:
        assert sha256(ROOT / rel) == expected[rel], rel
    print("SIGNED BILINEAR ENDPOINT CANDIDATE VALIDATION PASS")
    print(f"ROWS {p['rows']} SHA256 {p['sha256']}")
    print("PRODUCTION/REPLAY BYTE EQUALITY PASS")
    print("CANDIDATE ONLY; NO K2/G2/G6/S1'''/S2''' PROMOTION")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
