"""Validate the complete high-beta G5 lambda-two production/replay union."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

from flint import arb

import certify_surface_high_beta_g5_lambda2 as cert


ROOT = Path(__file__).resolve().parents[1]
COMMITTED_PRODUCTION = (
    ROOT / "scripts" / "surface_high_beta_g5_lambda2_production_20260727"
)
COMMITTED_REPLAY = (
    ROOT / "scripts" / "surface_high_beta_g5_lambda2_replay_20260727"
)


def sha256(relative: str) -> str:
    return hashlib.sha256((ROOT / relative).read_bytes()).hexdigest()


def parse(path: Path, unit: str) -> dict[str, object]:
    lines = path.read_text(encoding="utf-8").splitlines()
    if lines[0] != f"HIGH-BETA G5 LAMBDA2 UNIT {unit}":
        raise AssertionError(f"wrong header in {path}")
    heads = [
        line.split()[-1] for line in lines
        if line.startswith("PROVENANCE git_head ")
    ]
    if len(heads) != 1:
        raise AssertionError(f"wrong head count in {path}")
    dependencies = {}
    for line in lines:
        if line.startswith("DEPENDENCY "):
            _, relative, digest = line.split()
            dependencies[relative] = digest
    if set(dependencies) != set(cert.DEPENDENCIES):
        raise AssertionError(f"wrong dependency set in {path}")
    for relative, digest in dependencies.items():
        if sha256(relative) != digest:
            raise AssertionError(f"dependency drift {relative} in {path}")
    configs = [line for line in lines if line.startswith("CONFIG ")]
    if len(configs) != 1:
        raise AssertionError(f"wrong config count in {path}")
    required = (
        "delta_partition 0:9/1000:1/1000",
        "lambda_max 2",
        "near_exp exp(2)",
        "low_argument_z_ge_4",
    )
    if any(item not in configs[0] for item in required):
        raise AssertionError(f"wrong config in {path}")
    rows = [
        json.loads(line[4:]) for line in lines if line.startswith("ROW ")
    ]
    if len(rows) != 45:
        raise AssertionError(f"expected 45 rows in {path}, got {len(rows)}")
    terminal = [
        line for line in lines
        if line.startswith("CERTIFIED HIGH-BETA G5 LAMBDA2 UNIT ")
    ]
    if len(terminal) != 1 or f" {unit} 45 rows " not in terminal[0]:
        raise AssertionError(f"wrong terminal in {path}")
    return {
        "head": heads[0],
        "dependencies": dependencies,
        "config": configs[0],
        "rows": rows,
        "terminal": terminal[0],
    }


def validate(production_dir: Path, replay_dir: Path) -> dict[str, object]:
    expected_pairs = {
        (delta_index, lambda_index)
        for lambda_index in range(75, 100)
        for delta_index in range(9)
    }
    seen = set()
    heads = set()
    worst = None
    for unit in cert.unit_map():
        production = parse(production_dir / f"{unit}.txt", unit)
        replay = parse(replay_dir / f"{unit}.txt", unit)
        if production["rows"] != replay["rows"]:
            raise AssertionError(f"production/replay row mismatch in {unit}")
        if production["dependencies"] != replay["dependencies"]:
            raise AssertionError(f"production/replay dependency mismatch {unit}")
        if production["config"] != replay["config"]:
            raise AssertionError(f"production/replay config mismatch {unit}")
        heads.update((production["head"], replay["head"]))
        for row in production["rows"]:
            pair = (row["delta_index"], row["lambda_index"])
            if pair in seen:
                raise AssertionError(f"duplicate parameter cell {pair}")
            seen.add(pair)
            di, li = pair
            if row["delta_lo"] != f"{di}/1000":
                raise AssertionError(f"wrong delta_lo in {pair}")
            if row["delta_hi"] != f"{di + 1}/1000":
                raise AssertionError(f"wrong delta_hi in {pair}")
            if row["lambda_lo"] != f"{li}/50":
                raise AssertionError(f"wrong lambda_lo in {pair}")
            if row["lambda_hi"] != f"{li + 1}/50":
                raise AssertionError(f"wrong lambda_hi in {pair}")
            if not arb(row["families_lower"][3]) > 0:
                raise AssertionError(f"B0 is not positive in {pair}")
            if not arb(row["P0_lower"]) > 0:
                raise AssertionError(f"P0 is not positive in {pair}")
            h_lower = arb(row["H_lower"])
            if not h_lower > 0:
                raise AssertionError(f"H is not positive in {pair}")
            if worst is None or h_lower < worst[0]:
                worst = (h_lower, di, li)
    if seen != expected_pairs:
        missing = sorted(expected_pairs-seen)
        extra = sorted(seen-expected_pairs)
        raise AssertionError(f"union mismatch missing={missing} extra={extra}")
    if len(heads) != 1:
        raise AssertionError(f"mixed source heads {sorted(heads)}")
    return {
        "head": next(iter(heads)),
        "rows": len(seen),
        "worst_H_lower": worst[0].str(80),
        "worst_delta_index": worst[1],
        "worst_lambda_index": worst[2],
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "production_dir", type=Path, nargs="?",
        default=COMMITTED_PRODUCTION,
    )
    parser.add_argument(
        "replay_dir", type=Path, nargs="?",
        default=COMMITTED_REPLAY,
    )
    args = parser.parse_args()
    result = validate(args.production_dir, args.replay_dir)
    print("HIGH-BETA G5 LAMBDA2 UNION VALIDATION PASS")
    print(json.dumps(result, indent=2, sort_keys=True))
    print("SCOPE exact G5 strip only; no K2/K4/G2/G6 promotion")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
