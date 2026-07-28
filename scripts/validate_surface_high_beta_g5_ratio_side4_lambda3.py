"""Validate the committed 450-cell ratio-side4 production/replay union."""

from __future__ import annotations

import hashlib
import json
from datetime import datetime
from pathlib import Path

from flint import arb

import certify_surface_high_beta_g5_ratio_side4_lambda3 as cert


ROOT = Path(__file__).resolve().parents[1]
PRODUCTION = (
    ROOT
    / "scripts"
    / "surface_high_beta_g5_ratio_side4_lambda3_production_20260728"
)
REPLAY = (
    ROOT
    / "scripts"
    / "surface_high_beta_g5_ratio_side4_lambda3_replay_20260728"
)
SOURCE_HEAD = "4a5e9a6d8e4cfdd07b1277a6a61172e23e3ba7be"
MANIFEST = (
    ROOT
    / "run-manifests"
    / "surface-high-beta-g5-ratio-side4-lambda3-20260728.json"
)


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def digest_lf(path: Path) -> str:
    return hashlib.sha256(path.read_bytes().replace(b"\r\n", b"\n")).hexdigest()


def digest_variants(path: Path) -> set[str]:
    raw = path.read_bytes()
    lf = raw.replace(b"\r\n", b"\n")
    crlf = lf.replace(b"\n", b"\r\n")
    return {
        hashlib.sha256(raw).hexdigest(),
        hashlib.sha256(lf).hexdigest(),
        hashlib.sha256(crlf).hexdigest(),
    }


def validate_driver_configuration() -> None:
    """Pin angular refinements omitted from the compact transcript CONFIG."""

    text = (
        ROOT / "scripts" / "certify_surface_high_beta_g5_ratio_side4_lambda3.py"
    ).read_text(encoding="utf-8")
    required = (
        "side=SIDE, qgrid=128, rgrid=16,\n"
        "            thetagrid=4, phigrid=4,",
        "delta, lam, 1, side=SIDE, qgrid=256, rgrid=32,\n"
        "                thetagrid=4, phigrid=1,",
        "delta, lam, 3, side=SIDE, qgrid=256, rgrid=32,\n"
        "                thetagrid=8, phigrid=1,",
        "delta, lam, 5, side=SIDE, qgrid=256, rgrid=32,\n"
        "                thetagrid=4, phigrid=1,",
        "delta, lam, 2, side=SIDE, qgrid=256, rgrid=32,\n"
        "                thetagrid=1,",
        "delta, lam, 4, side=SIDE, qgrid=256, rgrid=32,\n"
        "                thetagrid=8,",
    )
    for token in required:
        if token not in text:
            raise AssertionError("registered angular-grid configuration drift")


def validate_file(path: Path, unit: tuple[int, int]) -> list[dict]:
    lines = path.read_text(encoding="utf-8").splitlines()
    slug = cert.unit_slug(unit)
    if lines[0] != f"HIGH-BETA G5 RATIO SIDE4 LAMBDA3 UNIT {slug}":
        raise AssertionError(f"wrong unit header: {path}")
    if f"PROVENANCE git_head {SOURCE_HEAD}" not in lines:
        raise AssertionError(f"wrong source head: {path}")
    for relative in cert.DEPENDENCIES:
        recorded = {
            line.split()[2]
            for line in lines
            if line.startswith(f"DEPENDENCY {relative} ")
        }
        if len(recorded) != 1 or not recorded <= digest_variants(ROOT / relative):
            raise AssertionError(f"dependency drift in {path}: {relative}")
    config = (
        "CONFIG delta_partition 0:9/1000:1/1000 "
        f"lambda_unit {unit[0]}/50:{unit[1]}/50:1/50 "
        "lambda_max 3 side 4 near_exp exp(lambda_hi) "
        "coarse qgrid128 rgrid16 mixed qgrid256 rgrid32"
    )
    if config not in lines:
        raise AssertionError(f"wrong config: {path}")
    terminal = (
        "CERTIFIED HIGH-BETA G5 RATIO SIDE4 LAMBDA3 UNIT "
        f"{slug} 45 rows"
    )
    if not any(line.startswith(terminal) for line in lines):
        raise AssertionError(f"missing terminal pass: {path}")
    rows = [
        json.loads(line.removeprefix("ROW "))
        for line in lines
        if line.startswith("ROW ")
    ]
    if len(rows) != 45:
        raise AssertionError(f"wrong row count in {path}: {len(rows)}")
    for row in rows:
        lambda_index = row["lambda_index"]
        delta_index = row["delta_index"]
        expected_geometry = {
            "lambda_lo": f"{lambda_index}/50",
            "lambda_hi": f"{lambda_index + 1}/50",
            "delta_lo": f"{delta_index}/1000",
            "delta_hi": f"{delta_index + 1}/1000",
        }
        for field, expected in expected_geometry.items():
            if row.get(field) != expected:
                raise AssertionError(
                    f"wrong {field} in {path}: {row.get(field)!r}"
                )
        if row.get("resolution") not in {"coarse-ratio", "mixed-ratio"}:
            raise AssertionError(f"unknown resolution in {path}")
        b0_lower = arb(row["B0_lower"])
        b0_upper = arb(row["B0_upper"])
        ratio_lower = arb(row["Qratio_lower"])
        ratio_upper = arb(row["Qratio_upper"])
        if not (b0_lower > 0 and b0_upper >= b0_lower):
            raise AssertionError(f"invalid B0 enclosure in {path}")
        if not (ratio_lower > 0 and ratio_upper >= ratio_lower):
            raise AssertionError(f"invalid Qratio enclosure in {path}")
        budgets = row.get("tail_budgets", [])
        if len(budgets) != 5 or not all(arb(value) >= 0 for value in budgets):
            raise AssertionError(f"invalid tail budgets in {path}")
    return rows


def validate() -> dict[str, object]:
    validate_driver_configuration()
    all_rows = []
    aggregate = hashlib.sha256()
    for unit in cert.UNITS:
        name = cert.unit_slug(unit) + ".txt"
        production = PRODUCTION / name
        replay = REPLAY / name
        production_bytes = production.read_bytes()
        replay_bytes = replay.read_bytes()
        if production_bytes != replay_bytes:
            raise AssertionError(f"production/replay mismatch: {name}")
        aggregate.update(name.encode("ascii"))
        aggregate.update(b"\0")
        aggregate.update(production_bytes.replace(b"\r\n", b"\n"))
        rows = validate_file(production, unit)
        if rows != validate_file(replay, unit):
            raise AssertionError(f"parsed replay mismatch: {name}")
        all_rows.extend(rows)

    expected = [
        (lambda_index, delta_index)
        for lambda_index in range(100, 150)
        for delta_index in range(9)
    ]
    got = [
        (row["lambda_index"], row["delta_index"])
        for row in all_rows
    ]
    if got != expected:
        raise AssertionError("450-cell adjacency or ordering mismatch")
    worst_b0_row = min(all_rows, key=lambda row: arb(row["B0_lower"]))
    worst_ratio_row = min(
        all_rows, key=lambda row: arb(row["Qratio_lower"])
    )
    worst_b0 = arb(worst_b0_row["B0_lower"])
    worst_ratio = arb(worst_ratio_row["Qratio_lower"])
    if not worst_b0 > 0:
        raise AssertionError("B0 lower endpoint is not positive")
    if not worst_ratio > 0:
        raise AssertionError("Qratio lower endpoint is not positive")
    resolutions: dict[str, int] = {}
    for row in all_rows:
        key = row["resolution"]
        resolutions[key] = resolutions.get(key, 0) + 1
    aggregate_sha256 = aggregate.hexdigest()

    manifest = json.loads(MANIFEST.read_text(encoding="utf-8"))
    assert manifest["schema_version"] == 1
    assert manifest["status"] == "certified"
    assert manifest["source_head"] == SOURCE_HEAD
    assert manifest["units"] == 10
    assert manifest["rows"] == 450
    assert manifest["replay_launched_after_production_terminal"] is True
    assert manifest["production"]["stderr_bytes"] == 0
    assert manifest["replay"]["stderr_bytes"] == 0
    production_started = datetime.fromisoformat(
        manifest["production"]["started_utc"].replace("Z", "+00:00")
    )
    production_finished = datetime.fromisoformat(
        manifest["production"]["finished_utc"].replace("Z", "+00:00")
    )
    replay_started = datetime.fromisoformat(
        manifest["replay"]["started_utc"].replace("Z", "+00:00")
    )
    replay_finished = datetime.fromisoformat(
        manifest["replay"]["finished_utc"].replace("Z", "+00:00")
    )
    assert production_started < production_finished < replay_started < replay_finished
    assert [item["path"] for item in manifest["dependencies"]] == list(
        cert.DEPENDENCIES
    )
    for item in manifest["dependencies"]:
        assert item["sha256"] in digest_variants(ROOT / item["path"])
        assert item["sha256_lf"] == digest_lf(ROOT / item["path"])
    for key, directory in (("production", PRODUCTION), ("replay", REPLAY)):
        outputs = manifest[key]["outputs"]
        expected_paths = [
            str(
                (directory / (cert.unit_slug(unit) + ".txt")).relative_to(ROOT)
            ).replace("\\", "/")
            for unit in cert.UNITS
        ]
        assert [item["path"] for item in outputs] == expected_paths
        for item in outputs:
            path = ROOT / item["path"]
            assert item["sha256"] in digest_variants(path)
            assert item["sha256_lf"] == digest_lf(path)
    assert manifest["aggregate_sha256"] == aggregate_sha256
    return {
        "sha256": aggregate_sha256,
        "rows": len(all_rows),
        "worst_b0": worst_b0,
        "worst_ratio": worst_ratio,
        "worst_b0_cell": (
            worst_b0_row["lambda_index"],
            worst_b0_row["delta_index"],
        ),
        "worst_ratio_cell": (
            worst_ratio_row["lambda_index"],
            worst_ratio_row["delta_index"],
        ),
        "resolutions": resolutions,
    }


def main() -> int:
    result = validate()
    print("HIGH-BETA G5 RATIO SIDE4 LAMBDA3 VALIDATION PASS")
    print("aggregate_sha256", result["sha256"])
    print("rows", result["rows"])
    print("worst_B0_lower", result["worst_b0"].str(50))
    print("worst_B0_cell", result["worst_b0_cell"])
    print("worst_Qratio_lower", result["worst_ratio"].str(50))
    print("worst_Qratio_cell", result["worst_ratio_cell"])
    print("resolutions", json.dumps(result["resolutions"], sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
