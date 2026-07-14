"""Validate all authoritative ninth-birth hybrid regular-K2 units."""

import hashlib
import json
from pathlib import Path

from flint import arb

import certify_surface_remainder_delta0_r4_extension_009_hybrid as cert
import surface_remainder_delta0_r4_extension_009_hybrid_contract as hybrid


ROOT = Path(__file__).resolve().parents[1]


def transcript_path(unit):
    return ROOT / "scripts" / (
        "certify_surface_remainder_delta0_r4_extension_009_hybrid_"
        f"{unit.slug}.txt"
    )


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate():
    expected_hashes = {
        relative: sha256(ROOT / relative) for relative in cert.DEPENDENCIES
    }
    units = hybrid.regular_units()
    rows, heads = {}, set()
    for unit in units:
        path = transcript_path(unit)
        lines = path.read_text(encoding="utf-8").splitlines()
        if any("CERTIFICATE FAIL" in line for line in lines):
            raise AssertionError(f"failure marker: {unit.slug}")
        head_lines = [line for line in lines
                      if line.startswith("PROVENANCE git_head ")]
        if len(head_lines) != 1:
            raise AssertionError(f"provenance head: {unit.slug}")
        heads.add(head_lines[0].split()[-1])
        dependencies = {
            line.split()[1]: line.split()[2] for line in lines
            if line.startswith("DEPENDENCY ")
        }
        if dependencies != expected_hashes:
            raise AssertionError(f"dependency mismatch: {unit.slug}")
        configs = [line for line in lines if line.startswith("CONFIG ")]
        if len(configs) != 1 or (
            "delta_birth 1/125:9/1000" not in configs[0]
            or "regular_t 0:313/100" not in configs[0]
            or "moving_edge_C 3/2" not in configs[0]
            or "physical_inner 1181/1000" not in configs[0]
            or "band_radius 62/5" not in configs[0]
            or f"unit {unit.slug}" not in configs[0]
        ):
            raise AssertionError(f"configuration mismatch: {unit.slug}")
        terminal = "CERTIFIED UNIT regular K2 r4 hybrid009 " + unit.slug
        if sum(line.startswith(terminal) for line in lines) != 1:
            raise AssertionError(f"terminal marker: {unit.slug}")
        row_lines = [line for line in lines if line.startswith("ROW ")]
        if len(row_lines) != 1:
            raise AssertionError(f"row count: {unit.slug}")
        row = json.loads(row_lines[0][4:])
        expected = {
            "slug": unit.slug,
            "kind": unit.kind,
            "index": unit.index,
            "depth": unit.depth,
            "part": unit.part,
            "t_lo": cert.fraction_string(unit.lo),
            "t_hi": cert.fraction_string(unit.hi),
            "grid": unit.grid,
            "band_radius": "62/5",
        }
        if any(row[key] != value for key, value in expected.items()):
            raise AssertionError(f"row contract: {unit.slug}")
        if row["slug"] in rows or not arb(row["margin_lower"]) > 0:
            raise AssertionError(f"duplicate or nonpositive: {unit.slug}")
        rows[row["slug"]] = row
    if len(heads) != 1 or set(rows) != {unit.slug for unit in units}:
        raise AssertionError("commit or cover mismatch")
    if not hybrid.edge_starts_no_later_than_cut():
        raise AssertionError("moving-edge inclusion")
    worst = min(rows.values(), key=lambda row: float(arb(row["margin_lower"])))
    print(
        "K2 hybrid ninth birth transcripts OK: 158 regular units, "
        "t<=313/100; moving-edge complement assigned to G5; worst",
        worst["slug"],
        "margin_lower",
        worst["margin_lower"],
    )


if __name__ == "__main__":
    validate()
