from pathlib import Path
import json

import importlib.util
import sys


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
SPEC = importlib.util.spec_from_file_location(
    "audit_surface_g2_relay_admissibility",
    ROOT / "scripts" / "audit_surface_g2_relay_admissibility.py",
)
MOD = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MOD)


def test_known_cwin_three_halves_unit_has_strict_rows():
    result = MOD.parse_transcript(
        ROOT / "scripts" / "surface_scaled_bulk_101p75_101p78125.txt"
    )
    assert result["cwin"] == "3/2"
    assert result["rows"] > 0
    assert "nonnegative_or_nonfinite_upper" not in result["reasons"]
    assert "row_adjacency_failure" not in result["reasons"]


def test_moving_right_seam_uses_beta_hi_not_beta_lo():
    result = MOD.parse_transcript(
        ROOT / "scripts" / "surface_scaled_bulk_ladder20_r300prereg.txt"
    )
    beta_lo, beta_hi = map(MOD.fraction, result["beta"])
    expected = MOD.arb.pi() - MOD.arb(3) / (MOD.arb(2) * MOD.arb(beta_hi.numerator) / MOD.arb(beta_hi.denominator))
    assert result["required_t"][1] == expected.str(18)
    assert beta_hi > beta_lo


def test_legacy_windows_artifact_path_is_portable():
    expected = ROOT / "scripts" / "surface_scaled_bulk_87_87p5.txt"
    assert MOD.artifact_path(r"scripts\surface_scaled_bulk_87_87p5.txt") == expected
    assert MOD.artifact_path("scripts/surface_scaled_bulk_87_87p5.txt") == expected


def test_legacy_artifact_path_rejects_parent_escape():
    import pytest

    with pytest.raises(ValueError, match="unsafe recorded artifact path"):
        MOD.artifact_path(r"..\outside.txt")


def test_terminal_promotion_is_bound_to_the_frozen_ownership_fingerprint():
    result = MOD.audit_summary()
    assert result["relay_status"] == "DIRECT_WRONSKIAN_SIGN_ARCHIVE_CERTIFIED"
    assert result["promotion"] == "FINITE_BULK_SIGN_CERTIFIED"
    assert result["canonical_subcover_owner_count"] == MOD.EXPECTED_OWNER_COUNT
    assert (
        result["canonical_subcover_fingerprint"]
        == MOD.EXPECTED_TERMINAL_FINGERPRINT
    )
    assert MOD.T_LEFT == MOD.fraction("3/5")


def test_nested_manifest_schema_is_normalized():
    from run_record_archive import frozen_record_path

    manifest = json.loads(
        frozen_record_path(
            "surface-scaled-bulk-cwin3p2-high-101p625-101p6875-20260720.json"
        ).read_text(encoding="utf-8")
    )
    assert len(MOD.output_groups(manifest)) == 2


def test_flat_manifest_schema_recovers_every_pair():
    from run_record_archive import frozen_record_path

    manifest = json.loads(
        frozen_record_path(
            "surface-scaled-bulk-cwin3p2-high-100p3125-100p5625-20260719.json"
        ).read_text(encoding="utf-8")
    )
    groups = MOD.output_groups(manifest)
    assert len(groups) == 4
    assert [name for name, _, _ in groups] == [
        "surface_scaled_bulk_cwin3p2_high_100p3125_100p375",
        "surface_scaled_bulk_cwin3p2_high_100p375_100p4375",
        "surface_scaled_bulk_cwin3p2_high_100p4375_100p5",
        "surface_scaled_bulk_cwin3p2_high_100p5_100p5625",
    ]


def _accepted(lo, hi, name):
    return {
        "manifest": f"{name}.json",
        "unit": name,
        "transcript": {"beta": [lo, hi]},
    }


def test_exact_union_accepts_redundant_overlap_and_builds_adjacent_ownership():
    old_hi = MOD.BETA_HI
    try:
        MOD.BETA_HI = MOD.fraction("23")
        result = MOD.beta_union_summary([
            _accepted("20", "21", "left"),
            _accepted("41/2", "22", "overlap"),
            _accepted("22", "23", "right"),
        ])
    finally:
        MOD.BETA_HI = old_hi
    assert result["raw_adjacency"] is False
    assert result["components"] == [["20", "23"]]
    assert result["gaps"] == []
    assert result["covered"] is True
    assert result["ownership_adjacency"] is True
    assert result["ownership_complete"] is True
    assert [row["owned_beta"] for row in result["ownership"]] == [
        ["20", "21"], ["21", "22"], ["22", "23"],
    ]


def test_exact_union_reports_a_real_gap_despite_adjacent_components():
    old_hi = MOD.BETA_HI
    try:
        MOD.BETA_HI = MOD.fraction("23")
        result = MOD.beta_union_summary([
            _accepted("20", "21", "left"),
            _accepted("43/2", "23", "right"),
        ])
    finally:
        MOD.BETA_HI = old_hi
    assert result["components"] == [["20", "21"], ["43/2", "23"]]
    assert result["gaps"] == [["21", "43/2"]]
    assert result["covered"] is False
    assert result["ownership_complete"] is False
