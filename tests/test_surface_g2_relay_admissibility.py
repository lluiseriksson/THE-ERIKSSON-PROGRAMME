from pathlib import Path

import importlib.util


ROOT = Path(__file__).resolve().parents[1]
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


def test_audit_never_claims_relay_from_sign_rows():
    assert MOD.RELAY_STATUS == "RELAY_LEMMA_UNPROVED"
    assert MOD.T_LEFT == MOD.fraction("3/5")
