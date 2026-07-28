import sys
from pathlib import Path

import pytest


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

import validate_surface_high_beta_g5_ratio_side4_lambda3 as validator


def test_committed_ratio_side4_lambda3_union() -> None:
    result = validator.validate()
    assert result["rows"] == 450
    assert result["worst_b0"] > 0
    assert result["worst_ratio"] > 0
    assert len(result["worst_b0_cell"]) == 2
    assert len(result["worst_ratio_cell"]) == 2


def test_ratio_side4_lambda3_rejects_geometry_tamper(tmp_path: Path) -> None:
    unit = validator.cert.UNITS[0]
    name = validator.cert.unit_slug(unit) + ".txt"
    source = validator.PRODUCTION / name
    text = source.read_text(encoding="utf-8")
    tampered_text = text.replace(
        '"delta_hi": "1/1000"',
        '"delta_hi": "2/1000"',
        1,
    )
    assert tampered_text != text
    tampered = tmp_path / name
    tampered.write_text(tampered_text, encoding="utf-8")
    with pytest.raises(AssertionError, match="wrong delta_hi"):
        validator.validate_file(tampered, unit)
