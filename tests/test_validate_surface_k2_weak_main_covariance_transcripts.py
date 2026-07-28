"""Static/parser tests for the preregistered weak-main transcript validator."""

from decimal import Decimal
import importlib.util
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = (
    ROOT/"scripts"/
    "validate_surface_k2_weak_main_covariance_transcripts.py"
)
SPEC = importlib.util.spec_from_file_location("weak_validator", SCRIPT)
MODULE = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
SPEC.loader.exec_module(MODULE)


def test_decimal_ball_parser() -> None:
    assert MODULE.endpoints("[1.25 +/- 0.05]") == (
        Decimal("1.20"),
        Decimal("1.30"),
    )
    assert MODULE.endpoints("-0.049") == (
        Decimal("-0.049"),
        Decimal("-0.049"),
    )


def test_frozen_validator_contract() -> None:
    source = SCRIPT.read_text(encoding="utf-8")
    assert "EXPECTED_HEAD = \"150f439ba30ac1ee915fc92e93ec0b4d708f4349\"" in source
    assert "expected 576 rows" in source
    assert "if not xmain_lower > TARGET" in source
    assert "production/replay byte mismatch" in source
    assert "stderr is not empty" in source
