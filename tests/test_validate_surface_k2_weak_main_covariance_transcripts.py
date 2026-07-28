"""Static/parser tests for the preregistered weak-main transcript validator."""

from decimal import Decimal
import hashlib
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
    assert MODULE.endpoints("[+/- 0.0246]") == (
        Decimal("-0.0246"),
        Decimal("0.0246"),
    )


def test_frozen_validator_contract() -> None:
    source = SCRIPT.read_text(encoding="utf-8")
    assert "EXPECTED_HEAD = \"150f439ba30ac1ee915fc92e93ec0b4d708f4349\"" in source
    assert "expected 576 rows" in source
    assert "if not xmain_lower > TARGET" in source
    assert "production/replay byte mismatch" in source
    assert "stderr is not empty" in source
    assert '"dependencies": 11' in source
    assert '"dependencies": 12' in source
    assert '"grids": (24, 48, 96)' in source
    assert "KDLOWER" in source
    assert "XMAINLOWER" in source


def test_dependency_hash_accepts_only_eol_equivalent_bytes(tmp_path: Path) -> None:
    dependency = tmp_path/"dependency.py"
    lf = b"first line\nsecond line\n"
    crlf = lf.replace(b"\n", b"\r\n")
    dependency.write_bytes(crlf)

    lf_digest = hashlib.sha256(lf).hexdigest()
    crlf_digest = hashlib.sha256(crlf).hexdigest()
    assert MODULE.dependency_hash_matches(dependency, lf_digest)
    assert MODULE.dependency_hash_matches(dependency, crlf_digest)

    dependency.write_bytes(b"first line\nchanged line\n")
    assert not MODULE.dependency_hash_matches(dependency, lf_digest)
    assert not MODULE.dependency_hash_matches(dependency, crlf_digest)
