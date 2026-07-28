"""Regression test for the pure lambda-three weak-relay validator."""

import hashlib
import sys
from pathlib import Path


SCRIPTS = Path(__file__).resolve().parents[1]/"scripts"
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

import validate_surface_high_beta_lambda3_weak_relay_inputs as validator


def test_lambda3_transcript_implies_tighter_weak_relay_bounds() -> None:
    result = validator.validate()
    assert result["rho_upper"] < validator.RHO_THRESHOLD
    assert result["adverse_upper"] < validator.ADVERSE_THRESHOLD


def test_dependency_hash_accepts_only_eol_equivalent_bytes(tmp_path: Path) -> None:
    dependency = tmp_path/"dependency.py"
    lf = b"first line\nsecond line\n"
    crlf = lf.replace(b"\n", b"\r\n")
    dependency.write_bytes(lf)

    lf_digest = hashlib.sha256(lf).hexdigest()
    crlf_digest = hashlib.sha256(crlf).hexdigest()
    assert validator.dependency_hash_matches(dependency, lf_digest)
    assert validator.dependency_hash_matches(dependency, crlf_digest)

    dependency.write_bytes(b"first line\nchanged line\n")
    assert not validator.dependency_hash_matches(dependency, lf_digest)
    assert not validator.dependency_hash_matches(dependency, crlf_digest)
