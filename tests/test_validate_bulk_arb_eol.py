from __future__ import annotations

import hashlib
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

import validate_bulk_arb_transcript as validator  # noqa: E402


def test_historical_bulk_binding_accepts_only_eol_normalization() -> None:
    raw = b"alpha\r\nbeta\r\n"
    lf = raw.replace(b"\r\n", b"\n")
    raw_digest = hashlib.sha256(raw).hexdigest()
    lf_digest = hashlib.sha256(lf).hexdigest()
    assert validator._matches_eol_bound(raw, raw_digest, lf_digest)
    assert validator._matches_eol_bound(lf, raw_digest, lf_digest)
    assert not validator._matches_eol_bound(
        lf.replace(b"beta", b"gamma"), raw_digest, lf_digest
    )


def test_historical_bulk_certificate_validates_in_current_checkout() -> None:
    result = validator.validate()
    assert result["beta_boxes"] == 3472
    assert result["t_boxes"] == 592_068
