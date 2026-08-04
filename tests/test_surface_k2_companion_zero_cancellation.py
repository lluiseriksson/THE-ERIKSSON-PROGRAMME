from __future__ import annotations

import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT/"scripts"))

import verify_surface_k2_companion_zero_cancellation as verify  # noqa: E402


def test_all_registered_companion_truncations_cancel_at_zero() -> None:
    verify.verify()
