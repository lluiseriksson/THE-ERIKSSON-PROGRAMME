from __future__ import annotations

import json
import sys
from pathlib import Path

import pytest


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

import audit_surface_k2_normalization_supersession as audit  # noqa: E402


def manifest(status: str, digest: str) -> dict[str, object]:
    return {
        "status": status,
        "inputs": [
            {
                "path": audit.TARGET_PATH,
                "sha256_lf": digest,
            }
        ],
    }


def test_repository_withdrawal_scope_is_exact() -> None:
    affected, current = audit.audit(ROOT / "run-manifests")
    assert len(affected) == 22
    assert len(current) == 12


def test_corrected_future_blob_is_not_withdrawn(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    names = sorted(audit.EXPECTED_CURRENT_WITHDRAWALS)
    monkeypatch.setattr(audit, "EXPECTED_CURRENT_WITHDRAWALS", {names[0]})
    (tmp_path / names[0]).write_text(
        json.dumps(manifest("current", audit.WITHDRAWN_SHA256_LF)),
        encoding="utf-8",
    )
    (tmp_path / "corrected.json").write_text(
        json.dumps(manifest("current", "0" * 64)),
        encoding="utf-8",
    )
    affected, current = audit.audit(tmp_path)
    assert [path.name for path in affected] == [names[0]]
    assert [path.name for path in current] == [names[0]]


def test_unregistered_current_dependency_is_rejected(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    monkeypatch.setattr(audit, "EXPECTED_CURRENT_WITHDRAWALS", set())
    (tmp_path / "unexpected.json").write_text(
        json.dumps(manifest("current", audit.WITHDRAWN_SHA256_LF)),
        encoding="utf-8",
    )
    with pytest.raises(ValueError, match="unexpected"):
        audit.audit(tmp_path)
