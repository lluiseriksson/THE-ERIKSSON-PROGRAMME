from __future__ import annotations

import importlib.util
import hashlib
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location(
    "run_record_archive", ROOT / "scripts" / "run_record_archive.py"
)
assert SPEC and SPEC.loader
archive = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = archive
SPEC.loader.exec_module(archive)


def test_repository_run_record_archive_is_closed() -> None:
    assert archive.validate_archive() == []


def test_historical_baseline_is_not_changed_artifact_coverage() -> None:
    text = (ROOT / "scripts" / "validate_changed_run_coverage.py").read_text(
        encoding="utf-8"
    )
    assert "historical-artifact-baseline" not in text
    assert archive.ARTIFACT_BASELINE.name == "historical-artifact-baseline.json"


def test_frozen_record_resolution_is_hash_bound() -> None:
    records = archive.iter_auditable_run_records("surface-scaled-bulk-*.json")
    assert records
    for logical, physical in records:
        assert logical.startswith("run-manifests/")
        assert physical.is_file()
        if physical.parent == archive.LEGACY_DIR:
            assert archive.frozen_record_path(physical.name) == physical


def test_frozen_record_hash_binding_is_eol_stable_only(tmp_path: Path) -> None:
    path = tmp_path / "record.json"
    raw = b'{\r\n  "value": 1\r\n}\r\n'
    lf = raw.replace(b"\r\n", b"\n")
    path.write_bytes(raw)
    raw_digest = hashlib.sha256(raw).hexdigest()
    lf_digest = hashlib.sha256(lf).hexdigest()
    assert archive.matches_eol_bound(path, raw_digest, lf_digest)
    path.write_bytes(lf)
    assert archive.matches_eol_bound(path, raw_digest, lf_digest)
    path.write_bytes(lf.replace(b"1", b"2"))
    assert not archive.matches_eol_bound(path, raw_digest, lf_digest)


def test_lf_size_tracks_only_crlf_normalization(tmp_path: Path) -> None:
    path = tmp_path / "transcript.txt"
    raw = b"a\r\nb\r\nc\n"
    path.write_bytes(raw)
    assert archive.size_lf(path) == len(raw.replace(b"\r\n", b"\n"))


def test_v88_live_reference_scan_excludes_only_the_explicit_archive() -> None:
    text = (ROOT / "scripts" / "audit_v88_sanitation.py").read_text(
        encoding="utf-8"
    )
    assert 'startswith("run-records/")' in text
    assert ("SUPERSEDED" + "_nonmonotone") in text


def test_historical_generators_cannot_write_into_strict_manifests() -> None:
    candidates = [
        path
        for path in (ROOT / "scripts").glob("*.py")
        if path.name.startswith(("make_", "index_"))
        or path.name == "run_surface_scaled_bulk_cwin3p2_seeded_campaign.py"
    ]
    offenders = [
        path.name
        for path in candidates
        if "run-manifests" in path.read_text(encoding="utf-8")
    ]
    assert offenders == []
    ignore = (ROOT / ".gitignore").read_text(encoding="utf-8")
    assert "run-records/local-staging/*.json" in ignore
