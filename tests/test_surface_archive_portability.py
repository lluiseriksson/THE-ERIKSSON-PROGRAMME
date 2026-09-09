"""Historical Windows paths must work without changing evidence identities."""

import hashlib
from pathlib import Path
import sys

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
import audit_surface_g2_relay_admissibility as audit


@pytest.mark.parametrize("separator", ["/", "\\"])
@pytest.mark.parametrize("ending", [b"\n", b"\r\n"])
def test_historical_output_paths_and_hashes_are_portable(tmp_path, monkeypatch, separator, ending):
    monkeypatch.setattr(audit, "ROOT", tmp_path)
    (tmp_path / "scripts").mkdir()
    original = b"recorded result\r\nsecond row\r\n"
    payload = original.replace(b"\r\n", ending)
    digest = hashlib.sha256(original).hexdigest()
    outputs = []
    for name in ("result.txt", "result_rerun.txt"):
        (tmp_path / "scripts" / name).write_bytes(payload)
        outputs.append({"path": f"scripts{separator}{name}", "sha256": digest})
    assert audit.verify_outputs(*outputs) == []
    group, production, replay = audit.output_groups({"outputs": outputs})[0]
    assert group == "result"
    # Retain the original spellings in the identity bound by the fingerprint.
    assert production["path"] == outputs[0]["path"]
    assert replay["path"] == outputs[1]["path"]


@pytest.mark.parametrize("damage,reason", [
    ("both", "recorded_output_hash_mismatch"),
    ("replay", "production_replay_byte_mismatch"),
    ("missing", "production_or_replay_file_missing"),
])
def test_path_portability_does_not_admit_damaged_or_missing_evidence(tmp_path, monkeypatch, damage, reason):
    monkeypatch.setattr(audit, "ROOT", tmp_path)
    (tmp_path / "scripts").mkdir()
    payload = b"CERTIFIED value 1\n"
    production = tmp_path / "scripts" / "result.txt"
    replay = tmp_path / "scripts" / "result_rerun.txt"
    production.write_bytes(payload)
    replay.write_bytes(payload)
    records = [
        {"path": "scripts\\result.txt", "sha256": hashlib.sha256(payload).hexdigest()},
        {"path": "scripts\\result_rerun.txt", "sha256": hashlib.sha256(payload).hexdigest()},
    ]
    if damage == "both":
        production.write_bytes(b"CERTIFIED value 2\n")
        replay.write_bytes(production.read_bytes())
    elif damage == "replay":
        replay.write_bytes(b"CERTIFIED value 2\n")
    else:
        replay.unlink()
    assert reason in audit.verify_outputs(*records)


@pytest.mark.parametrize("path", ["../outside.txt", "scripts\\..\\outside.txt", "/outside.txt", "C:\\outside.txt", "C:outside.txt", "\\\\server\\share\\file.txt"])
def test_archive_paths_cannot_escape_repository(tmp_path, monkeypatch, path):
    monkeypatch.setattr(audit, "ROOT", tmp_path)
    with pytest.raises(ValueError):
        audit.archive_path(path)


def test_terminal_fingerprint_keeps_raw_manifest_identity_and_detects_mutation(tmp_path, monkeypatch):
    monkeypatch.setattr(audit, "ROOT", tmp_path)
    (tmp_path / "scripts").mkdir()
    (tmp_path / "run-manifests").mkdir()
    manifest = tmp_path / "run-manifests" / "unit.json"
    manifest.write_bytes(b'{"claim":"original"}\n')
    for name in ("result.txt", "result_rerun.txt"):
        (tmp_path / "scripts" / name).write_bytes(b"recorded result\n")
    unit = {"manifest": "unit.json", "unit": "outputs", "ok": True,
            "production": "scripts\\result.txt", "replay": "scripts\\result_rerun.txt"}
    owner = {"manifest": "unit.json", "unit": "outputs",
             "owned_beta": ["20", "21"], "source_beta": ["20", "21"]}
    original = audit.terminal_fingerprint([unit], [owner])
    # Lookup normalization must not silently normalize the frozen identity.
    slash_unit = {**unit, "production": "scripts/result.txt", "replay": "scripts/result_rerun.txt"}
    assert audit.terminal_fingerprint([slash_unit], [owner]) != original
    for name in ("result.txt", "result_rerun.txt"):
        (tmp_path / "scripts" / name).write_bytes(b"recorded result\r\n")
    assert audit.terminal_fingerprint([unit], [owner]) == original
    manifest.write_bytes(b'{"claim":"changed"}\n')
    assert audit.terminal_fingerprint([unit], [owner]) != original
