"""Exercise pinned historical validators with EOL variants and real mutations."""

import hashlib
from pathlib import Path
import sys

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
import audit_surface_g2_weak_terminal_cover as terminal
import validate_bulk_arb_transcript as bulk
import validate_surface_bulk_3_6 as surface_bulk
import validate_surface_high_beta_lambda3_joint_interior as joint
import validate_surface_high_beta_lambda3_weak_relay_inputs as weak


def eol(raw, ending):
    return raw.replace(b"\r\n", b"\n").replace(b"\n", ending)


@pytest.mark.parametrize("module", [bulk, surface_bulk], ids=["bulk", "surface-bulk"])
@pytest.mark.parametrize("ending", [b"\n", b"\r\n"])
def test_bulk_keeps_historical_blob_and_content_checks(tmp_path, monkeypatch, module, ending):
    script = tmp_path / "source.py"
    transcript = tmp_path / "transcript.txt"
    script.write_bytes(eol(module.SCRIPT.read_bytes(), ending))
    transcript.write_bytes(eol(module.TRANSCRIPT.read_bytes(), ending))
    monkeypatch.setattr(module, "SCRIPT", script)
    monkeypatch.setattr(module, "TRANSCRIPT", transcript)
    result = module.validate() if module is bulk else module.validate(transcript)
    assert result["beta_boxes"] == 3472 and result["t_boxes"] == 592068
    assert result["transcript_sha256"] == hashlib.sha256(transcript.read_bytes()).hexdigest()
    script.write_bytes(script.read_bytes() + b"# changed source\n")
    with pytest.raises(AssertionError):
        module.validate() if module is bulk else module.validate(transcript)


def copied_lambda_pair(tmp_path, monkeypatch, module, ending):
    payload = eol(module.PRODUCTION.read_bytes(), ending)
    production, replay = tmp_path / "production.txt", tmp_path / "replay.txt"
    production.write_bytes(payload)
    replay.write_bytes(payload)
    monkeypatch.setattr(module, "PRODUCTION", production)
    monkeypatch.setattr(module, "REPLAY", replay)
    return production, replay


@pytest.mark.parametrize("module", [joint, weak], ids=["joint", "weak"])
@pytest.mark.parametrize("ending", [b"\n", b"\r\n"])
def test_lambda_three_accepts_only_representation_changes(tmp_path, monkeypatch, module, ending):
    production, replay = copied_lambda_pair(tmp_path, monkeypatch, module, ending)
    result = module.validate()
    key = "sha256" if module is joint else "transcript_sha256"
    assert result[key] == hashlib.sha256(production.read_bytes()).hexdigest()
    changed = production.read_bytes().replace(b"INTERIOR PASS", b"INTERIOR FAIL")
    assert changed != production.read_bytes()
    production.write_bytes(changed)
    replay.write_bytes(changed)
    with pytest.raises(AssertionError, match="digest"):
        module.validate()


@pytest.mark.parametrize("module", [joint, weak], ids=["joint", "weak"])
def test_lambda_three_keeps_production_replay_byte_equality(tmp_path, monkeypatch, module):
    production, replay = copied_lambda_pair(tmp_path, monkeypatch, module, b"\n")
    replay.write_bytes(eol(production.read_bytes(), b"\r\n"))
    with pytest.raises(AssertionError, match="byte mismatch"):
        module.validate()


@pytest.mark.parametrize("name", ["near", "far"])
@pytest.mark.parametrize("ending", [b"\n", b"\r\n"])
def test_exact_relay_pairs_preserve_pinned_hashes_and_reject_mutation(tmp_path, monkeypatch, name, ending):
    stem = terminal.RELAY_PAIRS[name]["stem"]
    original_root = terminal.ROOT
    output = tmp_path / "outputs"
    output.mkdir()
    files = []
    for kind in ("production", "replay"):
        filename = f"{stem}-{kind}-20260728.txt"
        path = output / filename
        path.write_bytes(eol((original_root / "outputs" / filename).read_bytes(), ending))
        (output / f"{stem}-{kind}-20260728.stderr.txt").write_bytes(b"")
        files.append(path)
    monkeypatch.setattr(terminal, "ROOT", tmp_path)
    observed = terminal._validate_relay_pair(name)
    assert observed == hashlib.sha256(files[0].read_bytes()).hexdigest().upper()
    for path in files:
        path.write_bytes(path.read_bytes().replace(b"EXACT PASS", b"EXACT FAIL"))
    with pytest.raises(AssertionError):
        terminal._validate_relay_pair(name)
