from __future__ import annotations

import hashlib
import io
import importlib.util
import json
from pathlib import Path
import tarfile

import pytest


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "tmp" / "seal_c6d_step3_localized_precision_prevalidation.py"
PACKAGE_SCRIPT = ROOT / "tmp" / "package_c6d_step3_localized_precision_evidence.py"


def load_sealer():
    spec = importlib.util.spec_from_file_location("seal_c6d_step3", SCRIPT)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def load_package():
    spec = importlib.util.spec_from_file_location("package_c6d_step3", PACKAGE_SCRIPT)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def test_remove_prevalidation_block_is_selective() -> None:
    sealer = load_sealer()
    source = (
        "import Mathlib\n\n"
        "/-!\n"
        "PRE-VALIDATION: source present but not compiler-verified.\n"
        "Second marker line to remove.\n\n"
        "Retained module documentation.\n"
        "-/\n\n"
        "theorem kept : True := by trivial\n"
    ).encode()
    sealed = sealer.remove_prevalidation_block(source, "synthetic.lean").decode()
    assert "PRE-VALIDATION:" not in sealed
    assert "Second marker line" not in sealed
    assert "Retained module documentation." in sealed
    assert "theorem kept" in sealed


def test_remove_prevalidation_block_rejects_ambiguity() -> None:
    sealer = load_sealer()
    with pytest.raises(RuntimeError, match="PREVALIDATION_BLOCK_COUNT"):
        sealer.remove_prevalidation_block(b"import Mathlib\n", "missing.lean")


def test_sealed_core_preserves_one_existing_import_and_adds_only_missing() -> None:
    sealer = load_sealer()

    class Verifier:
        BRICKS = (("First", 1), ("Second", 1), ("Third", 1))

    existing = "import YangMills.RG.SecondAudit"
    sealed = sealer.sealed_core(
        ("import Mathlib\n" + existing + "\n").encode(), Verifier
    ).decode()
    lines = sealed.splitlines()
    assert lines.count("import YangMills.RG.FirstAudit") == 1
    assert lines.count(existing) == 1
    assert lines.count("import YangMills.RG.ThirdAudit") == 1


def test_sealed_core_rejects_duplicate_existing_import() -> None:
    sealer = load_sealer()

    class Verifier:
        BRICKS = (("Only", 1),)

    duplicate = "import YangMills.RG.OnlyAudit\n" * 2
    with pytest.raises(RuntimeError, match="CORE_IMPORT_DUPLICATE"):
        sealer.sealed_core(duplicate.encode(), Verifier)


def test_archive_evidence_requires_exact_hash_and_one_json(tmp_path: Path) -> None:
    package = load_package()
    archive = tmp_path / "evidence.tar.gz"
    payload = json.dumps({"status": "PASS", "source_sha": "a" * 40}).encode()
    with tarfile.open(archive, "w:gz") as stream:
        directory = tarfile.TarInfo("evidence")
        directory.type = tarfile.DIRTYPE
        stream.addfile(directory)
        member = tarfile.TarInfo("evidence/evidence.json")
        member.size = len(payload)
        stream.addfile(member, io.BytesIO(payload))
    measured = hashlib.sha256(archive.read_bytes()).hexdigest().upper()
    observed, parsed = package.archive_evidence(archive, measured)
    assert observed == payload
    assert parsed["status"] == "PASS"
    with pytest.raises(RuntimeError, match="ARCHIVE_SHA256"):
        package.archive_evidence(archive, "0" * 64)
