from __future__ import annotations

import importlib.util
import json
from pathlib import Path
import subprocess
import sys


ROOT = Path(__file__).resolve().parents[1]
MATERIALIZER = ROOT / "tmp" / "promote_eq337_complex_ubar_radius_boundary.py"


def load_materializer():
    spec = importlib.util.spec_from_file_location("eq337_ubar_promotion", MATERIALIZER)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def test_preview_scope_is_exact_and_prevalidation_preserved() -> None:
    materializer = load_materializer()
    verifier = materializer.load_module(materializer.VERIFIER, "test_ubar_verifier")
    rows = materializer.boundary(verifier.SOURCE_SHA)
    assert len(rows) == 14
    assert len({destination for _, destination, _ in rows}) == 14
    assert all(source.startswith("tmp/") for source, _, _ in rows)
    assert all(destination.startswith("YangMills/RG/") for _, destination, _ in rows)
    assert all(b"PRE-VALIDATION:" in data for _, _, data in rows)
    assert materializer.manifest_digest(rows) == (
        "625C7EAC2EC08CE5168936B6E705B1C6F782F176459FDEAA151778C13E9EA4CF"
    )


def test_apply_requires_evidence_before_any_write() -> None:
    child = subprocess.run(
        [sys.executable, str(MATERIALIZER), "--apply"],
        cwd=ROOT,
        check=False,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    assert child.returncode != 0
    assert "UBAR_EVIDENCE_MANIFEST_REQUIRED" in child.stderr
    materializer = load_materializer()
    assert all(not (ROOT / materializer.destination(path)).exists() for path in materializer.paths())


def test_evidence_manifest_is_bound_to_source_and_runner(tmp_path: Path) -> None:
    materializer = load_materializer()
    verifier = materializer.load_module(materializer.VERIFIER, "test_ubar_verifier_manifest")
    manifest = tmp_path / "manifest.json"
    manifest.write_text(
        json.dumps(
            {
                "status": "EQ337_COMPLEX_UBAR_RADIUS_PACKAGE_OK",
                "source_sha": verifier.SOURCE_SHA,
                "runner_revision": verifier.RUNNER_REV,
            }
        ),
        encoding="utf-8",
    )
    materializer.require_evidence(manifest, verifier)
    payload = json.loads(manifest.read_text(encoding="utf-8"))
    payload["source_sha"] = "0" * 40
    manifest.write_text(json.dumps(payload), encoding="utf-8")
    try:
        materializer.require_evidence(manifest, verifier)
    except RuntimeError as error:
        assert str(error) == "UBAR_EVIDENCE_SOURCE_MISMATCH"
    else:
        raise AssertionError("source drift was accepted")
