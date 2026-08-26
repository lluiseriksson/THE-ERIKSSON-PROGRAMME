from __future__ import annotations

import hashlib
import importlib.util
import io
import json
from pathlib import Path
import subprocess
import sys
import tarfile


ROOT = Path(__file__).resolve().parents[1]
VERIFIER = ROOT / "tmp" / "verify_eq337_covariant_derivative_archive.py"
PACKAGER = ROOT / "tmp" / "package_eq337_covariant_derivative_archive.py"
SOURCE_SHA = "573d70e09eb3f069cc3e86f43ab76b16a2349163"
RUNNER_REV = "eq337-complex-coordinate-promoted-cold-v2"


def load_verifier():
    spec = importlib.util.spec_from_file_location("eq337_derivative_archive_test", VERIFIER)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def git_blob(path: str) -> bytes:
    return subprocess.run(
        ["git", "-c", "safe.directory=*", "cat-file", "blob", f"{SOURCE_SHA}:{path}"],
        cwd=ROOT,
        check=True,
        stdout=subprocess.PIPE,
    ).stdout


def synthetic_archive(path: Path, *, forbidden: bool = False) -> None:
    verifier = load_verifier()
    outputs = {stage: "" for stage in verifier.stages()}
    for index, (module, _) in enumerate(verifier.MODULES, start=1):
        audit_path = f"YangMills/RG/{module}Audit.lean"
        declarations = verifier.PRINT_RE.findall(git_blob(audit_path).decode())
        outputs[f"eq337_covariant_derivative_{index:02d}_{module.lower()}_audit"] = "".join(
            f"'{name}' depends on axioms: "
            f"[{'sorryAx' if forbidden and index == 1 and offset == 0 else 'propext, Quot.sound'}]\n"
            for offset, name in enumerate(declarations)
        )
    source_paths = {"YangMillsCore.lean"} | {
        relative
        for module, _ in verifier.MODULES
        for relative in (
            f"YangMills/RG/{module}.lean",
            f"YangMills/RG/{module}Audit.lean",
        )
    }
    source_blobs = {relative: hashlib.sha256(git_blob(relative)).hexdigest() for relative in source_paths}
    records = [
        {
            "stage": stage,
            "exit": 0,
            "seconds": 1.0,
            "output_sha256": hashlib.sha256(output.encode()).hexdigest(),
        }
        for stage, output in outputs.items()
    ]
    evidence = {
        "runner_rev": RUNNER_REV,
        "source_sha": SOURCE_SHA,
        "source_blobs": source_blobs,
        "mathlib_sha": verifier.EXPECTED_MATHLIB,
        "toolchain_asset_sha256": verifier.EXPECTED_TOOLCHAIN,
        "status": "PASS",
        "records": records,
    }
    root = "hrpoly-eq337-covariant-derivative-evidence"
    with tarfile.open(path, "w:gz") as archive:
        payload = (json.dumps(evidence, sort_keys=True, separators=(",", ":")) + "\n").encode()
        info = tarfile.TarInfo(f"{root}/evidence.json")
        info.size = len(payload)
        archive.addfile(info, io.BytesIO(payload))
        for stage, output in outputs.items():
            payload = output.encode()
            info = tarfile.TarInfo(f"{root}/{stage}.stdout")
            info.size = len(payload)
            archive.addfile(info, io.BytesIO(payload))


def run_verifier(archive: Path) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [
            sys.executable, str(VERIFIER), "--repo", str(ROOT),
            "--archive", str(archive), "--source-sha", SOURCE_SHA,
            "--runner-rev", RUNNER_REV,
        ],
        cwd=ROOT,
        check=False,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )


def test_archive_verifier_accepts_exact_scope(tmp_path: Path) -> None:
    archive = tmp_path / "evidence.tar.gz"
    synthetic_archive(archive)
    child = run_verifier(archive)
    assert child.returncode == 0, child.stderr
    result = json.loads(child.stdout)
    assert result["status"] == "EQ337_COVARIANT_DERIVATIVE_EVIDENCE_OK"
    assert result["expected_declarations"] == 57


def test_archive_verifier_rejects_forbidden_axiom(tmp_path: Path) -> None:
    archive = tmp_path / "forbidden.tar.gz"
    synthetic_archive(archive, forbidden=True)
    child = run_verifier(archive)
    assert child.returncode != 0
    assert "FORBIDDEN_AXIOM=sorryAx" in child.stderr


def test_packager_preserves_verified_archive(tmp_path: Path) -> None:
    archive = tmp_path / "evidence.tar.gz"
    synthetic_archive(archive)
    destination = tmp_path / "package"
    child = subprocess.run(
        [
            sys.executable, str(PACKAGER), "--archive", str(archive),
            "--destination", str(destination), "--source-sha", SOURCE_SHA,
            "--runner-rev", RUNNER_REV,
        ],
        cwd=ROOT,
        check=False,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    assert child.returncode == 0, child.stderr
    manifest = json.loads((destination / "manifest.json").read_text(encoding="utf-8"))
    assert manifest["status"] == "EQ337_COVARIANT_DERIVATIVE_ARCHIVE_PACKAGE_OK"
    assert (destination / "SHA256SUMS").is_file()
