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
VERIFIER = ROOT / "tmp" / "verify_eq337_complex_ubar_radius_archive.py"
CONTRACT = ROOT / "tmp" / "verify_eq337_complex_ubar_radius_evidence.py"
PACKAGER = ROOT / "tmp" / "package_eq337_complex_ubar_radius_archive.py"


def load(path: Path, name: str):
    spec = importlib.util.spec_from_file_location(name, path)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def synthetic_archive(path: Path, *, forbidden: bool = False) -> None:
    contract = load(CONTRACT, "eq337_ubar_archive_test_contract")
    outputs = {stage: "" for stage in contract.STAGES}
    prereq, _ = contract.PREREQUISITE
    declarations = contract.PRINT_RE.findall(
        contract.git_blob(ROOT, f"YangMills/RG/{prereq}Audit.lean").decode()
    )
    outputs["complex_ubar_radius_perturbed_background_audit"] = "".join(
        f"'{name}' depends on axioms: [propext, Quot.sound]\n"
        for name in declarations
    )
    for index, (module, _) in enumerate(contract.MODULES, start=1):
        declarations = contract.PRINT_RE.findall(
            contract.git_blob(ROOT, f"YangMills/RG/{module}Audit.lean").decode()
        )
        if forbidden and index == 1:
            outputs[
                f"complex_ubar_radius_{index:02d}_{module.lower()}_audit"
            ] = "".join(
                f"'{name}' depends on axioms: "
                f"[{'sorryAx' if offset == 0 else 'propext, Quot.sound'}]\n"
                for offset, name in enumerate(declarations)
            )
        else:
            outputs[
                f"complex_ubar_radius_{index:02d}_{module.lower()}_audit"
            ] = "".join(
                f"'{name}' depends on axioms: [propext, Quot.sound]\n"
                for name in declarations
            )

    source_paths = {"YangMillsCore.lean"} | {
        relative
        for module, _ in contract.MODULES
        for relative in (
            f"YangMills/RG/{module}.lean",
            f"YangMills/RG/{module}Audit.lean",
        )
    }
    source_blobs = {
        relative: hashlib.sha256(contract.git_blob(ROOT, relative)).hexdigest()
        for relative in source_paths
    }
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
        "runner_rev": contract.RUNNER_REV,
        "source_sha": contract.SOURCE_SHA,
        "source_blobs": source_blobs,
        "mathlib_sha": "07642720480157414db592fa85b626dafb71355b",
        "toolchain_asset_sha256": (
            "bf3e0a4025e47a0bea9ed907d12dcccd3d3590b1d8ad6c55a915298b01ad9d3e"
        ),
        "status": "PASS",
        "records": records,
    }
    root = "hrpoly-eq337-complex-ubar-radius-evidence"
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
        [sys.executable, str(VERIFIER), "--repo", str(ROOT), "--archive", str(archive)],
        cwd=ROOT,
        check=False,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )


def test_archive_verifier_accepts_exact_stage_outputs(tmp_path: Path) -> None:
    archive = tmp_path / "evidence.tar.gz"
    synthetic_archive(archive)
    child = run_verifier(archive)
    assert child.returncode == 0, child.stderr
    result = json.loads(child.stdout)
    assert result["status"] == "EQ337_COMPLEX_UBAR_RADIUS_EVIDENCE_OK"
    assert result["expected_declarations"] == 79
    assert result["transport"] == "durable-stage-stdout-archive"


def test_archive_verifier_rejects_forbidden_axiom(tmp_path: Path) -> None:
    archive = tmp_path / "forbidden.tar.gz"
    synthetic_archive(archive, forbidden=True)
    child = run_verifier(archive)
    assert child.returncode != 0
    assert "FORBIDDEN_AXIOM=sorryAx" in child.stderr


def test_archive_packager_preserves_verified_tar(tmp_path: Path) -> None:
    archive = tmp_path / "evidence.tar.gz"
    synthetic_archive(archive)
    destination = tmp_path / "package"
    child = subprocess.run(
        [
            sys.executable,
            str(PACKAGER),
            "--archive",
            str(archive),
            "--destination",
            str(destination),
        ],
        cwd=ROOT,
        check=False,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    assert child.returncode == 0, child.stderr
    manifest = json.loads((destination / "manifest.json").read_text(encoding="utf-8"))
    assert manifest["status"] == "EQ337_COMPLEX_UBAR_RADIUS_ARCHIVE_PACKAGE_OK"
    assert (destination / "SHA256SUMS").is_file()
