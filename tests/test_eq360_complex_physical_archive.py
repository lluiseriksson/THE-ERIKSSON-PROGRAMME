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
VERIFIER = ROOT / "tmp" / "verify_eq360_complex_physical_archive.py"
PACKAGER = ROOT / "tmp" / "package_eq360_complex_physical_archive.py"
CONTRACT = ROOT / "tmp" / "verify_eq360_complex_physical_contract.py"
RUNNER_REV = "eq360-complex-physical-test-v1"


def load(path: Path, name: str):
    spec = importlib.util.spec_from_file_location(name, path)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def make_repo(path: Path) -> tuple[str, dict[str, bytes]]:
    contract = load(CONTRACT, "eq360_fixture_contract")
    files: dict[str, bytes] = {"YangMillsCore.lean": b"-- fixture root\n"}
    for index, (module, count) in enumerate(contract.MODULES, start=1):
        files[f"YangMills/RG/{module}.lean"] = f"-- source {index}\n".encode()
        files[f"YangMills/RG/{module}Audit.lean"] = "".join(
            f"#print axioms fixture_{index}_{offset}\n" for offset in range(count)
        ).encode()
    for relative, data in files.items():
        target = path / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(data)
    subprocess.run(["git", "init", "-q"], cwd=path, check=True)
    subprocess.run(["git", "config", "user.name", "Eq360 Test"], cwd=path, check=True)
    subprocess.run(
        ["git", "config", "user.email", "eq360@example.invalid"], cwd=path, check=True
    )
    subprocess.run(["git", "add", "."], cwd=path, check=True)
    subprocess.run(["git", "commit", "-qm", "fixture"], cwd=path, check=True)
    sha = subprocess.run(
        ["git", "rev-parse", "HEAD"], cwd=path, check=True,
        text=True, stdout=subprocess.PIPE,
    ).stdout.strip()
    return sha, files


def synthetic_archive(path: Path, source_sha: str, files: dict[str, bytes],
                      *, forbidden: bool = False) -> None:
    contract = load(CONTRACT, "eq360_archive_fixture")
    verifier = load(VERIFIER, "eq360_archive_verifier_fixture")
    outputs = {stage: "" for stage in contract.stages()}
    for index, (module, _) in enumerate(contract.MODULES, start=1):
        declarations = contract.PRINT_RE.findall(
            files[f"YangMills/RG/{module}Audit.lean"].decode()
        )
        outputs[f"eq360_complex_physical_{index:02d}_{module.lower()}_audit"] = "".join(
            f"'{name}' depends on axioms: "
            f"[{'sorryAx' if forbidden and index == 1 and offset == 0 else 'propext, Quot.sound'}]\n"
            for offset, name in enumerate(declarations)
        )
    records = [
        {
            "stage": stage, "exit": 0, "seconds": 1.0,
            "output_sha256": hashlib.sha256(output.encode()).hexdigest(),
        }
        for stage, output in outputs.items()
    ]
    evidence = {
        "runner_rev": RUNNER_REV,
        "source_sha": source_sha,
        "source_blobs": {
            relative: hashlib.sha256(data).hexdigest() for relative, data in files.items()
        },
        "mathlib_sha": verifier.EXPECTED_MATHLIB,
        "toolchain_asset_sha256": verifier.EXPECTED_TOOLCHAIN,
        "status": "PASS",
        "records": records,
    }
    root = "hrpoly-eq360-complex-physical-evidence"
    with tarfile.open(path, "w:gz") as archive:
        payload = (json.dumps(evidence, sort_keys=True) + "\n").encode()
        info = tarfile.TarInfo(f"{root}/evidence.json")
        info.size = len(payload)
        archive.addfile(info, io.BytesIO(payload))
        for stage, output in outputs.items():
            payload = output.encode()
            info = tarfile.TarInfo(f"{root}/{stage}.stdout")
            info.size = len(payload)
            archive.addfile(info, io.BytesIO(payload))


def run_verifier(repo: Path, archive: Path, source_sha: str):
    return subprocess.run(
        [
            sys.executable, str(VERIFIER), "--repo", str(repo),
            "--archive", str(archive), "--source-sha", source_sha,
            "--runner-rev", RUNNER_REV,
        ],
        cwd=ROOT, check=False, text=True,
        stdout=subprocess.PIPE, stderr=subprocess.PIPE,
    )


def test_archive_accepts_exact_31_declarations(tmp_path: Path) -> None:
    repo = tmp_path / "repo"
    repo.mkdir()
    source_sha, files = make_repo(repo)
    archive = tmp_path / "evidence.tar.gz"
    synthetic_archive(archive, source_sha, files)
    child = run_verifier(repo, archive, source_sha)
    assert child.returncode == 0, child.stderr
    result = json.loads(child.stdout)
    assert result["status"] == "EQ360_COMPLEX_PHYSICAL_EVIDENCE_OK"
    assert result["expected_declarations"] == 31


def test_archive_rejects_sorry_axiom(tmp_path: Path) -> None:
    repo = tmp_path / "repo"
    repo.mkdir()
    source_sha, files = make_repo(repo)
    archive = tmp_path / "forbidden.tar.gz"
    synthetic_archive(archive, source_sha, files, forbidden=True)
    child = run_verifier(repo, archive, source_sha)
    assert child.returncode != 0
    assert "FORBIDDEN_AXIOM=sorryAx" in child.stderr


def test_packager_does_not_publish_invalid_archive(tmp_path: Path) -> None:
    archive = tmp_path / "invalid.tar.gz"
    archive.write_bytes(b"not a tar")
    destination = tmp_path / "package"
    child = subprocess.run(
        [
            sys.executable, str(PACKAGER), "--archive", str(archive),
            "--destination", str(destination), "--source-sha", "0" * 40,
            "--runner-rev", RUNNER_REV,
        ],
        cwd=ROOT, check=False, text=True,
        stdout=subprocess.PIPE, stderr=subprocess.PIPE,
    )
    assert child.returncode != 0
    assert not destination.exists()
