#!/usr/bin/env python3
"""Exercise the Eq359/C6d cross-evidence verifier without running Lean."""

from __future__ import annotations

import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tarfile
import tempfile


ROOT = Path(__file__).resolve().parents[1]
VERIFY = ROOT / "tmp" / "verify_c6d_eq359_cross_archive.py"
SEAL = ROOT / "tmp" / "seal_c6d_transitive_prevalidation.py"
EQ359_CONTRACT = ROOT / "tmp" / "verify_eq359_real_slice_contract.py"
EQ359_SOURCE = "cd6ff65638f0e09e2533733df2d7176c10714a3a"
C6D_SOURCE = "3738ddb64155a2d85f6d3609d05d5b71114ca498"
EQ359_REV = "eq359-real-slice-promoted-cold-v4"
CROSS_REV = "c6d-eq359-cross-postpass-v1"
MATHLIB = "07642720480157414db592fa85b626dafb71355b"
TOOLCHAIN = "bf3e0a4025e47a0bea9ed907d12dcccd3d3590b1d8ad6c55a915298b01ad9d3e"
ALLOWED = ["Classical.choice", "Quot.sound", "propext"]


def load(path: Path, name: str):
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError("C6D_CROSS_TEST_IMPORT_FAILED=" + str(path))
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


contract = load(EQ359_CONTRACT, "c6d_cross_test_eq359_contract")


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def git_blob(commit: str, relative: str) -> bytes:
    return subprocess.check_output(
        ["git", "-c", "safe.directory=*", "show", f"{commit}:{relative}"],
        cwd=ROOT,
    )


def axiom_output(names: list[str], *, forbidden: bool = False) -> str:
    rows = []
    for index, name in enumerate(names):
        axioms = "sorryAx" if forbidden and index == 0 else (
            "propext, Classical.choice, Quot.sound"
        )
        rows.append(f"'{name}' depends on axioms: [{axioms}]\n")
    return "".join(rows)


def write_archive(path: Path, members: dict[str, bytes]) -> None:
    staging = path.parent / (path.stem + "-staging")
    staging.mkdir()
    for relative, data in members.items():
        target = staging / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(data)
    with tarfile.open(path, "w:gz") as archive:
        for target in sorted(staging.rglob("*")):
            if target.is_file():
                archive.add(target, arcname=target.relative_to(staging).as_posix())


def eq359_fixture(path: Path) -> tuple[dict, str]:
    source_paths = {"YangMillsCore.lean"} | {
        relative
        for module, _ in contract.MODULES
        for relative in (
            f"YangMills/RG/{module}.lean",
            f"YangMills/RG/{module}Audit.lean",
        )
    }
    source_blobs = {
        relative: sha256(git_blob(EQ359_SOURCE, relative))
        for relative in source_paths
    }
    audit_outputs: dict[str, str] = {}
    for index, (module, _count) in enumerate(contract.MODULES, start=1):
        audit = f"YangMills/RG/{module}Audit.lean"
        names = contract.PRINT_RE.findall(git_blob(EQ359_SOURCE, audit).decode())
        stage = f"eq359_real_slice_{index:02d}_{module.lower()}_audit"
        audit_outputs[stage] = axiom_output(names)

    records = []
    members: dict[str, bytes] = {}
    for stage in contract.stages():
        output = audit_outputs.get(stage, "")
        raw = output.encode()
        records.append(
            {
                "stage": stage,
                "exit": 0,
                "seconds": 1.0,
                "output_sha256": sha256(raw),
            }
        )
        members[f"evidence/{stage}.stdout"] = raw
    evidence = {
        "runner_rev": EQ359_REV,
        "source_sha": EQ359_SOURCE,
        "status": "PASS",
        "mathlib_sha": MATHLIB,
        "toolchain_asset_sha256": TOOLCHAIN,
        "source_blobs": source_blobs,
        "records": records,
    }
    evidence_raw = (json.dumps(evidence, sort_keys=True) + "\n").encode()
    members["evidence/evidence.json"] = evidence_raw
    write_archive(path, members)
    root_record = next(
        record for record in records if record["stage"] == "eq359_real_slice_root"
    )
    return root_record, sha256(evidence_raw)


def c6d_fixture(
    path: Path, root_record: dict, eq359_evidence_hash: str, *, forbidden: bool
) -> None:
    manifest = git_blob(C6D_SOURCE, "tmp/C6D-TRANSITIVE-PREVALIDATION-PATHS.txt")
    paths = [
        line.strip()
        for line in manifest.decode().splitlines()
        if line.strip() and not line.lstrip().startswith("#")
    ]
    hashes = {relative: sha256(git_blob(C6D_SOURCE, relative)) for relative in paths}
    declarations = {
        relative: contract.PRINT_RE.findall(git_blob(C6D_SOURCE, relative).decode())
        for relative in paths
        if relative.endswith("Audit.lean")
    }
    records = []
    members: dict[str, bytes] = {}
    for index, (relative, names) in enumerate(sorted(declarations.items()), start=1):
        stage = f"c6d_cross_{index:02d}_{Path(relative).stem.lower()}"
        output = axiom_output(names, forbidden=forbidden and index == 1).encode()
        records.append(
            {
                "stage": stage,
                "path": relative,
                "exit": 0,
                "seconds": 1.0,
                "output_sha256": sha256(output),
            }
        )
        members[f"evidence/{stage}.stdout"] = output
    evidence = {
        "status": "PASS",
        "runner_rev": CROSS_REV,
        "eq359_source_sha": EQ359_SOURCE,
        "c6d_source_sha": C6D_SOURCE,
        "eq359_evidence_sha256": eq359_evidence_hash,
        "eq359_root_record": root_record,
        "boundary_paths": paths,
        "boundary_blob_sha256": hashes,
        "declarations_by_audit": declarations,
        "expected_declarations": 92,
        "allowed_axioms": ALLOWED,
        "records": records,
    }
    members["evidence/evidence.json"] = (
        json.dumps(evidence, sort_keys=True) + "\n"
    ).encode()
    write_archive(path, members)


def run(*args: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [sys.executable, *args],
        cwd=ROOT,
        check=False,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
    )


def main() -> int:
    with tempfile.TemporaryDirectory(prefix="c6d-cross-test-") as temp:
        root = Path(temp)
        eq359 = root / "eq359.tar.gz"
        cross = root / "cross.tar.gz"
        bad = root / "cross-bad.tar.gz"
        output = root / "verified.json"
        root_record, evidence_hash = eq359_fixture(eq359)
        c6d_fixture(cross, root_record, evidence_hash, forbidden=False)
        c6d_fixture(bad, root_record, evidence_hash, forbidden=True)

        good = run(
            str(VERIFY),
            "--repo",
            str(ROOT),
            "--eq359-archive",
            str(eq359),
            "--cross-archive",
            str(cross),
            "--json-out",
            str(output),
        )
        if good.returncode != 0:
            raise RuntimeError("C6D_CROSS_TEST_GOOD_FAILED=" + good.stdout)
        result = json.loads(output.read_text(encoding="utf-8"))
        if result.get("status") != "C6D_EQ359_CROSS_EVIDENCE_OK":
            raise RuntimeError("C6D_CROSS_TEST_GOOD_STATUS")

        rejected = run(
            str(VERIFY),
            "--repo",
            str(ROOT),
            "--eq359-archive",
            str(eq359),
            "--cross-archive",
            str(bad),
        )
        if rejected.returncode == 0 or "FORBIDDEN" not in rejected.stdout:
            raise RuntimeError("C6D_CROSS_TEST_FORBIDDEN_NOT_REJECTED")

        preview = run(
            str(SEAL),
            "--eq359-archive",
            str(eq359),
            "--cross-archive",
            str(cross),
        )
        if preview.returncode != 0:
            raise RuntimeError("C6D_CROSS_TEST_SEAL_PREVIEW_FAILED=" + preview.stdout)
        if "C6D_TRANSITIVE_SEAL_PREVIEW_OK" not in preview.stdout:
            raise RuntimeError("C6D_CROSS_TEST_SEAL_PREVIEW_SENTINEL")

    print("C6D_EQ359_CROSS_ARCHIVE_TEST_OK")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
