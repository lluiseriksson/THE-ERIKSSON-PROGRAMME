#!/usr/bin/env python3
"""Fail-closed verifier for the durable Eq. (3.37) Ubar Colab archive."""

from __future__ import annotations

import argparse
from collections import defaultdict
import hashlib
import importlib.util
import json
from pathlib import Path, PurePosixPath
import re
import tarfile


ROOT = Path(__file__).resolve().parents[1]
NOTEBOOK_VERIFIER = ROOT / "tmp" / "verify_eq337_complex_ubar_radius_evidence.py"
EXPECTED_MATHLIB = "07642720480157414db592fa85b626dafb71355b"
EXPECTED_TOOLCHAIN_ASSET = (
    "bf3e0a4025e47a0bea9ed907d12dcccd3d3590b1d8ad6c55a915298b01ad9d3e"
)


def load_contract():
    spec = importlib.util.spec_from_file_location("eq337_ubar_contract", NOTEBOOK_VERIFIER)
    if spec is None or spec.loader is None:
        raise RuntimeError("EQ337_UBAR_ARCHIVE_CONTRACT_LOAD_FAILED")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def safe_members(archive: tarfile.TarFile) -> tuple[str, dict[str, tarfile.TarInfo]]:
    files: dict[str, tarfile.TarInfo] = {}
    roots: set[str] = set()
    for member in archive.getmembers():
        path = PurePosixPath(member.name)
        if path.is_absolute() or ".." in path.parts or not path.parts:
            raise RuntimeError(f"EQ337_UBAR_ARCHIVE_UNSAFE_MEMBER={member.name}")
        roots.add(path.parts[0])
        if member.issym() or member.islnk() or member.isdev():
            raise RuntimeError(f"EQ337_UBAR_ARCHIVE_SPECIAL_MEMBER={member.name}")
        if member.isfile():
            files[member.name] = member
        elif not member.isdir():
            raise RuntimeError(f"EQ337_UBAR_ARCHIVE_MEMBER_TYPE={member.name}")
    if len(roots) != 1:
        raise RuntimeError(f"EQ337_UBAR_ARCHIVE_ROOT_COUNT={len(roots)} WANT=1")
    return next(iter(roots)), files


def read_member(archive: tarfile.TarFile, member: tarfile.TarInfo) -> bytes:
    stream = archive.extractfile(member)
    if stream is None:
        raise RuntimeError(f"EQ337_UBAR_ARCHIVE_MEMBER_READ_FAILED={member.name}")
    return stream.read()


def parse_axiom_set(body: str) -> frozenset[str]:
    return frozenset(name for name in re.split(r"\s*,\s*", body.strip()) if name)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo", type=Path, default=ROOT)
    parser.add_argument("--archive", type=Path, required=True)
    parser.add_argument("--json-out", type=Path)
    args = parser.parse_args()

    contract = load_contract()
    repo = args.repo.resolve()
    archive_path = args.archive.resolve()
    if not archive_path.is_file():
        raise RuntimeError(f"EQ337_UBAR_ARCHIVE_MISSING={archive_path}")

    with tarfile.open(archive_path, "r:gz") as archive:
        root, files = safe_members(archive)
        evidence_name = f"{root}/evidence.json"
        if evidence_name not in files:
            raise RuntimeError("EQ337_UBAR_ARCHIVE_EVIDENCE_JSON_MISSING")
        evidence_bytes = read_member(archive, files[evidence_name])
        evidence = json.loads(evidence_bytes.decode("utf-8"))

        if evidence.get("runner_rev") != contract.RUNNER_REV:
            raise RuntimeError("EQ337_UBAR_ARCHIVE_RUNNER_REV_MISMATCH")
        if evidence.get("source_sha") != contract.SOURCE_SHA:
            raise RuntimeError("EQ337_UBAR_ARCHIVE_SOURCE_SHA_MISMATCH")
        if evidence.get("status") != "PASS":
            raise RuntimeError(f"EQ337_UBAR_ARCHIVE_STATUS={evidence.get('status')}")
        if evidence.get("mathlib_sha") != EXPECTED_MATHLIB:
            raise RuntimeError("EQ337_UBAR_ARCHIVE_MATHLIB_MISMATCH")
        if evidence.get("toolchain_asset_sha256") != EXPECTED_TOOLCHAIN_ASSET:
            raise RuntimeError("EQ337_UBAR_ARCHIVE_TOOLCHAIN_MISMATCH")

        records = evidence.get("records")
        if not isinstance(records, list) or not records:
            raise RuntimeError("EQ337_UBAR_ARCHIVE_RECORDS_MISSING")
        by_stage: dict[str, dict] = {}
        outputs: dict[str, str] = {}
        for record in records:
            if not isinstance(record, dict) or not isinstance(record.get("stage"), str):
                raise RuntimeError("EQ337_UBAR_ARCHIVE_RECORD_INVALID")
            stage = record["stage"]
            if stage in by_stage:
                raise RuntimeError(f"EQ337_UBAR_ARCHIVE_DUPLICATE_STAGE={stage}")
            if record.get("exit") != 0:
                raise RuntimeError(f"EQ337_UBAR_ARCHIVE_STAGE_EXIT={stage}:{record.get('exit')}")
            member_name = f"{root}/{stage}.stdout"
            if member_name not in files:
                raise RuntimeError(f"EQ337_UBAR_ARCHIVE_STDOUT_MISSING={stage}")
            output_bytes = read_member(archive, files[member_name])
            measured = sha256_bytes(output_bytes)
            if measured != record.get("output_sha256"):
                raise RuntimeError(f"EQ337_UBAR_ARCHIVE_STDOUT_HASH_MISMATCH={stage}")
            outputs[stage] = output_bytes.decode("utf-8")
            by_stage[stage] = record

        expected_members = {evidence_name} | {
            f"{root}/{stage}.stdout" for stage in by_stage
        }
        if set(files) != expected_members:
            extra = sorted(set(files) - expected_members)
            missing = sorted(expected_members - set(files))
            raise RuntimeError(
                f"EQ337_UBAR_ARCHIVE_MEMBER_SET extra={extra} missing={missing}"
            )
        for stage in contract.STAGES:
            if stage not in by_stage:
                raise RuntimeError(f"EQ337_UBAR_ARCHIVE_REQUIRED_STAGE_MISSING={stage}")

        source_blobs = evidence.get("source_blobs")
        if not isinstance(source_blobs, dict):
            raise RuntimeError("EQ337_UBAR_ARCHIVE_SOURCE_BLOBS_MISSING")
        expected_source_paths = {"YangMillsCore.lean"} | {
            path
            for module, _ in contract.MODULES
            for path in (
                f"YangMills/RG/{module}.lean",
                f"YangMills/RG/{module}Audit.lean",
            )
        }
        if set(source_blobs) != expected_source_paths:
            raise RuntimeError("EQ337_UBAR_ARCHIVE_SOURCE_BLOB_SCOPE_MISMATCH")
        for relative, wanted in source_blobs.items():
            if not isinstance(relative, str) or not isinstance(wanted, str):
                raise RuntimeError("EQ337_UBAR_ARCHIVE_SOURCE_BLOB_INVALID")
            measured = sha256_bytes(contract.git_blob(repo, relative))
            if measured != wanted:
                raise RuntimeError(f"EQ337_UBAR_ARCHIVE_SOURCE_BLOB_MISMATCH={relative}")

        expected: list[str] = []
        declarations_by_module: dict[str, list[str]] = {}
        audit_stages: list[str] = []
        prereq_module, prereq_count = contract.PREREQUISITE
        prereq_audit = f"YangMills/RG/{prereq_module}Audit.lean"
        prereq_source = f"YangMills/RG/{prereq_module}.lean"
        boundary_hashes = {
            prereq_source: sha256_bytes(contract.git_blob(repo, prereq_source)),
            prereq_audit: sha256_bytes(contract.git_blob(repo, prereq_audit)),
        }
        declarations = [
            contract.resolved_declaration_name(name)
            for name in contract.PRINT_RE.findall(
                contract.git_blob(repo, prereq_audit).decode("utf-8")
            )
        ]
        if len(declarations) != prereq_count:
            raise RuntimeError("EQ337_UBAR_ARCHIVE_PREREQ_DECLARATION_COUNT")
        declarations_by_module[prereq_module] = declarations
        expected.extend(declarations)
        audit_stages.append("complex_ubar_radius_perturbed_background_audit")

        for index, (module, count) in enumerate(contract.MODULES, start=1):
            source = f"YangMills/RG/{module}.lean"
            audit_path = f"YangMills/RG/{module}Audit.lean"
            boundary_hashes[source] = sha256_bytes(contract.git_blob(repo, source))
            boundary_hashes[audit_path] = sha256_bytes(contract.git_blob(repo, audit_path))
            declarations = [
                contract.resolved_declaration_name(name)
                for name in contract.PRINT_RE.findall(
                    contract.git_blob(repo, audit_path).decode("utf-8")
                )
            ]
            if len(declarations) != count:
                raise RuntimeError(f"EQ337_UBAR_ARCHIVE_DECLARATION_COUNT={module}")
            declarations_by_module[module] = declarations
            expected.extend(declarations)
            audit_stages.append(
                f"complex_ubar_radius_{index:02d}_{module.lower()}_audit"
            )

        if len(expected) != 79 or len(set(expected)) != 79:
            raise RuntimeError("EQ337_UBAR_ARCHIVE_EXPECTED_SCOPE_MISMATCH")
        audit_text = "\n".join(outputs[stage] for stage in audit_stages)
        compact = re.sub(r"\s+", "", audit_text)
        for forbidden in contract.FORBIDDEN:
            if forbidden in compact:
                raise RuntimeError(f"FORBIDDEN_AXIOM={forbidden}")
        observed: dict[str, list[frozenset[str]]] = defaultdict(list)
        for declaration, body in contract.OUTPUT_RE.findall(audit_text):
            observed[declaration].append(parse_axiom_set(body))
        for declaration in contract.NO_AXIOM_RE.findall(audit_text):
            observed[declaration].append(frozenset())
        missing = [name for name in expected if not observed.get(name)]
        duplicate = {name: len(observed[name]) for name in expected if len(observed[name]) != 1}
        invalid = {
            name: [sorted(block) for block in observed[name] if not block.issubset(contract.ALLOWED)]
            for name in expected
            if any(not block.issubset(contract.ALLOWED) for block in observed[name])
        }
        if missing:
            raise RuntimeError("MISSING_AXIOM_READOUTS=" + json.dumps(missing))
        if duplicate:
            raise RuntimeError("DUPLICATE_AXIOM_READOUTS=" + json.dumps(duplicate, sort_keys=True))
        if invalid:
            raise RuntimeError("NONSTANDARD_AXIOMS=" + json.dumps(invalid, sort_keys=True))

    result = {
        "status": "EQ337_COMPLEX_UBAR_RADIUS_EVIDENCE_OK",
        "source_sha": contract.SOURCE_SHA,
        "runner_revision": contract.RUNNER_REV,
        "module_count": 1 + len(contract.MODULES),
        "expected_declarations": len(expected),
        "allowed_axioms": sorted(contract.ALLOWED),
        "stage_seconds": {
            stage: str(by_stage[stage].get("seconds")) for stage in contract.STAGES
        },
        "boundary_blob_sha256": boundary_hashes,
        "declarations_by_module": declarations_by_module,
        "evidence_input_sha256": sha256_file(archive_path),
        "transport": "durable-stage-stdout-archive",
    }
    rendered = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.json_out is not None:
        args.json_out.write_text(rendered, encoding="utf-8", newline="\n")
    print(rendered, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
