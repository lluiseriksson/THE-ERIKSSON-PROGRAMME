#!/usr/bin/env python3
"""Verify durable cold evidence for the remaining Eq. (3.37) derivatives."""

from __future__ import annotations

import argparse
from collections import defaultdict
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import tarfile


ROOT = Path(__file__).resolve().parents[1]
ARCHIVE_UTIL = ROOT / "tmp" / "verify_eq337_complex_ubar_radius_archive.py"
EXPECTED_MATHLIB = "07642720480157414db592fa85b626dafb71355b"
EXPECTED_TOOLCHAIN = "bf3e0a4025e47a0bea9ed907d12dcccd3d3590b1d8ad6c55a915298b01ad9d3e"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
FORBIDDEN = {"sorryAx", "ofReduceBool"}
MODULES = (
    ("BalabanCMP99Eq337PhysicalRealCovariantDerivative", 8),
    ("BalabanCMP99Eq337PhysicalComplexCovariantDerivative", 23),
    ("BalabanCMP99Eq337PhysicalComplexPerturbedBackground", 26),
)
PRINT_RE = re.compile(r"^#print\s+axioms\s+(.+?)\s*$", re.MULTILINE)
OUTPUT_RE = re.compile(
    r"'([^']+)'\s+depends\s+on\s+axioms:\s*\[([^\]]*)\]", re.MULTILINE
)
NO_AXIOM_RE = re.compile(
    r"'([^']+)'\s+does\s+not\s+depend\s+on\s+any\s+axioms", re.MULTILINE
)


def load_util():
    spec = importlib.util.spec_from_file_location("eq337_derivative_archive_util", ARCHIVE_UTIL)
    if spec is None or spec.loader is None:
        raise RuntimeError("EQ337_DERIVATIVE_ARCHIVE_UTIL_LOAD_FAILED")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def git_blob(repo: Path, source_sha: str, relative: str) -> bytes:
    child = subprocess.run(
        ["git", "-c", "safe.directory=*", "cat-file", "blob", f"{source_sha}:{relative}"],
        cwd=repo,
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    if child.returncode != 0:
        raise RuntimeError(
            f"EQ337_DERIVATIVE_GIT_BLOB_FAILED={relative}:"
            + child.stderr.decode(errors="replace")
        )
    return child.stdout


def stages() -> tuple[str, ...]:
    return (
        *(
            stage
            for index, (module, _) in enumerate(MODULES, start=1)
            for stage in (
                f"eq337_covariant_derivative_{index:02d}_{module.lower()}_source",
                f"eq337_covariant_derivative_{index:02d}_{module.lower()}_audit",
            )
        ),
        "eq337_covariant_derivative_root",
    )


def parse_axioms(body: str) -> frozenset[str]:
    return frozenset(name for name in re.split(r"\s*,\s*", body.strip()) if name)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo", type=Path, default=ROOT)
    parser.add_argument("--archive", type=Path, required=True)
    parser.add_argument("--source-sha", required=True)
    parser.add_argument("--runner-rev", required=True)
    parser.add_argument("--json-out", type=Path)
    args = parser.parse_args()
    if re.fullmatch(r"[0-9a-f]{40}", args.source_sha) is None:
        raise RuntimeError("EQ337_DERIVATIVE_SOURCE_SHA_INVALID")

    util = load_util()
    repo = args.repo.resolve()
    archive_path = args.archive.resolve()
    if not archive_path.is_file():
        raise RuntimeError(f"EQ337_DERIVATIVE_ARCHIVE_MISSING={archive_path}")

    with tarfile.open(archive_path, "r:gz") as archive:
        root, files = util.safe_members(archive)
        evidence_name = f"{root}/evidence.json"
        if evidence_name not in files:
            raise RuntimeError("EQ337_DERIVATIVE_EVIDENCE_MISSING")
        evidence = json.loads(util.read_member(archive, files[evidence_name]).decode())
        required = {
            "runner_rev": args.runner_rev,
            "source_sha": args.source_sha,
            "status": "PASS",
            "mathlib_sha": EXPECTED_MATHLIB,
            "toolchain_asset_sha256": EXPECTED_TOOLCHAIN,
        }
        for key, wanted in required.items():
            if evidence.get(key) != wanted:
                raise RuntimeError(f"EQ337_DERIVATIVE_EVIDENCE_{key.upper()}_MISMATCH")

        source_paths = {"YangMillsCore.lean"} | {
            relative
            for module, _ in MODULES
            for relative in (
                f"YangMills/RG/{module}.lean",
                f"YangMills/RG/{module}Audit.lean",
            )
        }
        source_blobs = evidence.get("source_blobs")
        if not isinstance(source_blobs, dict) or set(source_blobs) != source_paths:
            raise RuntimeError("EQ337_DERIVATIVE_SOURCE_BLOB_SCOPE")
        for relative, wanted in source_blobs.items():
            measured = hashlib.sha256(git_blob(repo, args.source_sha, relative)).hexdigest()
            if measured != wanted:
                raise RuntimeError(f"EQ337_DERIVATIVE_SOURCE_BLOB_MISMATCH={relative}")

        records = evidence.get("records")
        if not isinstance(records, list) or not records:
            raise RuntimeError("EQ337_DERIVATIVE_RECORDS_MISSING")
        by_stage: dict[str, dict] = {}
        outputs: dict[str, str] = {}
        for record in records:
            if not isinstance(record, dict) or not isinstance(record.get("stage"), str):
                raise RuntimeError("EQ337_DERIVATIVE_RECORD_INVALID")
            stage = record["stage"]
            if stage in by_stage:
                raise RuntimeError(f"EQ337_DERIVATIVE_DUPLICATE_STAGE={stage}")
            if record.get("exit") != 0:
                raise RuntimeError(f"EQ337_DERIVATIVE_STAGE_EXIT={stage}")
            member_name = f"{root}/{stage}.stdout"
            if member_name not in files:
                raise RuntimeError(f"EQ337_DERIVATIVE_STDOUT_MISSING={stage}")
            output = util.read_member(archive, files[member_name])
            if util.sha256_bytes(output) != record.get("output_sha256"):
                raise RuntimeError(f"EQ337_DERIVATIVE_STDOUT_HASH_MISMATCH={stage}")
            outputs[stage] = output.decode("utf-8")
            by_stage[stage] = record
        expected_members = {evidence_name} | {f"{root}/{stage}.stdout" for stage in by_stage}
        if set(files) != expected_members:
            raise RuntimeError("EQ337_DERIVATIVE_ARCHIVE_MEMBER_SCOPE")
        for stage in stages():
            if stage not in by_stage:
                raise RuntimeError(f"EQ337_DERIVATIVE_REQUIRED_STAGE={stage}")

        expected: list[str] = []
        hashes: dict[str, str] = {}
        declarations_by_module: dict[str, list[str]] = {}
        audit_stages: list[str] = []
        for index, (module, expected_count) in enumerate(MODULES, start=1):
            source_path = f"YangMills/RG/{module}.lean"
            audit_path = f"YangMills/RG/{module}Audit.lean"
            source = git_blob(repo, args.source_sha, source_path)
            audit = git_blob(repo, args.source_sha, audit_path)
            hashes[source_path] = hashlib.sha256(source).hexdigest()
            hashes[audit_path] = hashlib.sha256(audit).hexdigest()
            declarations = PRINT_RE.findall(audit.decode("utf-8"))
            if len(declarations) != expected_count:
                raise RuntimeError(f"EQ337_DERIVATIVE_AUDIT_COUNT={module}:{len(declarations)}")
            declarations_by_module[module] = declarations
            expected.extend(declarations)
            audit_stages.append(
                f"eq337_covariant_derivative_{index:02d}_{module.lower()}_audit"
            )
        if len(expected) != 57 or len(set(expected)) != 57:
            raise RuntimeError("EQ337_DERIVATIVE_DECLARATION_SCOPE")

        audit_text = "\n".join(outputs[stage] for stage in audit_stages)
        compact = re.sub(r"\s+", "", audit_text)
        for forbidden in FORBIDDEN:
            if forbidden in compact:
                raise RuntimeError(f"EQ337_DERIVATIVE_FORBIDDEN_AXIOM={forbidden}")
        observed: dict[str, list[frozenset[str]]] = defaultdict(list)
        for declaration, body in OUTPUT_RE.findall(audit_text):
            observed[declaration].append(parse_axioms(body))
        for declaration in NO_AXIOM_RE.findall(audit_text):
            observed[declaration].append(frozenset())
        missing = [name for name in expected if not observed.get(name)]
        duplicate = {name: len(observed[name]) for name in expected if len(observed[name]) != 1}
        invalid = {
            name: [sorted(block) for block in observed[name] if not block.issubset(ALLOWED)]
            for name in expected
            if any(not block.issubset(ALLOWED) for block in observed[name])
        }
        if missing:
            raise RuntimeError("EQ337_DERIVATIVE_MISSING=" + json.dumps(missing))
        if duplicate:
            raise RuntimeError("EQ337_DERIVATIVE_DUPLICATE=" + json.dumps(duplicate))
        if invalid:
            raise RuntimeError("EQ337_DERIVATIVE_NONSTANDARD=" + json.dumps(invalid))

    result = {
        "status": "EQ337_COVARIANT_DERIVATIVE_EVIDENCE_OK",
        "source_sha": args.source_sha,
        "runner_revision": args.runner_rev,
        "expected_declarations": 57,
        "allowed_axioms": sorted(ALLOWED),
        "stage_seconds": {stage: str(by_stage[stage].get("seconds")) for stage in stages()},
        "boundary_blob_sha256": hashes,
        "declarations_by_module": declarations_by_module,
        "evidence_input_sha256": util.sha256_file(archive_path),
        "transport": "durable-stage-stdout-archive",
    }
    rendered = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.json_out is not None:
        args.json_out.write_text(rendered, encoding="utf-8", newline="\n")
    print(rendered, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
