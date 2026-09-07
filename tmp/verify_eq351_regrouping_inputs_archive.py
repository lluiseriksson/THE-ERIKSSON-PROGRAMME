#!/usr/bin/env python3
"""Verify durable cold evidence for the canonical Eq. (3.51) inputs."""

from __future__ import annotations

import argparse
from collections import defaultdict
import importlib.util
import json
from pathlib import Path
import re
import tarfile


ROOT = Path(__file__).resolve().parents[1]
CONTRACT_PATH = ROOT / "tmp" / "verify_eq351_regrouping_inputs_contract.py"
ARCHIVE_UTIL_PATH = ROOT / "tmp" / "verify_eq337_complex_ubar_radius_archive.py"
EXPECTED_MATHLIB = "07642720480157414db592fa85b626dafb71355b"
EXPECTED_TOOLCHAIN = (
    "bf3e0a4025e47a0bea9ed907d12dcccd3d3590b1d8ad6c55a915298b01ad9d3e"
)


def load(path: Path, name: str):
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"EQ351_REGROUPING_INPUTS_MODULE_LOAD_FAILED={path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


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
        raise RuntimeError("EQ351_REGROUPING_INPUTS_SOURCE_SHA_INVALID")
    contract = load(CONTRACT_PATH, "eq351_regrouping_inputs_contract")
    util = load(ARCHIVE_UTIL_PATH, "eq351_regrouping_inputs_archive_util")
    archive_path = args.archive.resolve()
    if not archive_path.is_file():
        raise RuntimeError(f"EQ351_REGROUPING_INPUTS_ARCHIVE_MISSING={archive_path}")

    with tarfile.open(archive_path, "r:gz") as archive:
        root, files = util.safe_members(archive)
        evidence_name = f"{root}/evidence.json"
        if evidence_name not in files:
            raise RuntimeError("EQ351_REGROUPING_INPUTS_EVIDENCE_MISSING")
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
                raise RuntimeError(f"EQ351_REGROUPING_INPUTS_{key.upper()}_MISMATCH")

        source_paths = {"YangMillsCore.lean"} | {
            path
            for module, _ in contract.MODULES
            for path in (
                f"YangMills/RG/{module}.lean",
                f"YangMills/RG/{module}Audit.lean",
            )
        }
        source_blobs = evidence.get("source_blobs")
        if not isinstance(source_blobs, dict) or set(source_blobs) != source_paths:
            raise RuntimeError("EQ351_REGROUPING_INPUTS_SOURCE_BLOB_SCOPE")
        boundary_hashes: dict[str, str] = {}
        for relative, wanted in source_blobs.items():
            measured = util.sha256_bytes(
                contract.git_blob(args.repo.resolve(), args.source_sha, relative)
            )
            if measured != wanted:
                raise RuntimeError(
                    f"EQ351_REGROUPING_INPUTS_SOURCE_BLOB_MISMATCH={relative}"
                )
            boundary_hashes[relative] = measured

        records = evidence.get("records")
        if not isinstance(records, list) or not records:
            raise RuntimeError("EQ351_REGROUPING_INPUTS_RECORDS_MISSING")
        by_stage: dict[str, dict] = {}
        outputs: dict[str, str] = {}
        for record in records:
            if not isinstance(record, dict) or not isinstance(record.get("stage"), str):
                raise RuntimeError("EQ351_REGROUPING_INPUTS_RECORD_INVALID")
            stage = record["stage"]
            if stage in by_stage:
                raise RuntimeError(f"EQ351_REGROUPING_INPUTS_DUPLICATE_STAGE={stage}")
            if record.get("exit") != 0:
                raise RuntimeError(f"EQ351_REGROUPING_INPUTS_STAGE_EXIT={stage}")
            member = f"{root}/{stage}.stdout"
            if member not in files:
                raise RuntimeError(f"EQ351_REGROUPING_INPUTS_STDOUT_MISSING={stage}")
            output = util.read_member(archive, files[member])
            if util.sha256_bytes(output) != record.get("output_sha256"):
                raise RuntimeError(
                    f"EQ351_REGROUPING_INPUTS_STDOUT_HASH_MISMATCH={stage}"
                )
            outputs[stage] = output.decode("utf-8")
            by_stage[stage] = record
        if set(files) != {evidence_name} | {f"{root}/{s}.stdout" for s in by_stage}:
            raise RuntimeError("EQ351_REGROUPING_INPUTS_MEMBER_SCOPE")
        for stage in contract.stages():
            if stage not in by_stage:
                raise RuntimeError(f"EQ351_REGROUPING_INPUTS_REQUIRED_STAGE={stage}")

        expected: list[str] = []
        declarations_by_module: dict[str, list[str]] = {}
        audit_stages: list[str] = []
        for index, (module, expected_count) in enumerate(contract.MODULES, start=1):
            audit_path = f"YangMills/RG/{module}Audit.lean"
            declarations = contract.PRINT_RE.findall(
                contract.git_blob(args.repo.resolve(), args.source_sha, audit_path).decode()
            )
            if len(declarations) != expected_count:
                raise RuntimeError(
                    f"EQ351_REGROUPING_INPUTS_AUDIT_COUNT={module}:{len(declarations)}"
                )
            declarations_by_module[module] = declarations
            expected += declarations
            audit_stages.append(
                f"eq351_regrouping_inputs_{index:02d}_{module.lower()}_audit"
            )
        if len(expected) != 19 or len(set(expected)) != 19:
            raise RuntimeError("EQ351_REGROUPING_INPUTS_DECLARATION_SCOPE")

        audit_text = "\n".join(outputs[stage] for stage in audit_stages)
        compact = re.sub(r"\s+", "", audit_text)
        for forbidden in contract.FORBIDDEN:
            if forbidden in compact:
                raise RuntimeError(
                    f"EQ351_REGROUPING_INPUTS_FORBIDDEN_AXIOM={forbidden}"
                )
        observed: dict[str, list[frozenset[str]]] = defaultdict(list)
        for declaration, body in contract.OUTPUT_RE.findall(audit_text):
            observed[declaration].append(parse_axioms(body))
        for declaration in contract.NO_AXIOM_RE.findall(audit_text):
            observed[declaration].append(frozenset())
        missing = [name for name in expected if not observed.get(name)]
        duplicate = {
            name: len(observed[name])
            for name in expected
            if len(observed[name]) != 1
        }
        invalid = {
            name: [
                sorted(block)
                for block in observed[name]
                if not block.issubset(contract.ALLOWED)
            ]
            for name in expected
            if any(not block.issubset(contract.ALLOWED) for block in observed[name])
        }
        if missing:
            raise RuntimeError("EQ351_REGROUPING_INPUTS_MISSING=" + json.dumps(missing))
        if duplicate:
            raise RuntimeError(
                "EQ351_REGROUPING_INPUTS_DUPLICATE="
                + json.dumps(duplicate, sort_keys=True)
            )
        if invalid:
            raise RuntimeError(
                "EQ351_REGROUPING_INPUTS_NONSTANDARD="
                + json.dumps(invalid, sort_keys=True)
            )

    result = {
        "status": "EQ351_REGROUPING_INPUTS_EVIDENCE_OK",
        "source_sha": args.source_sha,
        "runner_revision": args.runner_rev,
        "expected_declarations": len(expected),
        "allowed_axioms": sorted(contract.ALLOWED),
        "stage_seconds": {
            stage: str(by_stage[stage].get("seconds")) for stage in contract.stages()
        },
        "boundary_blob_sha256": boundary_hashes,
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
