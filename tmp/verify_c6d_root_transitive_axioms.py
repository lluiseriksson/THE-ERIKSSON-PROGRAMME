#!/usr/bin/env python3
"""Fail-closed audit of the C6d PRE-VALIDATION dependency boundary.

The active cold runner axiom-gates the three C6d declarations directly.  Its
fresh ``YangMillsCore`` stage also builds the audit modules for every
PRE-VALIDATION dependency below C6d and its three immediate Eq. (3.35)
consumers.  This verifier pins the expected ``#print axioms`` declarations to
the immutable source checkpoint and checks the root-stage transcript without
relying on line wrapping.

It is intentionally a post-processing verifier: it neither runs Lean nor
changes the checkout.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
from collections import defaultdict
from pathlib import Path


SOURCE_SHA = "b70735b82216a0ab1cd9a3bd4e195db1426a83fe"
RUNNER_REV = "c6d-localized-retained-tower-cold-v6"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
FORBIDDEN = {"sorryAx", "ofReduceBool"}
PRE_MARKER = (
    "PRE-VALIDATION: source is present in scratch only; no `.olean` has been\n"
    "materialized and no compiler or axiom-oracle verdict exists for this module."
)

MODULES = (
    "BalabanCMP99Eq335PhysicalLocalizedRetainedTower",
    "BalabanCMP99Eq335PhysicalLocalizedRetainedTowerOfSourceRegion",
    "BalabanCMP99Eq335PhysicalRegularityClassLocalizedRetainedTower",
    "BalabanCMP99Eq335PhysicalRegularityLaplacianLocality",
    "BalabanCMP99Eq335PhysicalRetainedNearIdentity",
    "BalabanCMP99Eq335SourceRegionDictionary",
    "BalabanCMP99SourceLocalizedNextBackground",
    "BalabanCMP99SourceLocalizedRetainedTower",
    "BalabanCMP99SourceLocalizedTowerCanonicalExtension",
    "BalabanCMP99SourceLocalizedWeightedQprimeTower",
    "BalabanCMP99SourceRetainedCarrierEndpointGeometry",
    "BalabanCMP99SourceRetainedExactReadCarrier",
    "BalabanCMP99SourceRetainedFineExtension",
    "BalabanCMP99SourceSelectedNextBackgroundLocality",
    "BalabanCMP99SourceTransportedAverageExactReadCarrier",
    "BalabanCMP99SourceUbarExactReadCarrier",
    "BalabanCMP99SourceUbarLocalDeviationBound",
)

PRINT_RE = re.compile(r"^#print\s+axioms\s+(.+?)\s*$", re.MULTILINE)
OUTPUT_RE = re.compile(
    r"'([^']+)'\s+depends\s+on\s+axioms:\s*\[([^\]]*)\]",
    re.MULTILINE,
)
NO_AXIOM_RE = re.compile(
    r"'([^']+)'\s+does\s+not\s+depend\s+on\s+any\s+axioms",
    re.MULTILINE,
)


def git_blob(repo: Path, path: str) -> bytes:
    child = subprocess.run(
        ["git", "-c", "safe.directory=*", "show", f"{SOURCE_SHA}:{path}"],
        cwd=repo,
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    if child.returncode != 0:
        raise RuntimeError(
            f"GIT_BLOB_READ_FAILED path={path} stderr={child.stderr.decode(errors='replace')}"
        )
    return child.stdout


def parse_axiom_set(body: str) -> frozenset[str]:
    return frozenset(name for name in re.split(r"\s*,\s*", body.strip()) if name)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo", type=Path, required=True)
    source = parser.add_mutually_exclusive_group(required=True)
    source.add_argument("--root-log", type=Path)
    source.add_argument("--notebook", type=Path)
    parser.add_argument("--json-out", type=Path)
    args = parser.parse_args()

    repo = args.repo.resolve()
    if args.root_log is not None:
        evidence_bytes = args.root_log.read_bytes()
        root_log = evidence_bytes.decode("utf-8", errors="replace")
    else:
        evidence_bytes = args.notebook.read_bytes()
        notebook = json.loads(evidence_bytes.decode("utf-8"))
        chunks: list[str] = []
        for cell in notebook.get("cells", []):
            for output in cell.get("outputs", []):
                text = output.get("text", "")
                if isinstance(text, list):
                    chunks.extend(str(part) for part in text)
                elif isinstance(text, str):
                    chunks.append(text)
        transcript = "".join(chunks)
        if transcript.count(f"RUNNER_REV={RUNNER_REV}") != 1:
            raise RuntimeError(
                "RUNNER_REV_COUNT="
                f"{transcript.count(f'RUNNER_REV={RUNNER_REV}')} WANT=1"
            )
        coverage_marker = (
            "LEAN_AXIOM_READOUT_COVERAGE_OK "
            "files=34 declarations=92 readouts=92"
        )
        if transcript.count(coverage_marker) != 1:
            raise RuntimeError(
                f"COVERAGE_MARKER_COUNT={transcript.count(coverage_marker)} WANT=1"
            )
        coverage_exit = re.findall(
            r"STAGE=c6d_axiom_readout_coverage EXIT=(\d+) SECONDS=([0-9.]+)",
            transcript,
        )
        if len(coverage_exit) != 1 or coverage_exit[0][0] != "0":
            raise RuntimeError(f"COVERAGE_EXIT_RECORD={coverage_exit!r} WANT_ZERO")
        if transcript.count("FINAL_STATUS=PASS") != 1:
            raise RuntimeError(
                f"FINAL_PASS_COUNT={transcript.count('FINAL_STATUS=PASS')} WANT=1"
            )
        if transcript.count("LAUNCHER_EXIT=0") != 1:
            raise RuntimeError(
                "LAUNCHER_EXIT_ZERO_COUNT="
                f"{transcript.count('LAUNCHER_EXIT=0')} WANT=1"
            )
        start_marker = (
            'STAGE=c6d_localized_retained_tower_root CMD='
            '["lake", "build", "YangMillsCore"]'
        )
        end_marker = "STAGE=c6d_localized_retained_tower_root EXIT="
        start = transcript.find(start_marker)
        end = transcript.find(end_marker, start + len(start_marker))
        if start < 0 or end < 0:
            raise RuntimeError("ROOT_STAGE_NOT_FOUND_IN_NOTEBOOK")
        line_end = transcript.find("\n", end)
        if line_end < 0:
            line_end = len(transcript)
        root_log = transcript[start:line_end]
    root_exit_matches = re.findall(
        r"STAGE=c6d_localized_retained_tower_root EXIT=(\d+) SECONDS=([0-9.]+)",
        root_log,
    )
    if len(root_exit_matches) != 1:
        raise RuntimeError(f"ROOT_EXIT_RECORD_COUNT={len(root_exit_matches)} WANT=1")
    root_exit, root_seconds = root_exit_matches[0]
    if root_exit != "0":
        raise RuntimeError(f"ROOT_EXIT={root_exit} WANT=0")
    compact_log = re.sub(r"\s+", "", root_log)
    for forbidden in FORBIDDEN:
        if forbidden in compact_log:
            raise RuntimeError(f"FORBIDDEN_AXIOM={forbidden}")

    core = git_blob(repo, "YangMillsCore.lean").decode("utf-8")
    expected: list[str] = []
    audit_hashes: dict[str, str] = {}
    boundary_hashes: dict[str, str] = {}
    boundary_paths: list[str] = []
    per_module: dict[str, list[str]] = {}

    for module in MODULES:
        source_path = f"YangMills/RG/{module}.lean"
        audit_path = f"YangMills/RG/{module}Audit.lean"
        boundary_paths.extend((source_path, audit_path))
        expected_import = f"import YangMills.RG.{module}Audit"
        if expected_import not in core:
            raise RuntimeError(f"ROOT_IMPORT_MISSING={expected_import}")
        source_blob = git_blob(repo, source_path)
        audit_blob = git_blob(repo, audit_path)
        for path, blob in ((source_path, source_blob), (audit_path, audit_blob)):
            decoded = blob.decode("utf-8")
            marker_count = decoded.count(PRE_MARKER)
            if marker_count != 1:
                raise RuntimeError(
                    f"PRE_MARKER_COUNT path={path} count={marker_count} WANT=1"
                )
            boundary_hashes[path] = hashlib.sha256(blob).hexdigest()
        audit_hashes[audit_path] = hashlib.sha256(audit_blob).hexdigest()
        declarations = PRINT_RE.findall(audit_blob.decode("utf-8"))
        if not declarations:
            raise RuntimeError(f"NO_AXIOM_READOUTS={audit_path}")
        per_module[module] = declarations
        expected.extend(declarations)

    if len(expected) != 92:
        raise RuntimeError(f"EXPECTED_DECLARATION_COUNT={len(expected)} WANT=92")
    if len(set(expected)) != len(expected):
        raise RuntimeError("DUPLICATE_EXPECTED_DECLARATION")

    observed: dict[str, list[frozenset[str]]] = defaultdict(list)
    for declaration, body in OUTPUT_RE.findall(root_log):
        observed[declaration].append(parse_axiom_set(body))
    for declaration in NO_AXIOM_RE.findall(root_log):
        observed[declaration].append(frozenset())

    missing: list[str] = []
    duplicate: dict[str, int] = {}
    invalid: dict[str, list[list[str]]] = {}
    for declaration in expected:
        blocks = observed.get(declaration, [])
        if not blocks:
            missing.append(declaration)
            continue
        if len(blocks) != 1:
            duplicate[declaration] = len(blocks)
        bad = [sorted(block) for block in blocks if not block.issubset(ALLOWED)]
        if bad:
            invalid[declaration] = bad

    unexpected_forbidden = {
        declaration: [sorted(block) for block in blocks]
        for declaration, blocks in observed.items()
        if any(not block.issubset(ALLOWED) for block in blocks)
    }
    if missing:
        raise RuntimeError("MISSING_AXIOM_READOUTS=" + json.dumps(missing))
    if duplicate:
        raise RuntimeError(
            "DUPLICATE_AXIOM_READOUTS=" + json.dumps(duplicate, sort_keys=True)
        )
    if invalid or unexpected_forbidden:
        raise RuntimeError(
            "NONSTANDARD_AXIOMS="
            + json.dumps({"expected": invalid, "all": unexpected_forbidden}, sort_keys=True)
        )

    result = {
        "status": "C6D_ROOT_TRANSITIVE_AXIOMS_OK",
        "source_sha": SOURCE_SHA,
        "runner_revision": RUNNER_REV,
        "module_count": len(MODULES),
        "expected_declarations": len(expected),
        "observed_declaration_names": len(observed),
        "root_exit": int(root_exit),
        "root_seconds": root_seconds,
        "allowed_axioms": sorted(ALLOWED),
        "audit_blob_sha256": audit_hashes,
        "boundary_paths": boundary_paths,
        "boundary_blob_sha256": boundary_hashes,
        "declarations_by_module": per_module,
        "evidence_input_sha256": hashlib.sha256(evidence_bytes).hexdigest(),
        "root_stage_sha256": hashlib.sha256(root_log.encode()).hexdigest(),
    }
    rendered = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.json_out is not None:
        args.json_out.write_text(rendered, encoding="utf-8", newline="\n")
    print(rendered, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
