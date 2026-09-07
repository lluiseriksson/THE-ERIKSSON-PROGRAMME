#!/usr/bin/env python3
"""Fail-closed verifier for the Eq. (3.37) complex-coordinate cold gate."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
from collections import defaultdict
from pathlib import Path


SOURCE_SHA = "b70735b82216a0ab1cd9a3bd4e195db1426a83fe"
RUNNER_REV = "eq337-complex-coordinate-fresh-v4"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
FORBIDDEN = {"sorryAx", "ofReduceBool"}
MODULES = (
    "BalabanCMP99Eq337PhysicalRealCovariantDerivative",
    "BalabanCMP99Eq337PhysicalComplexCovariantDerivative",
    "BalabanCMP99Eq337PhysicalComplexPerturbedBackground",
)
STAGES = (
    "eq337_axiom_readout_coverage",
    "eq337_real_covariant_derivative_focal",
    "eq337_real_covariant_derivative_audit",
    "eq337_complex_covariant_derivative_focal",
    "eq337_complex_covariant_derivative_audit",
    "eq337_complex_coordinate_background_focal",
    "eq337_complex_coordinate_background_audit",
)
EXPECTED_PER_AUDIT = (8, 23, 26)

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
            f"GIT_BLOB_READ_FAILED path={path} "
            f"stderr={child.stderr.decode(errors='replace')}"
        )
    return child.stdout


def notebook_transcript(path: Path) -> tuple[bytes, str]:
    payload = path.read_bytes()
    notebook = json.loads(payload.decode("utf-8"))
    chunks: list[str] = []
    for cell in notebook.get("cells", []):
        for output in cell.get("outputs", []):
            text = output.get("text", "")
            if isinstance(text, list):
                chunks.extend(str(part) for part in text)
            elif isinstance(text, str):
                chunks.append(text)
    return payload, "".join(chunks)


def parse_axiom_set(body: str) -> frozenset[str]:
    return frozenset(name for name in re.split(r"\s*,\s*", body.strip()) if name)


def require_once(transcript: str, marker: str) -> None:
    count = transcript.count(marker)
    if count != 1:
        raise RuntimeError(f"MARKER_COUNT={marker!r}:{count} WANT=1")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo", type=Path, required=True)
    parser.add_argument("--notebook", type=Path, required=True)
    parser.add_argument("--json-out", type=Path)
    args = parser.parse_args()

    repo = args.repo.resolve()
    evidence_bytes, transcript = notebook_transcript(args.notebook)
    require_once(transcript, f"RUNNER_REV={RUNNER_REV}")
    require_once(transcript, "FINAL_STATUS=PASS")
    require_once(transcript, "LAUNCHER_EXIT=0")
    require_once(
        transcript,
        "LEAN_AXIOM_READOUT_COVERAGE_OK files=6 declarations=57 readouts=57",
    )
    compact = re.sub(r"\s+", "", transcript)
    for forbidden in FORBIDDEN:
        if forbidden in compact:
            raise RuntimeError(f"FORBIDDEN_AXIOM={forbidden}")
    stage_seconds: dict[str, str] = {}
    for stage in STAGES:
        matches = re.findall(
            rf"STAGE={re.escape(stage)} EXIT=(\d+) SECONDS=([0-9.]+)",
            transcript,
        )
        if len(matches) != 1:
            raise RuntimeError(f"STAGE_EXIT_COUNT={stage}:{len(matches)} WANT=1")
        exit_code, seconds = matches[0]
        if exit_code != "0":
            raise RuntimeError(f"STAGE_EXIT={stage}:{exit_code} WANT=0")
        stage_seconds[stage] = seconds

    expected: list[str] = []
    boundary_hashes: dict[str, str] = {}
    declarations_by_module: dict[str, list[str]] = {}
    for module, expected_count in zip(MODULES, EXPECTED_PER_AUDIT, strict=True):
        source_path = f"YangMills/RG/{module}.lean"
        audit_path = f"YangMills/RG/{module}Audit.lean"
        source_blob = git_blob(repo, source_path)
        audit_blob = git_blob(repo, audit_path)
        boundary_hashes[source_path] = hashlib.sha256(source_blob).hexdigest()
        boundary_hashes[audit_path] = hashlib.sha256(audit_blob).hexdigest()
        declarations = PRINT_RE.findall(audit_blob.decode("utf-8"))
        if len(declarations) != expected_count:
            raise RuntimeError(
                f"AUDIT_DECLARATION_COUNT={audit_path}:{len(declarations)} "
                f"WANT={expected_count}"
            )
        declarations_by_module[module] = declarations
        expected.extend(declarations)
    if len(expected) != 57 or len(set(expected)) != 57:
        raise RuntimeError(f"EXPECTED_DECLARATION_SCOPE={len(expected)}/{len(set(expected))}")

    observed: dict[str, list[frozenset[str]]] = defaultdict(list)
    for declaration, body in OUTPUT_RE.findall(transcript):
        observed[declaration].append(parse_axiom_set(body))
    for declaration in NO_AXIOM_RE.findall(transcript):
        observed[declaration].append(frozenset())

    missing = [name for name in expected if not observed.get(name)]
    duplicate = {name: len(observed[name]) for name in expected if len(observed[name]) != 1}
    invalid = {
        name: [sorted(block) for block in observed[name] if not block.issubset(ALLOWED)]
        for name in expected
        if any(not block.issubset(ALLOWED) for block in observed[name])
    }
    if missing:
        raise RuntimeError("MISSING_AXIOM_READOUTS=" + json.dumps(missing))
    if duplicate:
        raise RuntimeError("DUPLICATE_AXIOM_READOUTS=" + json.dumps(duplicate, sort_keys=True))
    if invalid:
        raise RuntimeError("NONSTANDARD_AXIOMS=" + json.dumps(invalid, sort_keys=True))

    result = {
        "status": "EQ337_COMPLEX_COORDINATE_EVIDENCE_OK",
        "source_sha": SOURCE_SHA,
        "runner_revision": RUNNER_REV,
        "module_count": len(MODULES),
        "expected_declarations": len(expected),
        "allowed_axioms": sorted(ALLOWED),
        "stage_seconds": stage_seconds,
        "boundary_blob_sha256": boundary_hashes,
        "declarations_by_module": declarations_by_module,
        "evidence_input_sha256": hashlib.sha256(evidence_bytes).hexdigest(),
    }
    rendered = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.json_out is not None:
        args.json_out.write_text(rendered, encoding="utf-8", newline="\n")
    print(rendered, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
