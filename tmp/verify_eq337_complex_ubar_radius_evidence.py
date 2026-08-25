#!/usr/bin/env python3
"""Fail-closed verifier for the Eq. (3.37) complex-Ubar prerequisite gate."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
from collections import defaultdict
from pathlib import Path


SOURCE_SHA = "44a0d11aa78b1b6bce9f5bb7f9ab164e45b90677"
RUNNER_REV = "eq337-complex-ubar-radius-cold-v2"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
FORBIDDEN = {"sorryAx", "ofReduceBool"}
MODULES = (
    ("BalabanCMP99ComplexUbarSpecialLinear", 13),
    ("BalabanCMP99ComplexUbarCoordinateExponent", 8),
    ("BalabanCMP99Eq337PhysicalComplexPerturbedLinkRadius", 5),
    ("BalabanCMP99ComplexFourFactorDeviation", 2),
    ("BalabanCMP99Eq337PhysicalComplexWilsonLineRadius", 10),
    ("BalabanCMP99ComplexLocalizedUbarBackground", 4),
    ("BalabanCMP99Eq337PhysicalComplexUbarDeviationRadius", 10),
)
PREREQUISITE = ("BalabanCMP99Eq337PhysicalComplexPerturbedBackground", 26)
STAGES = (
    "complex_ubar_radius_materialize_prerequisites",
    "complex_ubar_radius_perturbed_background_audit",
    "complex_ubar_radius_prepare_build_dirs",
    *(
        stage
        for index, (module, _) in enumerate(MODULES, start=1)
        for stage in (
            f"complex_ubar_radius_{index:02d}_{module.lower()}_source",
            f"complex_ubar_radius_{index:02d}_{module.lower()}_audit",
        )
    ),
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
            f"GIT_BLOB_READ_FAILED path={path} "
            f"stderr={child.stderr.decode(errors='replace')}"
        )
    return child.stdout


def notebook_transcript(path: Path) -> tuple[bytes, str, str]:
    payload = path.read_bytes()
    notebook = json.loads(payload.decode("utf-8"))
    chunks: list[str] = []
    launchers: list[str] = []
    for cell in notebook.get("cells", []):
        if cell.get("cell_type") == "code":
            source = cell.get("source", "")
            launchers.append("".join(source) if isinstance(source, list) else str(source))
        for output in cell.get("outputs", []):
            text = output.get("text", "")
            if isinstance(text, list):
                chunks.extend(str(part) for part in text)
            elif isinstance(text, str):
                chunks.append(text)
    if len(launchers) != 1:
        raise RuntimeError(f"LAUNCHER_CELL_COUNT={len(launchers)} WANT=1")
    return payload, "".join(chunks), launchers[0]


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
    evidence_bytes, transcript, launcher = notebook_transcript(args.notebook)
    require_once(transcript, f"RUNNER_REV={RUNNER_REV}")
    require_once(transcript, "FINAL_STATUS=PASS")
    require_once(transcript, "LAUNCHER_EXIT=0")
    runner_hashes = re.findall(
        r'(?m)^RUNNER_SHA256\s*=\s*["\']([0-9a-f]{64})["\']\s*$', launcher
    )
    if len(runner_hashes) != 1:
        raise RuntimeError(f"LAUNCHER_RUNNER_HASH_COUNT={len(runner_hashes)} WANT=1")
    require_once(transcript, f"RUNNER_TRANSPORT_SHA256={runner_hashes[0]}")
    head_matches = re.findall(
        rf'STAGE=head CMD=\["git", "rev-parse", "HEAD"\]\s+'
        rf'{SOURCE_SHA}\s+STAGE=head EXIT=0',
        transcript,
    )
    if len(head_matches) != 1:
        raise RuntimeError(f"EXACT_HEAD_MARKER_COUNT={len(head_matches)} WANT=1")
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
    prerequisite_module, prerequisite_count = PREREQUISITE
    prerequisite_source_path = f"YangMills/RG/{prerequisite_module}.lean"
    prerequisite_audit_path = f"YangMills/RG/{prerequisite_module}Audit.lean"
    prerequisite_source_blob = git_blob(repo, prerequisite_source_path)
    prerequisite_audit_blob = git_blob(repo, prerequisite_audit_path)
    boundary_hashes[prerequisite_source_path] = hashlib.sha256(
        prerequisite_source_blob
    ).hexdigest()
    boundary_hashes[prerequisite_audit_path] = hashlib.sha256(
        prerequisite_audit_blob
    ).hexdigest()
    prerequisite_declarations = PRINT_RE.findall(
        prerequisite_audit_blob.decode("utf-8")
    )
    if len(prerequisite_declarations) != prerequisite_count:
        raise RuntimeError(
            f"AUDIT_DECLARATION_COUNT={prerequisite_audit_path}:"
            f"{len(prerequisite_declarations)} WANT={prerequisite_count}"
        )
    declarations_by_module[prerequisite_module] = prerequisite_declarations
    expected.extend(prerequisite_declarations)
    for module, expected_count in MODULES:
        source_path = f"tmp/{module}.draft.lean"
        audit_path = f"tmp/{module}Audit.draft.lean"
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
    if len(expected) != 78 or len(set(expected)) != 78:
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
        "status": "EQ337_COMPLEX_UBAR_RADIUS_EVIDENCE_OK",
        "source_sha": SOURCE_SHA,
        "runner_revision": RUNNER_REV,
        "module_count": 1 + len(MODULES),
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
