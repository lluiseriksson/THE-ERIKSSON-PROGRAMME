#!/usr/bin/env python3
"""Fail-closed verifier for the complex-recursion prerequisite gate."""

from __future__ import annotations

import argparse
from collections import defaultdict
import hashlib
import json
from pathlib import Path
import re
import subprocess


ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
FORBIDDEN = {"sorryAx", "ofReduceBool"}
MODULES = (
    ("BalabanCMP99ComplexInverseRadius", 1),
    ("BalabanCMP99ComplexUbarSmallFieldPropagation", 12),
)
SOURCE_PATHS = (
    "tmp/CMP99ComplexInverseRadius.repro.lean",
    *(path
      for module, _ in MODULES
      for path in (
          f"tmp/{module}.draft.lean",
          f"tmp/{module}Audit.draft.lean",
      )),
)
STAGES = (
    "complex_recursion_prereq_prepare_build_dirs",
    "complex_inverse_radius_repro",
    "complex_recursion_prereq_materialize_dependencies",
    "complex_inverse_radius_source",
    "complex_inverse_radius_audit",
    "complex_ubar_small_field_source",
    "complex_ubar_small_field_audit",
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


def require_sha(value: str, label: str) -> None:
    if re.fullmatch(r"[0-9a-f]{40}", value) is None:
        raise RuntimeError(f"{label}_SHA_FORMAT_INVALID")


def git_blob(repo: Path, source_sha: str, path: str) -> bytes:
    child = subprocess.run(
        ["git", "-c", "safe.directory=*", "cat-file", "blob",
         f"{source_sha}:{path}"],
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
            launchers.append(
                "".join(source) if isinstance(source, list) else str(source)
            )
        for output in cell.get("outputs", []):
            text = output.get("text", "")
            if isinstance(text, list):
                chunks.extend(str(part) for part in text)
            elif isinstance(text, str):
                chunks.append(text)
    if len(launchers) != 1:
        raise RuntimeError(f"LAUNCHER_CELL_COUNT={len(launchers)} WANT=1")
    return payload, "".join(chunks), launchers[0]


def require_once(transcript: str, marker: str) -> None:
    count = transcript.count(marker)
    if count != 1:
        raise RuntimeError(f"MARKER_COUNT={marker!r}:{count} WANT=1")


def parse_axiom_set(body: str) -> frozenset[str]:
    return frozenset(name for name in re.split(r"\s*,\s*", body.strip()) if name)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo", type=Path, required=True)
    parser.add_argument("--notebook", type=Path, required=True)
    parser.add_argument("--source-sha", required=True)
    parser.add_argument("--runner-rev", required=True)
    parser.add_argument("--json-out", type=Path)
    args = parser.parse_args()
    require_sha(args.source_sha, "SOURCE")

    repo = args.repo.resolve()
    evidence_bytes, transcript, launcher = notebook_transcript(
        args.notebook.resolve()
    )
    require_once(transcript, f"RUNNER_REV={args.runner_rev}")
    require_once(transcript, "FINAL_STATUS=PASS")
    require_once(transcript, "LAUNCHER_EXIT=0")
    runner_hashes = re.findall(
        r'(?m)^RUNNER_SHA256\s*=\s*["\']([0-9a-f]{64})["\']\s*$',
        launcher,
    )
    if len(runner_hashes) != 1:
        raise RuntimeError(
            f"LAUNCHER_RUNNER_HASH_COUNT={len(runner_hashes)} WANT=1"
        )
    require_once(
        transcript, f"RUNNER_TRANSPORT_SHA256={runner_hashes[0]}"
    )
    head_matches = re.findall(
        rf'STAGE=head CMD=\["git", "rev-parse", "HEAD"\]\s+'
        rf'{args.source_sha}\s+STAGE=head EXIT=0',
        transcript,
    )
    if len(head_matches) != 1:
        raise RuntimeError(
            f"EXACT_HEAD_MARKER_COUNT={len(head_matches)} WANT=1"
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
            raise RuntimeError(
                f"STAGE_EXIT_COUNT={stage}:{len(matches)} WANT=1"
            )
        exit_code, seconds = matches[0]
        if exit_code != "0":
            raise RuntimeError(f"STAGE_EXIT={stage}:{exit_code} WANT=0")
        stage_seconds[stage] = seconds

    boundary_hashes: dict[str, str] = {}
    for path in SOURCE_PATHS:
        measured = hashlib.sha256(
            git_blob(repo, args.source_sha, path)
        ).hexdigest()
        boundary_hashes[path] = measured
        require_once(transcript, f"SOURCE_BLOB={path} SHA256={measured}")

    expected: list[str] = []
    declarations_by_module: dict[str, list[str]] = {}
    for module, expected_count in MODULES:
        audit_path = f"tmp/{module}Audit.draft.lean"
        declarations = PRINT_RE.findall(
            git_blob(repo, args.source_sha, audit_path).decode("utf-8")
        )
        if len(declarations) != expected_count:
            raise RuntimeError(
                f"AUDIT_DECLARATION_COUNT={audit_path}:{len(declarations)} "
                f"WANT={expected_count}"
            )
        declarations_by_module[module] = declarations
        expected.extend(declarations)
    if len(expected) != 13 or len(set(expected)) != 13:
        raise RuntimeError(
            f"EXPECTED_DECLARATION_SCOPE={len(expected)}/{len(set(expected))}"
        )

    observed: dict[str, list[frozenset[str]]] = defaultdict(list)
    for declaration, body in OUTPUT_RE.findall(transcript):
        observed[declaration].append(parse_axiom_set(body))
    for declaration in NO_AXIOM_RE.findall(transcript):
        observed[declaration].append(frozenset())
    missing = [name for name in expected if not observed.get(name)]
    duplicate = {
        name: len(observed[name]) for name in expected
        if len(observed[name]) != 1
    }
    invalid = {
        name: [sorted(block) for block in observed[name]
               if not block.issubset(ALLOWED)]
        for name in expected
        if any(not block.issubset(ALLOWED) for block in observed[name])
    }
    if missing:
        raise RuntimeError("MISSING_AXIOM_READOUTS=" + json.dumps(missing))
    if duplicate:
        raise RuntimeError(
            "DUPLICATE_AXIOM_READOUTS=" + json.dumps(duplicate, sort_keys=True)
        )
    if invalid:
        raise RuntimeError(
            "NONSTANDARD_AXIOMS=" + json.dumps(invalid, sort_keys=True)
        )

    result = {
        "status": "EQ337_COMPLEX_RECURSION_PREREQ_EVIDENCE_OK",
        "source_sha": args.source_sha,
        "runner_revision": args.runner_rev,
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
