#!/usr/bin/env python3
"""Fail-closed verifier for a C6d Step3 executed Colab notebook."""

from __future__ import annotations

import argparse
from collections import defaultdict
import hashlib
import json
from pathlib import Path
import re
import subprocess


RUNNER_REV = "c6d-step3-localized-precision-v3"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
FORBIDDEN = {"sorryAx", "ofReduceBool"}
BRICKS: tuple[tuple[str, int], ...] = (
    ("BalabanCMP99Eq335PhysicalLaplacianInternalCarrier", 3),
    ("BalabanCMP99Eq335PhysicalRegularityInternalLaplacianBridge", 2),
    ("BalabanCMP99Eq335PhysicalRegularityClassLocalizedPrecision", 6),
)
STAGES = (
    "00_c6d_step3_clm_extensionality_repro",
    "00a_c6d_step3_axiom_readout_coverage",
    "01_cmp99eq335physicallaplacianinternalcarrier_focal",
    "01_cmp99eq335physicallaplacianinternalcarrier_audit",
    "02_cmp99eq335physicalregularityinternallaplacianbridge_focal",
    "02_cmp99eq335physicalregularityinternallaplacianbridge_audit",
    "03_cmp99eq335physicalregularityclasslocalizedprecision_focal",
    "03_cmp99eq335physicalregularityclasslocalizedprecision_audit",
    "04_c6d_step3_yang_mills_core_root",
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


def exact_commit(repo: Path, source_sha: str) -> None:
    if re.fullmatch(r"[0-9a-f]{40}", source_sha) is None:
        raise RuntimeError("C6D_STEP3_SOURCE_SHA_FORMAT_INVALID")
    child = subprocess.run(
        ["git", "-c", "safe.directory=*", "rev-parse", f"{source_sha}^{{commit}}"],
        cwd=repo,
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
    )
    if child.returncode != 0 or child.stdout.strip() != source_sha:
        raise RuntimeError(
            "C6D_STEP3_SOURCE_COMMIT_MISMATCH="
            + child.stdout.strip()
            + "/"
            + child.stderr.strip()
        )


def git_blob(repo: Path, source_sha: str, path: str) -> bytes:
    child = subprocess.run(
        ["git", "-c", "safe.directory=*", "show", f"{source_sha}:{path}"],
        cwd=repo,
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    if child.returncode != 0:
        raise RuntimeError(
            f"C6D_STEP3_GIT_BLOB_READ_FAILED={path}/"
            + child.stderr.decode(errors="replace")
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
        raise RuntimeError(f"C6D_STEP3_MARKER_COUNT={marker!r}:{count} WANT=1")


def qualified(name: str) -> str:
    return name if name.startswith("YangMills.RG.") else "YangMills.RG." + name


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo", type=Path, required=True)
    parser.add_argument("--source-sha", required=True)
    parser.add_argument("--notebook", type=Path, required=True)
    parser.add_argument("--json-out", type=Path)
    args = parser.parse_args()

    repo = args.repo.resolve()
    exact_commit(repo, args.source_sha)
    evidence_bytes, transcript = notebook_transcript(args.notebook)
    require_once(transcript, f"RUNNER_REV={RUNNER_REV}")
    require_once(transcript, "FINAL_STATUS=PASS")
    require_once(transcript, "LAUNCHER_EXIT=0")
    require_once(
        transcript,
        "LEAN_AXIOM_READOUT_COVERAGE_OK files=6 declarations=11 readouts=11",
    )
    head_lines = re.findall(rf"(?m)^{re.escape(args.source_sha)}\s*$", transcript)
    if len(head_lines) != 1:
        raise RuntimeError(
            f"C6D_STEP3_HEAD_LINE_COUNT={len(head_lines)} WANT=1"
        )
    compact = re.sub(r"\s+", "", transcript)
    for forbidden in FORBIDDEN:
        if forbidden in compact:
            raise RuntimeError(f"C6D_STEP3_FORBIDDEN_AXIOM={forbidden}")

    stage_seconds: dict[str, str] = {}
    for stage in STAGES:
        matches = re.findall(
            rf"STAGE={re.escape(stage)} EXIT=(\d+) SECONDS=([0-9.]+)",
            transcript,
        )
        if len(matches) != 1:
            raise RuntimeError(f"C6D_STEP3_STAGE_COUNT={stage}:{len(matches)} WANT=1")
        exit_code, seconds = matches[0]
        if exit_code != "0":
            raise RuntimeError(f"C6D_STEP3_STAGE_EXIT={stage}:{exit_code} WANT=0")
        stage_seconds[stage] = seconds

    expected: list[str] = []
    boundary_hashes: dict[str, str] = {}
    declarations_by_module: dict[str, list[str]] = {}
    for module, expected_count in BRICKS:
        source_path = f"YangMills/RG/{module}.lean"
        audit_path = f"YangMills/RG/{module}Audit.lean"
        source_blob = git_blob(repo, args.source_sha, source_path)
        audit_blob = git_blob(repo, args.source_sha, audit_path)
        boundary_hashes[source_path] = hashlib.sha256(source_blob).hexdigest()
        boundary_hashes[audit_path] = hashlib.sha256(audit_blob).hexdigest()
        declarations = [qualified(name) for name in PRINT_RE.findall(audit_blob.decode("utf-8"))]
        if len(declarations) != expected_count:
            raise RuntimeError(
                f"C6D_STEP3_AUDIT_DECLARATION_COUNT={audit_path}:"
                f"{len(declarations)} WANT={expected_count}"
            )
        declarations_by_module[module] = declarations
        expected.extend(declarations)
    if len(expected) != 11 or len(set(expected)) != 11:
        raise RuntimeError(f"C6D_STEP3_EXPECTED_SCOPE={len(expected)}/{len(set(expected))}")

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
        raise RuntimeError("C6D_STEP3_MISSING_READOUTS=" + json.dumps(missing))
    if duplicate:
        raise RuntimeError(
            "C6D_STEP3_DUPLICATE_READOUTS=" + json.dumps(duplicate, sort_keys=True)
        )
    if invalid:
        raise RuntimeError(
            "C6D_STEP3_NONSTANDARD_AXIOMS=" + json.dumps(invalid, sort_keys=True)
        )

    result = {
        "status": "C6D_STEP3_LOCALIZED_PRECISION_EVIDENCE_OK",
        "source_sha": args.source_sha,
        "runner_revision": RUNNER_REV,
        "module_count": len(BRICKS),
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
