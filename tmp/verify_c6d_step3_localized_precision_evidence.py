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


RUNNER_REV = "c6d-step3-localized-precision-v5"
NOTEBOOK_CHECKPOINT = "214746e0370af6c348537ac0ab08c2d14392c8ea"
NOTEBOOK_PATH = "scripts/colab_c6d_step3_localized_precision_validation.ipynb"
NOTEBOOK_BLOB_SHA256 = "CB584CFADDFC14A833FDFD342EBF27781A9390C5AFD0AF0140C0124F04E05FF1"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
FORBIDDEN = {"sorryAx", "ofReduceBool"}
BRICKS: tuple[tuple[str, int], ...] = (
    ("BalabanCMP99Eq335PhysicalLaplacianInternalCarrier", 3),
    ("BalabanCMP99Eq335PhysicalRegularityInternalLaplacianBridge", 2),
    ("BalabanCMP99SourceLocalizedRetainedTower", 4),
    ("BalabanCMP99Eq335PhysicalRegularityClassLocalizedPrecision", 6),
)
STAGES = (
    "00_c6d_step3_clm_extensionality_repro",
    "00a_c6d_step3_axiom_readout_coverage",
    "01_cmp99eq335physicallaplacianinternalcarrier_focal",
    "01_cmp99eq335physicallaplacianinternalcarrier_audit",
    "02_cmp99eq335physicalregularityinternallaplacianbridge_focal",
    "02_cmp99eq335physicalregularityinternallaplacianbridge_audit",
    "03_cmp99sourcelocalizedretainedtower_focal",
    "03_cmp99sourcelocalizedretainedtower_audit",
    "04_cmp99eq335physicalregularityclasslocalizedprecision_focal",
    "04_cmp99eq335physicalregularityclasslocalizedprecision_audit",
    "05_c6d_step3_yang_mills_core_root",
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


def notebook_code_source(payload: bytes) -> str:
    notebook = json.loads(payload.decode("utf-8"))
    code_cells = [
        cell for cell in notebook.get("cells", []) if cell.get("cell_type") == "code"
    ]
    if len(code_cells) != 1:
        raise RuntimeError(
            f"C6D_STEP3_NOTEBOOK_CODE_CELL_COUNT={len(code_cells)} WANT=1"
        )
    source = code_cells[0].get("source", "")
    if isinstance(source, list):
        return "".join(str(part) for part in source)
    if isinstance(source, str):
        return source
    raise RuntimeError("C6D_STEP3_NOTEBOOK_CODE_SOURCE_INVALID")


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
    parser.add_argument("--runner-evidence", type=Path)
    parser.add_argument("--axiom-supplement", type=Path)
    parser.add_argument("--json-out", type=Path)
    args = parser.parse_args()

    if (args.runner_evidence is None) != (args.axiom_supplement is None):
        raise RuntimeError("C6D_STEP3_SPLIT_EVIDENCE_REQUIRES_BOTH_INPUTS")

    repo = args.repo.resolve()
    exact_commit(repo, args.source_sha)
    exact_commit(repo, NOTEBOOK_CHECKPOINT)
    evidence_bytes, transcript = notebook_transcript(args.notebook)
    expected_notebook = git_blob(repo, NOTEBOOK_CHECKPOINT, NOTEBOOK_PATH)
    expected_notebook_sha = hashlib.sha256(expected_notebook).hexdigest().upper()
    if expected_notebook_sha != NOTEBOOK_BLOB_SHA256:
        raise RuntimeError(
            f"C6D_STEP3_NOTEBOOK_BLOB_SHA256={expected_notebook_sha} "
            f"WANT={NOTEBOOK_BLOB_SHA256}"
        )
    if notebook_code_source(evidence_bytes) != notebook_code_source(expected_notebook):
        raise RuntimeError("C6D_STEP3_NOTEBOOK_CODE_SOURCE_MISMATCH")
    require_once(transcript, "FINAL_STATUS=PASS")
    require_once(transcript, "LAUNCHER_EXIT=0")
    stage_seconds: dict[str, str] = {}
    axiom_transcript = transcript
    runner_evidence_sha256 = None
    axiom_supplement_sha256 = None
    if args.runner_evidence is not None and args.axiom_supplement is not None:
        runner_evidence_bytes = args.runner_evidence.read_bytes()
        runner_evidence_sha256 = hashlib.sha256(runner_evidence_bytes).hexdigest()
        evidence_markers = re.findall(
            r"(?m)^EVIDENCE_SHA256=([A-Fa-f0-9]+)\s*$", transcript
        )
        if evidence_markers != [runner_evidence_sha256]:
            raise RuntimeError(
                "C6D_STEP3_RUNNER_EVIDENCE_SHA256="
                f"{runner_evidence_sha256} MARKERS={evidence_markers!r}"
            )
        runner_evidence = json.loads(runner_evidence_bytes.decode("utf-8"))
        if runner_evidence.get("status") != "PASS":
            raise RuntimeError("C6D_STEP3_RUNNER_EVIDENCE_STATUS_NOT_PASS")
        if runner_evidence.get("source_sha") != args.source_sha:
            raise RuntimeError("C6D_STEP3_RUNNER_EVIDENCE_SOURCE_MISMATCH")
        if runner_evidence.get("runner_rev") != RUNNER_REV:
            raise RuntimeError("C6D_STEP3_RUNNER_EVIDENCE_REV_MISMATCH")
        records = runner_evidence.get("records")
        if not isinstance(records, list):
            raise RuntimeError("C6D_STEP3_RUNNER_EVIDENCE_RECORDS_INVALID")
        records_by_stage: dict[str, list[dict]] = defaultdict(list)
        for record in records:
            if not isinstance(record, dict) or not isinstance(record.get("stage"), str):
                raise RuntimeError("C6D_STEP3_RUNNER_EVIDENCE_RECORD_INVALID")
            records_by_stage[record["stage"]].append(record)
        for stage in STAGES:
            stage_records = records_by_stage.get(stage, [])
            if len(stage_records) != 1:
                raise RuntimeError(
                    f"C6D_STEP3_RUNNER_RECORD_COUNT={stage}:{len(stage_records)} WANT=1"
                )
            record = stage_records[0]
            if record.get("exit") != 0:
                raise RuntimeError(
                    f"C6D_STEP3_RUNNER_RECORD_EXIT={stage}:{record.get('exit')} WANT=0"
                )
            stage_seconds[stage] = str(record.get("seconds"))
        head_records = records_by_stage.get("head", [])
        expected_head_hash = hashlib.sha256(
            (args.source_sha + "\n").encode("utf-8")
        ).hexdigest()
        if len(head_records) != 1 or head_records[0].get("output_sha256") != expected_head_hash:
            raise RuntimeError("C6D_STEP3_RUNNER_HEAD_RECORD_MISMATCH")

        axiom_supplement_bytes = args.axiom_supplement.read_bytes()
        axiom_supplement_sha256 = hashlib.sha256(axiom_supplement_bytes).hexdigest()
        axiom_transcript = axiom_supplement_bytes.decode("utf-8")
        require_once(axiom_transcript, f"RUNNER_REV={RUNNER_REV}")
        require_once(axiom_transcript, "C6D_STEP3_AXIOM_SUPPLEMENT_STATUS=PASS")
        require_once(
            axiom_transcript,
            "LEAN_AXIOM_READOUT_COVERAGE_OK files=8 declarations=15 readouts=15",
        )
        head_lines = re.findall(
            rf"(?m)^{re.escape(args.source_sha)}\s*$", axiom_transcript
        )
        if len(head_lines) != 1:
            raise RuntimeError(
                f"C6D_STEP3_SUPPLEMENT_HEAD_LINE_COUNT={len(head_lines)} WANT=1"
            )
    else:
        require_once(transcript, f"RUNNER_REV={RUNNER_REV}")
        require_once(
            transcript,
            "LEAN_AXIOM_READOUT_COVERAGE_OK files=8 declarations=15 readouts=15",
        )
        head_lines = re.findall(rf"(?m)^{re.escape(args.source_sha)}\s*$", transcript)
        if len(head_lines) != 1:
            raise RuntimeError(
                f"C6D_STEP3_HEAD_LINE_COUNT={len(head_lines)} WANT=1"
            )
        for stage in STAGES:
            matches = re.findall(
                rf"STAGE={re.escape(stage)} EXIT=(\d+) SECONDS=([0-9.]+)",
                transcript,
            )
            if len(matches) != 1:
                raise RuntimeError(
                    f"C6D_STEP3_STAGE_COUNT={stage}:{len(matches)} WANT=1"
                )
            exit_code, seconds = matches[0]
            if exit_code != "0":
                raise RuntimeError(f"C6D_STEP3_STAGE_EXIT={stage}:{exit_code} WANT=0")
            stage_seconds[stage] = seconds

    compact = re.sub(r"\s+", "", axiom_transcript)
    for forbidden in FORBIDDEN:
        if forbidden in compact:
            raise RuntimeError(f"C6D_STEP3_FORBIDDEN_AXIOM={forbidden}")

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
    if len(expected) != 15 or len(set(expected)) != 15:
        raise RuntimeError(f"C6D_STEP3_EXPECTED_SCOPE={len(expected)}/{len(set(expected))}")

    observed: dict[str, list[frozenset[str]]] = defaultdict(list)
    for declaration, body in OUTPUT_RE.findall(axiom_transcript):
        observed[declaration].append(parse_axiom_set(body))
    for declaration in NO_AXIOM_RE.findall(axiom_transcript):
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
        "notebook_checkpoint": NOTEBOOK_CHECKPOINT,
        "notebook_blob_sha256": NOTEBOOK_BLOB_SHA256,
        "module_count": len(BRICKS),
        "expected_declarations": len(expected),
        "allowed_axioms": sorted(ALLOWED),
        "stage_seconds": stage_seconds,
        "boundary_blob_sha256": boundary_hashes,
        "declarations_by_module": declarations_by_module,
        "evidence_input_sha256": hashlib.sha256(evidence_bytes).hexdigest(),
        "runner_evidence_sha256": runner_evidence_sha256,
        "axiom_supplement_sha256": axiom_supplement_sha256,
    }
    rendered = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.json_out is not None:
        args.json_out.write_text(rendered, encoding="utf-8", newline="\n")
    print(rendered, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
