#!/usr/bin/env python3
"""Recover the C6d Step3 axiom readouts lost to Colab output truncation.

Run only in the retained cold clone after the original runner has emitted
``FINAL_STATUS=PASS``.  The script does not rebuild the project: it reruns the
four audit leaves against the already materialized source SHA, validates all
15 readouts, and emits a small self-checking transcript.
"""

from __future__ import annotations

import argparse
from collections import defaultdict
import json
from pathlib import Path
import re
import subprocess


RUNNER_REV = "c6d-step3-localized-precision-v5"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
FORBIDDEN = {"sorryAx", "ofReduceBool"}
BRICKS: tuple[tuple[str, int], ...] = (
    ("BalabanCMP99Eq335PhysicalLaplacianInternalCarrier", 3),
    ("BalabanCMP99Eq335PhysicalRegularityInternalLaplacianBridge", 2),
    ("BalabanCMP99SourceLocalizedRetainedTower", 4),
    ("BalabanCMP99Eq335PhysicalRegularityClassLocalizedPrecision", 6),
)
PRINT_RE = re.compile(r"^#print\s+axioms\s+(.+?)\s*$", re.MULTILINE)
OUTPUT_RE = re.compile(
    r"'([^']+)'\s+depends\s+on\s+axioms:\s*\[([^\]]*)\]", re.MULTILINE
)
NO_AXIOM_RE = re.compile(
    r"'([^']+)'\s+does\s+not\s+depend\s+on\s+any\s+axioms", re.MULTILINE
)


def qualified(name: str) -> str:
    return name if name.startswith("YangMills.RG.") else "YangMills.RG." + name


def parse_axiom_set(body: str) -> frozenset[str]:
    return frozenset(name for name in re.split(r"\s*,\s*", body.strip()) if name)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo", type=Path, required=True)
    parser.add_argument("--source-sha", required=True)
    parser.add_argument("--runner-evidence", type=Path, required=True)
    args = parser.parse_args()

    repo = args.repo.resolve()
    head = subprocess.run(
        ["git", "rev-parse", "HEAD"], cwd=repo, check=True,
        stdout=subprocess.PIPE, text=True
    ).stdout.strip()
    if head != args.source_sha:
        raise RuntimeError(f"C6D_STEP3_SUPPLEMENT_HEAD={head} WANT={args.source_sha}")

    evidence = json.loads(args.runner_evidence.read_text(encoding="utf-8"))
    if evidence.get("status") != "PASS":
        raise RuntimeError("C6D_STEP3_SUPPLEMENT_RUNNER_STATUS_NOT_PASS")
    if evidence.get("source_sha") != args.source_sha:
        raise RuntimeError("C6D_STEP3_SUPPLEMENT_SOURCE_MISMATCH")
    if evidence.get("runner_rev") != RUNNER_REV:
        raise RuntimeError("C6D_STEP3_SUPPLEMENT_RUNNER_REV_MISMATCH")
    records = evidence.get("records")
    if not isinstance(records, list) or any(
        not isinstance(record, dict) or record.get("exit") != 0 for record in records
    ):
        raise RuntimeError("C6D_STEP3_SUPPLEMENT_NONZERO_OR_INVALID_RECORD")

    expected: list[str] = []
    output_chunks: list[str] = []
    for module, expected_count in BRICKS:
        audit = repo / "YangMills" / "RG" / f"{module}Audit.lean"
        declarations = [qualified(name) for name in PRINT_RE.findall(
            audit.read_text(encoding="utf-8")
        )]
        if len(declarations) != expected_count:
            raise RuntimeError(
                f"C6D_STEP3_SUPPLEMENT_DECLARATION_COUNT={module}:"
                f"{len(declarations)} WANT={expected_count}"
            )
        expected.extend(declarations)
        child = subprocess.run(
            ["lake", "env", "lean", str(audit.relative_to(repo))],
            cwd=repo, check=False, stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT, text=True
        )
        if child.returncode != 0:
            raise RuntimeError(
                f"C6D_STEP3_SUPPLEMENT_AUDIT_EXIT={module}:{child.returncode}\n"
                + child.stdout
            )
        output_chunks.append(child.stdout)

    if len(expected) != 15 or len(set(expected)) != 15:
        raise RuntimeError("C6D_STEP3_SUPPLEMENT_EXPECTED_SCOPE_INVALID")
    output = "".join(output_chunks)
    compact = re.sub(r"\s+", "", output)
    for forbidden in FORBIDDEN:
        if forbidden in compact:
            raise RuntimeError(f"C6D_STEP3_SUPPLEMENT_FORBIDDEN_AXIOM={forbidden}")
    observed: dict[str, list[frozenset[str]]] = defaultdict(list)
    for declaration, body in OUTPUT_RE.findall(output):
        observed[declaration].append(parse_axiom_set(body))
    for declaration in NO_AXIOM_RE.findall(output):
        observed[declaration].append(frozenset())
    missing = [name for name in expected if not observed.get(name)]
    duplicate = {name: len(observed[name]) for name in expected if len(observed[name]) != 1}
    invalid = {
        name: [sorted(block) for block in observed[name] if not block.issubset(ALLOWED)]
        for name in expected
        if any(not block.issubset(ALLOWED) for block in observed[name])
    }
    if missing or duplicate or invalid:
        raise RuntimeError(
            "C6D_STEP3_SUPPLEMENT_AXIOM_GATE="
            + json.dumps({"missing": missing, "duplicate": duplicate, "invalid": invalid},
                         sort_keys=True)
        )

    print(f"RUNNER_REV={RUNNER_REV}")
    print(args.source_sha)
    print(output, end="" if output.endswith("\n") else "\n")
    print("LEAN_AXIOM_READOUT_COVERAGE_OK files=8 declarations=15 readouts=15")
    print("C6D_STEP3_AXIOM_SUPPLEMENT_STATUS=PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
