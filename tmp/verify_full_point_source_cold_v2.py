#!/usr/bin/env python3
"""Fail-closed verifier for the full point-source cold-v2 Colab seal."""

from __future__ import annotations

import argparse
import hashlib
import io
import json
import re
import tarfile
from pathlib import Path


SOURCE = "a819e5074a9f58fb7ae7b93c6369a186956419a2"
RUNNER = "cmp99-full-point-source-solution-cold-v2"
STAGES = [
    "full_complex_precision_fibre_action_focal",
    "full_complex_precision_fibre_action_audit",
    "full_point_source_solution_focal",
    "full_point_source_solution_audit",
]
EXPECTED = {
    "YangMills.RG.cmp99SourceFlatFixedCoarseFibreCoefficientExtension_apply",
    "YangMills.RG.cmp99FlatPhysicalFibreDFT_fixedCoarseFibreFourierSynthesis",
    "YangMills.RG.cmp99SourceFlatFixedCoarseFibreFourierSynthesis_eq_sum",
    "YangMills.RG.cmp99SourceFlatFullComplexPrecisionAction_add",
    "YangMills.RG.cmp99SourceFlatFullComplexPrecisionAction_finset_sum",
    "YangMills.RG.cmp99FlatPhysicalFibreDFT_sourceFlatFullComplexPrecision_fixedCoarseFibre",
    "YangMills.RG.cmp99SourceFlatFullComplexPrecisionPointSourceFibreCoefficients",
    "YangMills.RG.cmp99SourceFlatFullComplexPrecisionPointSourceFibreSolution",
    "YangMills.RG.cmp99FlatPhysicalFibreDFT_sourceFlatFullComplexPrecision_fixedCoarseFibreSolution_eq_zero_of_coarseAlias_ne",
    "YangMills.RG.cmp99FlatPhysicalFibreDFT_sourceFlatFullComplexPrecision_pointSourceFibreSolution",
    "YangMills.RG.cmp99SourceFlatFullComplexPrecisionPointSourceSolution",
    "YangMills.RG.cmp99SourceFlatFullComplexPrecisionAction_pointSourceSolution",
}
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("archive", type=Path)
    parser.add_argument("notebook", type=Path)
    args = parser.parse_args()

    with tarfile.open(args.archive, "r:gz") as archive:
        members = [m for m in archive.getmembers() if m.name.endswith("/evidence.json")]
        if len(members) != 1:
            raise SystemExit(f"EVIDENCE_JSON_COUNT={len(members)}")
        stream = archive.extractfile(members[0])
        if stream is None:
            raise SystemExit("EVIDENCE_JSON_UNREADABLE")
        evidence = json.load(io.TextIOWrapper(stream, encoding="utf-8"))

    if evidence.get("status") != "PASS":
        raise SystemExit(f"STATUS={evidence.get('status')!r}")
    if evidence.get("source_sha") != SOURCE:
        raise SystemExit(f"SOURCE_SHA={evidence.get('source_sha')!r}")
    if evidence.get("runner_rev") != RUNNER:
        raise SystemExit(f"RUNNER_REV={evidence.get('runner_rev')!r}")
    records = {r["stage"]: r for r in evidence.get("records", [])}
    for stage in STAGES:
        if stage not in records or records[stage].get("exit") != 0:
            raise SystemExit(f"STAGE_NOT_GREEN={stage}:{records.get(stage)!r}")

    notebook = json.loads(args.notebook.read_text(encoding="utf-8"))
    code_cells = [c for c in notebook.get("cells", []) if c.get("cell_type") == "code"]
    if len(code_cells) != 1 or code_cells[0].get("execution_count") != 1:
        raise SystemExit(
            f"NOTEBOOK_EXECUTION_SHAPE={len(code_cells)}:"
            f"{[c.get('execution_count') for c in code_cells]}"
        )
    output_parts: list[str] = []
    for output in code_cells[0].get("outputs", []):
        text = output.get("text")
        if isinstance(text, list):
            output_parts.extend(text)
        elif isinstance(text, str):
            output_parts.append(text)
        traceback = output.get("traceback")
        if traceback:
            output_parts.extend(traceback)
    raw = "".join(output_parts)
    compact = re.sub(r"\s+", "", raw)
    if compact.count("FINAL_STATUS=PASS") != 1 or "FINAL_STATUS=FAIL" in compact:
        raise SystemExit("FINAL_STATUS_GATE_FAILED")
    if "sorryAx" in compact or "ofReduceBool" in compact:
        raise SystemExit("FORBIDDEN_AXIOM")
    gates = re.findall(r"AXIOM_GATE=([^\s]+)\s+AXIOMS=([^\r\n]*)", raw)
    names = {name.strip() for name, _ in gates}
    if names != EXPECTED:
        raise SystemExit(f"AXIOM_DECLARATIONS={sorted(names)!r}")
    for name, body in gates:
        axioms = {item for item in body.strip().split(",") if item}
        if not axioms.issubset(ALLOWED):
            raise SystemExit(f"AXIOM_SET={name}:{sorted(axioms)!r}")

    print("FULL_POINT_SOURCE_COLD_V2_EVIDENCE_OK")
    print(f"archive_sha256={sha256(args.archive).upper()}")
    print(f"notebook_sha256={sha256(args.notebook).upper()}")
    for stage in STAGES:
        print(f"stage={stage} seconds={records[stage]['seconds']:.3f} exit=0")


if __name__ == "__main__":
    main()
