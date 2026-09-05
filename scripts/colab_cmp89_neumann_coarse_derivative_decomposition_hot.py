#!/usr/bin/env python3
"""Hot diagnostic for the exact regional Neumann coarse-derivative split."""

from __future__ import annotations

import re
from pathlib import Path
import subprocess
import time


RUNNER_REV = "cmp89-neumann-coarse-derivative-decomposition-hot-v1"
SOURCE_SHA = "138b265386fcdc2216746737ef4dee5f4da87f27"
ROOT = Path("/content/hrpoly-cmp89-neumann-two-level-poincare-composition-cold")
EXPECTED_BLOBS = {
    "YangMills/RG/BalabanCMP89SourceNeumannCoarseDerivativeDecomposition.lean":
        "7c862efee2405b4559a569504141adcf139c3b83",
    "YangMills/RG/BalabanCMP89SourceNeumannCoarseDerivativeDecompositionAudit.lean":
        "eba78bae6083d1a74909e587c44bf6fb9086ded6",
}
EXPECTED_DECLARATIONS = {
    "YangMills.RG.cmp99SourceParallelAverageDefectCochain",
    "YangMills.RG.cmp99SourceParallelAverageDefectCochain_apply",
    "YangMills.RG.restrictOne_covariantD0_cmp99FullSourceBlockAverage_eq_defect_add_remainder",
    "YangMills.RG.cmp89SourceNeumannRegionalCovariantD0CLM_oneScaleAverage_eq_twoSpecies",
}
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def run(stage: str, command: list[str]) -> str:
    print("STAGE=" + stage + " CMD=" + repr(command), flush=True)
    started = time.perf_counter()
    child = subprocess.run(
        command, cwd=ROOT, text=True,
        stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
    )
    elapsed = time.perf_counter() - started
    print(child.stdout, end="" if child.stdout.endswith("\n") else "\n", flush=True)
    print(
        "STAGE=" + stage + " EXIT=" + str(child.returncode)
        + " SECONDS=" + f"{elapsed:.3f}", flush=True,
    )
    if child.returncode != 0:
        raise RuntimeError("STAGE_FAILED=" + stage)
    return child.stdout


def main() -> int:
    print("RUNNER_REV=" + RUNNER_REV, flush=True)
    if not ROOT.is_dir():
        raise RuntimeError("RETAINED_ROOT_MISSING=" + str(ROOT))
    run("fetch", ["git", "fetch", "--no-tags", "origin", SOURCE_SHA])
    run("checkout", ["git", "checkout", "--detach", SOURCE_SHA])
    head = run("head", ["git", "rev-parse", "HEAD"]).strip()
    if head != SOURCE_SHA:
        raise RuntimeError("HEAD_MISMATCH=" + head)
    for relative, expected in EXPECTED_BLOBS.items():
        actual = run(
            "blob_" + Path(relative).stem,
            ["git", "hash-object", relative],
        ).strip()
        print("SOURCE_BLOB=" + relative + " OID=" + actual, flush=True)
        if actual != expected:
            raise RuntimeError("SOURCE_BLOB_MISMATCH=" + relative)
    manifest = Path("/content/cmp89-neumann-coarse-derivative-decomposition-hot-paths.txt")
    manifest.write_text("\n".join(EXPECTED_BLOBS) + "\n", encoding="utf-8")
    run("overlay_text_guard", [
        "python3", "scripts/check_lean_overlay_text.py",
        "--paths-from", str(manifest), "--require-prevalidation",
    ])
    run("import_prefix_guard", [
        "python3", "scripts/check_lean_import_prefix.py", *EXPECTED_BLOBS,
    ])
    run("focal", [
        "lake", "build",
        "YangMills.RG.BalabanCMP89SourceNeumannCoarseDerivativeDecomposition",
    ])
    audit = run("audit", [
        "lake", "env", "lean",
        "YangMills/RG/BalabanCMP89SourceNeumannCoarseDerivativeDecompositionAudit.lean",
    ])
    compact = re.sub(r"\s+", "", audit)
    for forbidden in ("sorryAx", "ofReduceBool", "Lean.ofReduceBool"):
        if forbidden in compact:
            raise RuntimeError("FORBIDDEN_AXIOM=" + forbidden)
    blocks = re.findall(r"'([^']+)'dependsonaxioms:\[([^\]]*)\]", compact)
    names = {name for name, _ in blocks}
    if len(blocks) != len(EXPECTED_DECLARATIONS) or names != EXPECTED_DECLARATIONS:
        raise RuntimeError("AXIOM_DECLARATION_MISMATCH=" + repr(blocks))
    for name, raw_axioms in blocks:
        axioms = {item for item in raw_axioms.split(",") if item}
        if not axioms.issubset(ALLOWED_AXIOMS):
            raise RuntimeError("AXIOM_SET=" + name + ":" + repr(sorted(axioms)))
        print(
            "AXIOM_GATE=" + name + " AXIOMS=" + ",".join(sorted(axioms)),
            flush=True,
        )
    print("HOT_FINAL_STATUS=PASS", flush=True)
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except Exception as error:
        print("ERROR=" + repr(error), flush=True)
        print("HOT_FINAL_STATUS=FAIL", flush=True)
        raise
