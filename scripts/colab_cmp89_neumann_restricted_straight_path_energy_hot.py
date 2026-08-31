#!/usr/bin/env python3
"""Hot diagnostic for the restricted Neumann straight-path energy bound."""

from __future__ import annotations

import re
from pathlib import Path
import subprocess
import time


RUNNER_REV = "cmp89-neumann-restricted-straight-path-energy-hot-v1"
SOURCE_SHA = "dfa6ecc286a31f2180a509268f7caa6253e84672"
ROOT = Path("/content/hrpoly-cmp89-neumann-two-level-poincare-composition-cold")
EXPECTED_BLOBS = {
    "YangMills/RG/BalabanCMP89SourceNeumannRestrictedStraightPathEnergy.lean":
        "56e757e207eea92cbd88438e66d5b5e6f0a853a2",
    "YangMills/RG/BalabanCMP89SourceNeumannRestrictedStraightPathEnergyAudit.lean":
        "d7081cfef1135157aae80dd09307e4e967db394c",
}
EXPECTED_DECLARATIONS = {
    "YangMills.RG.cmp89SourceNeumannParallelFineBondAt_injective",
    "YangMills.RG.cmp89SourceNeumannParallelFineBondAt_mem_bonds",
    "YangMills.RG.sum_covariantPathEnergy_cmp99StraightPositivePath_le_neumannRaw",
    "YangMills.RG.sum_cmp89SourceNeumannParallelPathEnergy_le_raw",
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
    manifest = Path(
        "/content/cmp89-neumann-restricted-straight-path-energy-hot-paths.txt"
    )
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
        "YangMills.RG.BalabanCMP89SourceNeumannRestrictedStraightPathEnergy",
    ])
    audit = run("audit", [
        "lake", "env", "lean",
        "YangMills/RG/BalabanCMP89SourceNeumannRestrictedStraightPathEnergyAudit.lean",
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
