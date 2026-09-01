#!/usr/bin/env python3
"""Retained-runtime repair for the CMP89 three-species split and Eq. (2.48) role gates."""

from __future__ import annotations

import hashlib
import re
import subprocess
import time
from pathlib import Path


RUNNER_REV = "cmp89-neumann-three-species-hot-v2"
SOURCE_SHA = "342c232fbbbb961ea8df3b8620e7681a7b557215"
ROOT = Path("/content/hrpoly-cmp89-neumann-three-species-debug-v1")
MATHLIB_SHA = "07642720480157414db592fa85b626dafb71355b"
SOURCE_BLOBS = {
    "YangMills/RG/BalabanCMP89NeumannPrecisionThreeSpecies.lean":
        "cd3e03aa89809a06f1d0b9e8c233cdef564fd8a9d365f8318beff1606026a8ba",
    "YangMills/RG/BalabanCMP89NeumannPrecisionThreeSpeciesAudit.lean":
        "4404349c64655597ec26bffe759d114671fd9a0a8fdcc710682bdfa2009073e1",
    "YangMills/RG/BalabanCMP89Eq248SameScaleEndpointNoGo.lean":
        "b361186be4126adc69968ddea528840d7ad634c3e037400a7fd2fa58af39b41f",
    "YangMills/RG/BalabanCMP89Eq248SameScaleEndpointNoGoAudit.lean":
        "0da87222b54879c1a5a6df9c5190b54a17239c0cf18074972bc4b9a22d91d36f",
    "YangMills/RG/BalabanCMP89Eq248FineToCoarseGreenQprimeStar.lean":
        "aa35439a5a4a63c36777454ad7e8530636b425fa58cbd4b994621034c07fdcbf",
    "YangMills/RG/BalabanCMP89Eq248FineToCoarseGreenQprimeStarAudit.lean":
        "a051d4b9c12dd323fabfa6de7ba7c50505745d66c83cc4c49739ed68da937ceb",
}
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
EXPECTED_AXIOM_HEADERS = 5


def run(stage: str, command: list[str]) -> str:
    print(f"STAGE={stage} CMD={command!r}", flush=True)
    started = time.perf_counter()
    child = subprocess.run(
        command, cwd=ROOT, text=True, stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT, check=False,
    )
    elapsed = time.perf_counter() - started
    if child.stdout:
        print(child.stdout, end="" if child.stdout.endswith("\n") else "\n")
    print(f"STAGE={stage} EXIT={child.returncode} SECONDS={elapsed:.3f}", flush=True)
    if child.returncode != 0:
        raise RuntimeError(f"STAGE_FAILED={stage} EXIT={child.returncode}")
    return child.stdout


def git_blob(path: str) -> bytes:
    child = subprocess.run(
        ["git", "cat-file", "blob", f"{SOURCE_SHA}:{path}"], cwd=ROOT,
        stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=False,
    )
    if child.returncode != 0:
        raise RuntimeError(f"GIT_BLOB_READ_FAILED={path}")
    return child.stdout


def audit_axioms(output: str) -> None:
    compact = re.sub(r"\s+", "", output)
    for forbidden in ("sorryAx", "ofReduceBool", "Lean.ofReduceBool"):
        if forbidden in compact:
            raise RuntimeError(f"FORBIDDEN_AXIOM={forbidden}")
    blocks = re.findall(r"dependsonaxioms:\[([^\]]*)\]", compact)
    pure = compact.count("doesnotdependonanyaxioms")
    if len(blocks) + pure != EXPECTED_AXIOM_HEADERS:
        raise RuntimeError(
            f"AXIOM_HEADER_COUNT={len(blocks) + pure} "
            f"EXPECTED={EXPECTED_AXIOM_HEADERS} "
            f"NONEMPTY={len(blocks)} EMPTY={pure}"
        )
    for index, body in enumerate(blocks):
        names = {name for name in body.split(",") if name}
        if not names.issubset(ALLOWED_AXIOMS):
            raise RuntimeError(f"AXIOM_SET_{index}={sorted(names)!r}")
        print(f"AXIOM_BLOCK_{index + 1}={','.join(sorted(names))}", flush=True)
    print(f"AXIOM_EMPTY_BLOCKS={pure}", flush=True)


def main() -> int:
    print(f"RUNNER_REV={RUNNER_REV}", flush=True)
    if not ROOT.is_dir():
        raise RuntimeError(f"RETAINED_ROOT_MISSING={ROOT}")
    dirty = run(
        "tracked_clean_gate",
        ["git", "status", "--porcelain", "--untracked-files=no"],
    ).strip()
    if dirty:
        raise RuntimeError(f"TRACKED_WORKTREE_DIRTY={dirty!r}")
    run("fetch_source", ["git", "fetch", "--no-tags", "origin", SOURCE_SHA])
    run("checkout_source", ["git", "checkout", "--detach", SOURCE_SHA])
    if run("head_gate", ["git", "rev-parse", "HEAD"]).strip() != SOURCE_SHA:
        raise RuntimeError("HEAD_MISMATCH")
    pin = run(
        "mathlib_pin_gate",
        ["git", "-C", ".lake/packages/mathlib", "rev-parse", "HEAD"],
    ).strip()
    if pin != MATHLIB_SHA:
        raise RuntimeError(f"MATHLIB_PIN_MISMATCH={pin}")
    for path, expected in SOURCE_BLOBS.items():
        measured = hashlib.sha256(git_blob(path)).hexdigest()
        print(f"SOURCE_BLOB={path} SHA256={measured}", flush=True)
        if measured != expected:
            raise RuntimeError(f"SOURCE_BLOB_HASH_MISMATCH={path}")
    paths = Path("/content/cmp89-neumann-three-species-hot-v2-paths.txt")
    paths.write_text("\n".join(SOURCE_BLOBS) + "\n", encoding="utf-8")
    run(
        "overlay_text_guard",
        ["python3", "scripts/check_lean_overlay_text.py", "--paths-from", str(paths),
         "--require-prevalidation"],
    )
    run(
        "import_prefix_guard",
        ["python3", "scripts/check_lean_import_prefix.py", *SOURCE_BLOBS],
    )
    run(
        "neumann_precision_three_species_focal",
        ["lake", "build", "YangMills.RG.BalabanCMP89NeumannPrecisionThreeSpecies"],
    )
    audit1 = run(
        "neumann_precision_three_species_audit",
        ["lake", "env", "lean",
         "YangMills/RG/BalabanCMP89NeumannPrecisionThreeSpeciesAudit.lean"],
    )
    run(
        "eq248_same_scale_endpoint_nogo_focal",
        ["lake", "build", "YangMills.RG.BalabanCMP89Eq248SameScaleEndpointNoGo"],
    )
    audit2 = run(
        "eq248_same_scale_endpoint_nogo_audit",
        ["lake", "env", "lean",
         "YangMills/RG/BalabanCMP89Eq248SameScaleEndpointNoGoAudit.lean"],
    )
    run(
        "eq248_fine_to_coarse_gqstar_focal",
        ["lake", "build", "YangMills.RG.BalabanCMP89Eq248FineToCoarseGreenQprimeStar"],
    )
    audit3 = run(
        "eq248_fine_to_coarse_gqstar_audit",
        ["lake", "env", "lean",
         "YangMills/RG/BalabanCMP89Eq248FineToCoarseGreenQprimeStarAudit.lean"],
    )
    audit_axioms(audit1 + "\n" + audit2 + "\n" + audit3)
    print("HOT_DIAGNOSTIC_STATUS=PASS", flush=True)
    print("COLD_SEAL_AUTHORITY=0", flush=True)
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except Exception as error:
        print(f"HOT_DIAGNOSTIC_STATUS=FAIL ERROR={error!r}", flush=True)
        raise
