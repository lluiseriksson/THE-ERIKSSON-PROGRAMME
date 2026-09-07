#!/usr/bin/env python3
"""Retained-runtime diagnostic for the canonical CMP89 rectangle specializations.

This is not cold-seal authority.  It reuses the verified dependency graph of
the preceding rectangle-lift seal, checks out the exact PRE-VALIDATION source,
and stops at the first focal or axiom-audit error.
"""

from __future__ import annotations

import hashlib
import re
import subprocess
import time
from pathlib import Path


RUNNER_REV = "cmp89-neumann-rectangle-specialization-hot-v1"
SOURCE_SHA = "ed6d96d8e061ba141c263c42847352a34db310fa"
ROOT = Path("/content/hrpoly-cmp89-neumann-rectangle-lift-cold")
SOURCE_BLOBS = {
    "YangMills/RG/BalabanCMP89SourceFlatGeneratedFiniteDepthCanonicalNeumannRectangleReflectionRepresentation.lean":
        "f3cc06c780ac08dab545646303cc24abb4a4f3b6d611eb090f8975333178bb7f",
    "YangMills/RG/BalabanCMP89SourceFlatGeneratedFiniteDepthCanonicalNeumannRectangleReflectionRepresentationAudit.lean":
        "ab96c9e06c46bfcb98bfc9b55d73bcb3dac6f2956ebc04b8058da0371cf3583b",
    "YangMills/RG/BalabanCMP89SourceFlatGeneratedFiniteDepthCanonicalNeumannRectanglePhysicalReflectionRepresentation.lean":
        "773c1940c132dc0f298061a9a91b79061724907a341809e5ae8f5774aa14f9ae",
    "YangMills/RG/BalabanCMP89SourceFlatGeneratedFiniteDepthCanonicalNeumannRectanglePhysicalReflectionRepresentationAudit.lean":
        "9c28fc57c3c33c3acdbf968f7b64b03a2dff102a46050e6baa7713356a888422",
}
EXPECTED_DECLARATIONS = {
    "YangMills.RG.CMP89SourceFlatGeneratedFiniteDepthCanonicalNeumannRectangleReflectionRepresentation",
    "YangMills.RG.cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannRectangleReflectionRepresentation_eq_series",
    "YangMills.RG.cmp89Eq248PhysicalFullLatticeGreenRealAction",
    "YangMills.RG.CMP89SourceFlatGeneratedFiniteDepthCanonicalNeumannRectanglePhysicalReflectionRepresentation",
    "YangMills.RG.cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannRectanglePhysicalReflectionRepresentation_eq_series",
}
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
FORBIDDEN_TOKENS = {"sorryAx", "ofReduceBool", "Lean.ofReduceBool"}


def run(stage: str, command: list[str], *, cwd: Path = ROOT) -> str:
    print(f"STAGE={stage} CMD={command!r}", flush=True)
    started = time.perf_counter()
    child = subprocess.run(
        command,
        cwd=cwd,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        check=False,
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
        ["git", "cat-file", "blob", f"{SOURCE_SHA}:{path}"],
        cwd=ROOT,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    if child.returncode != 0:
        raise RuntimeError(
            f"GIT_BLOB_READ_FAILED={path} STDERR={child.stderr.decode(errors='replace')!r}"
        )
    return child.stdout


def audit_axioms(output: str) -> None:
    compact = re.sub(r"\s+", "", output)
    for token in FORBIDDEN_TOKENS:
        if token in compact:
            raise RuntimeError(f"FORBIDDEN_AXIOM={token}")
    blocks = re.findall(r"'([^']+)'dependsonaxioms:\[([^\]]*)\]", compact)
    found = {name: body for name, body in blocks}
    if set(found) != EXPECTED_DECLARATIONS:
        raise RuntimeError(
            "AXIOM_DECLARATIONS_MISMATCH="
            + repr({"found": sorted(found), "expected": sorted(EXPECTED_DECLARATIONS)})
        )
    for name in sorted(EXPECTED_DECLARATIONS):
        axioms = {item for item in found[name].split(",") if item}
        if not axioms.issubset(ALLOWED_AXIOMS):
            raise RuntimeError(f"AXIOM_SET={name}:{sorted(axioms)!r}")
        print(f"AXIOM_GATE={name} AXIOMS={','.join(sorted(axioms))}", flush=True)


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
    head = run("head_gate", ["git", "rev-parse", "HEAD"]).strip()
    if head != SOURCE_SHA:
        raise RuntimeError(f"HEAD_MISMATCH={head}")
    mathlib = run(
        "mathlib_pin_gate",
        ["git", "-C", ".lake/packages/mathlib", "rev-parse", "HEAD"],
    ).strip()
    if mathlib != "07642720480157414db592fa85b626dafb71355b":
        raise RuntimeError(f"MATHLIB_PIN_MISMATCH={mathlib}")
    for path, expected in SOURCE_BLOBS.items():
        measured = hashlib.sha256(git_blob(path)).hexdigest()
        print(f"SOURCE_BLOB={path} SHA256={measured}", flush=True)
        if measured != expected:
            raise RuntimeError(f"SOURCE_BLOB_HASH_MISMATCH={path}")
    paths = "/content/cmp89-neumann-rectangle-specialization-hot-paths.txt"
    Path(paths).write_text("\n".join(SOURCE_BLOBS) + "\n", encoding="utf-8")
    run(
        "overlay_text_guard",
        ["python3", "scripts/check_lean_overlay_text.py", "--paths-from", paths,
         "--require-prevalidation"],
    )
    run(
        "import_prefix_guard",
        ["python3", "scripts/check_lean_import_prefix.py", *SOURCE_BLOBS],
    )
    run(
        "cmp89_neumann_rectangle_specialization_focal",
        ["lake", "build",
         "YangMills.RG.BalabanCMP89SourceFlatGeneratedFiniteDepthCanonicalNeumannRectangleReflectionRepresentation"],
    )
    audit1 = run(
        "cmp89_neumann_rectangle_specialization_audit",
        ["lake", "env", "lean",
         "YangMills/RG/BalabanCMP89SourceFlatGeneratedFiniteDepthCanonicalNeumannRectangleReflectionRepresentationAudit.lean"],
    )
    run(
        "cmp89_neumann_rectangle_physical_specialization_focal",
        ["lake", "build",
         "YangMills.RG.BalabanCMP89SourceFlatGeneratedFiniteDepthCanonicalNeumannRectanglePhysicalReflectionRepresentation"],
    )
    audit2 = run(
        "cmp89_neumann_rectangle_physical_specialization_audit",
        ["lake", "env", "lean",
         "YangMills/RG/BalabanCMP89SourceFlatGeneratedFiniteDepthCanonicalNeumannRectanglePhysicalReflectionRepresentationAudit.lean"],
    )
    audit_axioms(audit1 + "\n" + audit2)
    print("HOT_DIAGNOSTIC_STATUS=PASS", flush=True)
    print("COLD_SEAL_AUTHORITY=0", flush=True)
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except Exception as error:
        print(f"HOT_DIAGNOSTIC_STATUS=FAIL ERROR={error!r}", flush=True)
        raise
