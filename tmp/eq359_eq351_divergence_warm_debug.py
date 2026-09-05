#!/usr/bin/env python3
"""Warm diagnostic for the canonical complex divergence in CMP99 (3.51).

Run only after the exact Eq359 cold gate and the two bounded Eq351 bond
diagnostics have passed in the retained runtime.  The script checks out one
published PRE-VALIDATION source checkpoint, verifies the exact Git blobs,
materializes only the divergence source/audit pair, and compiles it
stop-on-first-error.  It is diagnostic evidence only: it does not remove
PRE-VALIDATION, edit the ledger, commit, push, or release the runtime.
"""

from __future__ import annotations

import json
from pathlib import Path
import re
import subprocess
import time


ROOT = Path("/content/hrpoly-eq359-real-slice")
EVIDENCE = Path("/content/hrpoly-eq359-real-slice-evidence/evidence.json")
EQ359_SOURCE = "cd6ff65638f0e09e2533733df2d7176c10714a3a"
DEBUG_SOURCE = "e87e833bf84e597e99ac7fb171c23046965abb2d"
SOURCE_DRAFT = (
    "tmp/BalabanCMP99Eq351PhysicalComplexCovariantDivergence.draft.lean"
)
AUDIT_DRAFT = (
    "tmp/BalabanCMP99Eq351PhysicalComplexCovariantDivergenceAudit.draft.lean"
)
SOURCE_BLOB = "a24d8ac01ea0aebc9aadcf168c7c838de9b36c58"
AUDIT_BLOB = "7ec4dd3da539bae6ea34a5003b7d970d3015ebee"
MANIFEST_BLOB = "a9ef7ddbb466ffb360718a5e0f3e54f5b5217a87"
TOOLCHAIN_BLOB = "87b20aaf848f44309e4d34c1f941c70a2283f22b"
MODULE = "BalabanCMP99Eq351PhysicalComplexCovariantDivergence"
EXPECTED_AXIOM_HEADERS = 4
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def run(stage: str, command: list[str]) -> str:
    started = time.perf_counter()
    print("WARM_DIV_STAGE=" + stage + " CMD=" + json.dumps(command), flush=True)
    child = subprocess.run(
        command,
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
    )
    elapsed = time.perf_counter() - started
    print(child.stdout, flush=True)
    print(
        f"WARM_DIV_STAGE={stage} EXIT={child.returncode} SECONDS={elapsed:.3f}",
        flush=True,
    )
    if child.returncode != 0:
        raise RuntimeError("WARM_DIV_FIRST_ERROR=" + stage)
    return child.stdout


def require_passed_eq359() -> None:
    if not EVIDENCE.is_file():
        raise RuntimeError("WARM_DIV_EQ359_EVIDENCE_MISSING")
    evidence = json.loads(EVIDENCE.read_text(encoding="utf-8"))
    if evidence.get("status") != "PASS":
        raise RuntimeError("WARM_DIV_EQ359_NOT_PASS")
    if evidence.get("source_sha") != EQ359_SOURCE:
        raise RuntimeError("WARM_DIV_EQ359_SOURCE_MISMATCH")


def git_blob(path: str) -> str:
    return run("blob_" + Path(path).stem.lower(), ["git", "rev-parse", f"HEAD:{path}"]).strip()


def require_blob(path: str, expected: str) -> None:
    measured = git_blob(path)
    if measured != expected:
        raise RuntimeError(f"WARM_DIV_BLOB_MISMATCH={path}:{measured}")
    print(f"WARM_DIV_BLOB_OK={path}:{measured}", flush=True)


def materialize() -> None:
    source = ROOT / SOURCE_DRAFT
    audit = ROOT / AUDIT_DRAFT
    target = ROOT / f"YangMills/RG/{MODULE}.lean"
    target.write_text(source.read_text(encoding="utf-8"), encoding="utf-8", newline="\n")

    audit_text = audit.read_text(encoding="utf-8")
    old_import = (
        "import tmp."
        "BalabanCMP99Eq351PhysicalComplexCovariantDivergence.draft"
    )
    new_import = (
        "import YangMills.RG."
        "BalabanCMP99Eq351PhysicalComplexCovariantDivergence"
    )
    if audit_text.count(old_import) != 1:
        raise RuntimeError("WARM_DIV_AUDIT_IMPORT_COUNT")
    audit_text = audit_text.replace(old_import, new_import)
    audit_target = ROOT / f"YangMills/RG/{MODULE}Audit.lean"
    audit_target.write_text(audit_text, encoding="utf-8", newline="\n")
    print(f"WARM_DIV_MATERIALIZED={target.relative_to(ROOT)}", flush=True)
    print(f"WARM_DIV_MATERIALIZED={audit_target.relative_to(ROOT)}", flush=True)


def compile_module(stage: str, module: str) -> str:
    source = f"YangMills/RG/{module}.lean"
    output = f".lake/build/lib/lean/YangMills/RG/{module}.olean"
    return run(stage, ["lake", "env", "lean", source, "-o", output])


def parse_axioms(output: str) -> None:
    compact = re.sub(r"\s+", "", output)
    for forbidden in ("sorryAx", "ofReduceBool"):
        if forbidden in compact:
            raise RuntimeError("WARM_DIV_FORBIDDEN_AXIOM=" + forbidden)
    blocks = re.findall(r"dependsonaxioms:\[([^\]]*)\]", compact)
    pure = compact.count("doesnotdependonanyaxioms")
    if len(blocks) + pure != EXPECTED_AXIOM_HEADERS:
        raise RuntimeError(
            "WARM_DIV_AXIOM_HEADER_COUNT=" + str(len(blocks) + pure)
        )
    for index, body in enumerate(blocks, start=1):
        names = {name for name in body.split(",") if name}
        unexpected = names - ALLOWED_AXIOMS
        if unexpected:
            raise RuntimeError(
                f"WARM_DIV_AXIOM_SET_{index}={sorted(unexpected)}"
            )
    print(
        f"WARM_DIV_AXIOM_GATE_OK headers={EXPECTED_AXIOM_HEADERS} "
        f"blocks={len(blocks)} pure={pure}",
        flush=True,
    )


def main() -> int:
    require_passed_eq359()
    run("fetch_debug", ["git", "fetch", "origin", DEBUG_SOURCE])
    run("checkout_debug", ["git", "checkout", "--detach", DEBUG_SOURCE])
    head = run("head", ["git", "rev-parse", "HEAD"]).strip()
    if head != DEBUG_SOURCE:
        raise RuntimeError("WARM_DIV_HEAD_MISMATCH=" + head)

    require_blob(SOURCE_DRAFT, SOURCE_BLOB)
    require_blob(AUDIT_DRAFT, AUDIT_BLOB)
    require_blob("lake-manifest.json", MANIFEST_BLOB)
    require_blob("lean-toolchain", TOOLCHAIN_BLOB)
    materialize()
    (ROOT / ".lake/build/lib/lean/YangMills/RG").mkdir(parents=True, exist_ok=True)
    compile_module("divergence_source", MODULE)
    audit_output = compile_module("divergence_audit", MODULE + "Audit")
    parse_axioms(audit_output)
    print("WARM_EQ351_DIVERGENCE_FINAL_STATUS=PASS", flush=True)
    return 0


if __name__ == "__main__":
    try:
        exit_code = main()
    except Exception as exc:
        print("WARM_EQ351_DIVERGENCE_FINAL_STATUS=FAIL", flush=True)
        print("WARM_EQ351_DIVERGENCE_ERROR=" + repr(exc), flush=True)
        raise
    raise SystemExit(exit_code)
