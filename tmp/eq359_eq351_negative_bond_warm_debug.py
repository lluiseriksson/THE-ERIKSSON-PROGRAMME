#!/usr/bin/env python3
"""Warm diagnostic for the canonical negative-bond Eq. (3.50) factorization.

Run only after the exact Eq359 cold gate and the bounded positive-adjoint
diagnostic have passed in the retained runtime.  This script checks out one
published PRE-VALIDATION source checkpoint, materializes only the negative-
bond source/audit pair, and compiles it stop-on-first-error.  It is diagnostic
evidence only: it does not remove PRE-VALIDATION, edit the ledger, commit,
push, or release the runtime.
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
import re
import subprocess
import time


ROOT = Path("/content/hrpoly-eq359-real-slice")
EVIDENCE = Path("/content/hrpoly-eq359-real-slice-evidence/evidence.json")
EQ359_SOURCE = "cd6ff65638f0e09e2533733df2d7176c10714a3a"
DEBUG_SOURCE = "6c9c21c379fd496c851cbcd1ce47f40aa070d3e1"
SOURCE_DRAFT = (
    "tmp/BalabanCMP99Eq351PhysicalComplexNegativeBondFactorization.draft.lean"
)
AUDIT_DRAFT = (
    "tmp/BalabanCMP99Eq351PhysicalComplexNegativeBondFactorizationAudit.draft.lean"
)
SOURCE_SHA256 = "462AC2AE9C6BD8DF05D40E9126757A12AD5DEA91EE29308B4CAA548E97AECF0F"
AUDIT_SHA256 = "78722D2D193B0A2C14518E997DEA0864130AA12673F1A9172F553E83D84B4F2B"
MODULE = "BalabanCMP99Eq351PhysicalComplexNegativeBondFactorization"
EXPECTED_AXIOM_HEADERS = 10
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest().upper()


def run(stage: str, command: list[str]) -> str:
    started = time.perf_counter()
    print("WARM_NEG_STAGE=" + stage + " CMD=" + json.dumps(command), flush=True)
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
        f"WARM_NEG_STAGE={stage} EXIT={child.returncode} SECONDS={elapsed:.3f}",
        flush=True,
    )
    if child.returncode != 0:
        raise RuntimeError("WARM_NEG_FIRST_ERROR=" + stage)
    return child.stdout


def require_passed_eq359() -> None:
    if not EVIDENCE.is_file():
        raise RuntimeError("WARM_NEG_EQ359_EVIDENCE_MISSING")
    evidence = json.loads(EVIDENCE.read_text(encoding="utf-8"))
    if evidence.get("status") != "PASS":
        raise RuntimeError("WARM_NEG_EQ359_NOT_PASS")
    if evidence.get("source_sha") != EQ359_SOURCE:
        raise RuntimeError("WARM_NEG_EQ359_SOURCE_MISMATCH")


def materialize() -> None:
    source = ROOT / SOURCE_DRAFT
    audit = ROOT / AUDIT_DRAFT
    if sha256(source) != SOURCE_SHA256:
        raise RuntimeError("WARM_NEG_SOURCE_HASH_MISMATCH")
    if sha256(audit) != AUDIT_SHA256:
        raise RuntimeError("WARM_NEG_AUDIT_HASH_MISMATCH")

    target = ROOT / f"YangMills/RG/{MODULE}.lean"
    target.write_text(source.read_text(encoding="utf-8"), encoding="utf-8", newline="\n")

    audit_text = audit.read_text(encoding="utf-8")
    old_import = (
        "import tmp."
        "BalabanCMP99Eq351PhysicalComplexNegativeBondFactorization.draft"
    )
    new_import = (
        "import YangMills.RG."
        "BalabanCMP99Eq351PhysicalComplexNegativeBondFactorization"
    )
    if audit_text.count(old_import) != 1:
        raise RuntimeError("WARM_NEG_AUDIT_IMPORT_COUNT")
    audit_text = audit_text.replace(old_import, new_import)
    audit_target = ROOT / f"YangMills/RG/{MODULE}Audit.lean"
    audit_target.write_text(audit_text, encoding="utf-8", newline="\n")
    print(f"WARM_NEG_MATERIALIZED={target.relative_to(ROOT)} SHA256={sha256(target)}")
    print(
        f"WARM_NEG_MATERIALIZED={audit_target.relative_to(ROOT)} "
        f"SHA256={sha256(audit_target)}"
    )


def compile_module(stage: str, module: str) -> str:
    source = f"YangMills/RG/{module}.lean"
    output = f".lake/build/lib/lean/YangMills/RG/{module}.olean"
    return run(stage, ["lake", "env", "lean", source, "-o", output])


def parse_axioms(output: str) -> None:
    compact = re.sub(r"\s+", "", output)
    for forbidden in ("sorryAx", "ofReduceBool"):
        if forbidden in compact:
            raise RuntimeError("WARM_NEG_FORBIDDEN_AXIOM=" + forbidden)
    blocks = re.findall(r"dependsonaxioms:\[([^\]]*)\]", compact)
    pure = compact.count("doesnotdependonanyaxioms")
    if len(blocks) + pure != EXPECTED_AXIOM_HEADERS:
        raise RuntimeError(
            "WARM_NEG_AXIOM_HEADER_COUNT=" + str(len(blocks) + pure)
        )
    for index, body in enumerate(blocks, start=1):
        names = {name for name in body.split(",") if name}
        unexpected = names - ALLOWED_AXIOMS
        if unexpected:
            raise RuntimeError(
                f"WARM_NEG_AXIOM_SET_{index}={sorted(unexpected)}"
            )
    print(
        f"WARM_NEG_AXIOM_GATE_OK headers={EXPECTED_AXIOM_HEADERS} "
        f"blocks={len(blocks)} pure={pure}",
        flush=True,
    )


def main() -> int:
    require_passed_eq359()
    manifest_before = sha256(ROOT / "lake-manifest.json")
    toolchain_before = sha256(ROOT / "lean-toolchain")
    run("fetch_debug", ["git", "fetch", "origin", DEBUG_SOURCE])
    run("checkout_debug", ["git", "checkout", "--detach", DEBUG_SOURCE])
    if sha256(ROOT / "lake-manifest.json") != manifest_before:
        raise RuntimeError("WARM_NEG_MANIFEST_DRIFT")
    if sha256(ROOT / "lean-toolchain") != toolchain_before:
        raise RuntimeError("WARM_NEG_TOOLCHAIN_DRIFT")
    materialize()
    (ROOT / ".lake/build/lib/lean/YangMills/RG").mkdir(parents=True, exist_ok=True)
    compile_module("negative_bond_source", MODULE)
    audit_output = compile_module("negative_bond_audit", MODULE + "Audit")
    parse_axioms(audit_output)
    print("WARM_NEGATIVE_BOND_FINAL_STATUS=PASS", flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
