#!/usr/bin/env python3
"""Hot-only diagnostic for exact depth-zero full-companion coercivity.

Run after the two retained-runtime C6d ambient/compression queues.  The
existing `.lake` graph is preserved.  A PASS is diagnostic only and cannot
remove PRE-VALIDATION, enlarge the cold manifest silently, move `20/41`, or
instantiate `TermSource`.
"""

from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import time


SOURCE_SHA = "2c25f7bac370306b6ebbc96e05d048c0b0cf15a9"
ROOT = Path("/content/hrpoly-c6d-source-coercivity-green")
EVIDENCE = Path("/content/hrpoly-c6d-zero-depth-hot-evidence")
MODULE = "BalabanCMP99SourceActiveRegionFullCompanionZeroDepth"
SOURCE_DRAFT = Path(
    "tmp/BalabanCMP99SourceActiveRegionFullCompanionZeroDepth.draft.lean"
)
AUDIT_DRAFT = Path(
    "tmp/BalabanCMP99SourceActiveRegionFullCompanionZeroDepthAudit.draft.lean"
)
EXPECTED_AXIOM_HEADERS = 3
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def run(stage: str, command: list[str]) -> str:
    started = time.perf_counter()
    print("STAGE=" + stage + " CMD=" + json.dumps(command), flush=True)
    child = subprocess.run(
        command,
        cwd=ROOT,
        env=os.environ.copy(),
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
    )
    elapsed = time.perf_counter() - started
    output = child.stdout
    print(output, flush=True)
    EVIDENCE.mkdir(parents=True, exist_ok=True)
    (EVIDENCE / f"{stage}.stdout").write_text(
        output, encoding="utf-8", newline="\n"
    )
    print(
        f"STAGE={stage} EXIT={child.returncode} SECONDS={elapsed:.3f} "
        + "SHA256=" + hashlib.sha256(output.encode()).hexdigest(),
        flush=True,
    )
    if child.returncode != 0:
        raise RuntimeError("FIRST_ERROR=" + stage)
    return output


def materialize(source: Path, destination_name: str) -> None:
    source_path = ROOT / source
    destination = ROOT / "YangMills" / "RG" / destination_name
    if not source_path.is_file():
        raise RuntimeError("SCRATCH_SOURCE_MISSING=" + str(source))
    payload = source_path.read_bytes()
    if destination.exists() and destination.read_bytes() != payload:
        raise RuntimeError("DESTINATION_COLLISION=" + str(destination))
    destination.write_bytes(payload)
    print(
        "MATERIALIZED=" + str(destination.relative_to(ROOT))
        + " SHA256=" + hashlib.sha256(payload).hexdigest(),
        flush=True,
    )


def verify_axioms(output: str) -> None:
    dependency_blocks = re.findall(
        r"depends on axioms:\s*\[(.*?)\]", output, flags=re.DOTALL
    )
    pure_count = output.count("does not depend on any axioms")
    actual = len(dependency_blocks) + pure_count
    if actual != EXPECTED_AXIOM_HEADERS:
        raise RuntimeError(
            f"AXIOM_HEADER_COUNT={actual} EXPECTED={EXPECTED_AXIOM_HEADERS}"
        )
    for block in dependency_blocks:
        names = {name.strip() for name in block.replace("\n", " ").split(",")}
        forbidden = sorted(name for name in names if name not in ALLOWED_AXIOMS)
        if forbidden:
            raise RuntimeError(f"FORBIDDEN_AXIOMS={forbidden!r}")
    for forbidden in ("sorryAx", "ofReduceBool"):
        if forbidden in output:
            raise RuntimeError(f"FORBIDDEN_AXIOM_TOKEN={forbidden}")
    print(f"AXIOM_GATE=PASS DECLARATIONS={actual}", flush=True)


def main() -> int:
    print("HOT_DIAGNOSTIC_ONLY=1", flush=True)
    print("SOURCE_SHA=" + SOURCE_SHA, flush=True)
    if not (ROOT / ".git").is_dir():
        raise RuntimeError("RETAINED_CHECKOUT_MISSING")
    run("zero_depth_fetch_exact_sha", ["git", "fetch", "origin", SOURCE_SHA])
    run("zero_depth_checkout_exact_sha", ["git", "checkout", "--detach", SOURCE_SHA])
    head = run("zero_depth_verify_head", ["git", "rev-parse", "HEAD"]).strip()
    if head != SOURCE_SHA:
        raise RuntimeError("HOT_SOURCE_SHA_MISMATCH=" + head)
    run(
        "zero_depth_text_guard",
        [
            "python3",
            "scripts/check_lean_overlay_text.py",
            "--paths-from",
            "tmp/c6d-full-companion-zero-depth-draft-paths.txt",
        ],
    )
    materialize(SOURCE_DRAFT, MODULE + ".lean")
    materialize(AUDIT_DRAFT, MODULE + "Audit.lean")
    run(
        "zero_depth_source",
        [
            "lake", "env", "lean", f"YangMills/RG/{MODULE}.lean", "-o",
            f".lake/build/lib/lean/YangMills/RG/{MODULE}.olean",
        ],
    )
    audit = run(
        "zero_depth_audit",
        [
            "lake", "env", "lean", f"YangMills/RG/{MODULE}Audit.lean", "-o",
            f".lake/build/lib/lean/YangMills/RG/{MODULE}Audit.olean",
        ],
    )
    verify_axioms(audit)
    print("FINAL_STATUS=PASS", flush=True)
    print("CLASSIFICATION=HOT_DIAGNOSTIC_ONLY", flush=True)
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except Exception as exc:
        print(repr(exc), flush=True)
        print("FINAL_STATUS=FAIL", flush=True)
        raise
