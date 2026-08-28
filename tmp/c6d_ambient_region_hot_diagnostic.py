#!/usr/bin/env python3
"""Hot-only diagnostic for the C6d ambient producer and carrier transport.

Run only after the six-pair full-companion hot queue passes in the retained
Colab checkout.  The script checks out one exact published source checkpoint
without deleting `.lake`, materializes four scratch files under their intended
module names, and stops on the first compiler or axiom-gate error.  A PASS is
diagnostic evidence only: it does not authorize promotion, removal of any
PRE-VALIDATION marker, or movement of `20/41`.
"""

from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import time


SOURCE_SHA = "ec4db69a54e0f47189940086476edf4c47a39abe"
ROOT = Path("/content/hrpoly-c6d-source-coercivity-green")
EVIDENCE = Path("/content/hrpoly-c6d-ambient-region-hot-evidence")
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
PAIRS = [
    (
        "BalabanCMP99ActiveGaugeRegionReindex",
        "tmp/BalabanCMP99ActiveGaugeRegionReindex.draft.lean",
        "tmp/BalabanCMP99ActiveGaugeRegionReindexAudit.draft.lean",
        10,
    ),
    (
        "BalabanCMP99Eq360C6dSourceAmbientBaselinePrecision",
        "tmp/BalabanCMP99Eq360C6dSourceAmbientBaselinePrecision.draft.lean",
        "tmp/BalabanCMP99Eq360C6dSourceAmbientBaselinePrecisionAudit.draft.lean",
        7,
    ),
    (
        "BalabanCMP99ActiveGaugeRegionReindexGreen",
        "tmp/BalabanCMP99ActiveGaugeRegionReindexGreen.draft.lean",
        "tmp/BalabanCMP99ActiveGaugeRegionReindexGreenAudit.draft.lean",
        4,
    ),
]


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


def materialize(source_relative: str, destination_name: str) -> None:
    source = ROOT / source_relative
    destination = ROOT / "YangMills" / "RG" / destination_name
    if not source.is_file():
        raise RuntimeError("SCRATCH_SOURCE_MISSING=" + source_relative)
    payload = source.read_bytes()
    if destination.exists() and destination.read_bytes() != payload:
        raise RuntimeError("DESTINATION_COLLISION=" + str(destination))
    destination.write_bytes(payload)
    print(
        "MATERIALIZED=" + str(destination.relative_to(ROOT))
        + " SHA256=" + hashlib.sha256(payload).hexdigest(),
        flush=True,
    )


def verify_axioms(output: str, expected: int, label: str) -> None:
    dependency_blocks = re.findall(
        r"depends on axioms:\s*\[(.*?)\]", output, flags=re.DOTALL
    )
    pure_count = output.count("does not depend on any axioms")
    actual = len(dependency_blocks) + pure_count
    if actual != expected:
        raise RuntimeError(
            f"AXIOM_HEADER_COUNT_{label}={actual} EXPECTED={expected}"
        )
    for block in dependency_blocks:
        names = {name.strip() for name in block.replace("\n", " ").split(",")}
        forbidden = sorted(name for name in names if name not in ALLOWED_AXIOMS)
        if forbidden:
            raise RuntimeError(f"FORBIDDEN_AXIOMS_{label}={forbidden!r}")
    for forbidden in ("sorryAx", "ofReduceBool"):
        if forbidden in output:
            raise RuntimeError(f"FORBIDDEN_AXIOM_TOKEN_{label}={forbidden}")
    print(f"AXIOM_GATE_{label}=PASS DECLARATIONS={actual}", flush=True)


def main() -> int:
    print("HOT_DIAGNOSTIC_ONLY=1", flush=True)
    print("SOURCE_SHA=" + SOURCE_SHA, flush=True)
    if not (ROOT / ".git").is_dir():
        raise RuntimeError("RETAINED_CHECKOUT_MISSING")
    run("ambient_region_fetch_exact_sha", ["git", "fetch", "origin", SOURCE_SHA])
    run("ambient_region_checkout_exact_sha", ["git", "checkout", "--detach", SOURCE_SHA])
    head = run("ambient_region_verify_head", ["git", "rev-parse", "HEAD"]).strip()
    if head != SOURCE_SHA:
        raise RuntimeError("HOT_SOURCE_SHA_MISMATCH=" + head)
    for manifest in (
        "tmp/c6d-active-region-reindex-draft-paths.txt",
        "tmp/c6d-ambient-baseline-draft-paths.txt",
        "tmp/c6d-active-region-reindex-green-draft-paths.txt",
    ):
        run(
            "text_guard_" + Path(manifest).stem,
            ["python3", "scripts/check_lean_overlay_text.py", "--paths-from", manifest],
        )
    for index, (module, source_draft, audit_draft, expected_axioms) in enumerate(
        PAIRS, start=1
    ):
        materialize(source_draft, module + ".lean")
        materialize(audit_draft, module + "Audit.lean")
        run(
            f"ambient_region_{index:02d}_{module.lower()}_source",
            [
                "lake", "env", "lean", f"YangMills/RG/{module}.lean", "-o",
                f".lake/build/lib/lean/YangMills/RG/{module}.olean",
            ],
        )
        audit_output = run(
            f"ambient_region_{index:02d}_{module.lower()}_audit",
            [
                "lake", "env", "lean", f"YangMills/RG/{module}Audit.lean", "-o",
                f".lake/build/lib/lean/YangMills/RG/{module}Audit.olean",
            ],
        )
        verify_axioms(audit_output, expected_axioms, module)
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
