#!/usr/bin/env python3
"""Warm stop-on-first-error diagnostic for the C6d real-slice gate.

The first cold run proved that the runner omitted a prerequisite `.olean`
boundary.  This script runs only in that retained checkout: it materializes
the direct prerequisites of the three promoted modules and then executes their
source/audit pairs.  Its output is
diagnostic and cannot replace a fresh cold seal with the corrected runner.
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
import re
import subprocess
import time


DEBUG_REV = "c6d-next-real-slice-retry-warm-v1"
BASE_SOURCE_SHA = "81cc22e41d46cce150c2a263c85e4acb90087153"
ROOT = Path("/content/hrpoly-c6d-next-real-slice")
EVIDENCE = Path("/content/hrpoly-c6d-next-real-slice-retry-debug")
MODULES = (
    ("BalabanCMP99Eq337PhysicalComplexBaselineRealSlice", 1),
    ("BalabanCMP99SourceRetainedFineOneCochainExtension", 7),
    ("BalabanCMP99SourcePhysicalRealSliceTower", 2),
)
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
FORBIDDEN = ("sorryAx", "ofReduceBool", "Lean.ofReduceBool")


def run(stage: str, command: list[str]) -> str:
    started = time.perf_counter()
    print("STAGE=" + stage + " CMD=" + json.dumps(command), flush=True)
    child = subprocess.run(
        command,
        cwd=ROOT,
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
        f"STAGE={stage} EXIT={child.returncode} SECONDS={elapsed:.3f}",
        flush=True,
    )
    if child.returncode != 0:
        raise RuntimeError("FIRST_ERROR=" + stage)
    return output


def check_axioms(label: str, output: str, expected: int) -> None:
    compact = re.sub(r"\s+", "", output)
    for forbidden in FORBIDDEN:
        if forbidden in compact:
            raise RuntimeError(label + "_FORBIDDEN=" + forbidden)
    blocks = re.findall(r"'[^']+'dependsonaxioms:\[(.*?)\]", compact)
    no_axiom = re.findall(r"'[^']+'doesnotdependonanyaxioms", compact)
    if len(blocks) + len(no_axiom) != expected:
        raise RuntimeError(
            label + "_AXIOM_COUNT=" + str(len(blocks) + len(no_axiom))
        )
    for body in blocks:
        names = {name for name in body.split(",") if name}
        if not names.issubset(ALLOWED):
            raise RuntimeError(
                label + "_NONSTANDARD=" + ",".join(sorted(names))
            )


def main() -> int:
    print("DEBUG_REV=" + DEBUG_REV, flush=True)
    if not ROOT.is_dir():
        raise RuntimeError("C6D_NEXT_REAL_SLICE_ROOT_MISSING")
    head = subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=ROOT, text=True
    ).strip()
    print("BASE_SOURCE_SHA=" + head, flush=True)
    if head != BASE_SOURCE_SHA:
        raise RuntimeError("C6D_NEXT_REAL_SLICE_BASE_SOURCE_MISMATCH")

    output_dir = ROOT / ".lake/build/lib/lean/YangMills/RG"
    output_dir.mkdir(parents=True, exist_ok=True)
    run(
        "c6d_next_real_slice_missing_prerequisites",
        [
            "lake", "build",
            "YangMills.RG.BalabanCMP99PhysicalBackgroundRealSlice",
            "YangMills.RG.BalabanCMP99SourceRetainedFineExtension",
            "YangMills.RG.BalabanCMP99Eq359TowerRealSliceAgreement",
            "YangMills.RG.BalabanCMP99SourceGeneratedPoincareQprime",
        ],
    )

    for index, (module, expected) in enumerate(MODULES, start=1):
        prefix = f"c6d_next_real_slice_retry_{index:02d}_{module.lower()}"
        run(
            prefix + "_source",
            [
                "lake", "env", "lean", f"YangMills/RG/{module}.lean", "-o",
                f".lake/build/lib/lean/YangMills/RG/{module}.olean",
            ],
        )
        audit_output = run(
            prefix + "_audit",
            [
                "lake", "env", "lean", f"YangMills/RG/{module}Audit.lean",
                "-o", f".lake/build/lib/lean/YangMills/RG/{module}Audit.olean",
            ],
        )
        check_axioms(module, audit_output, expected)

    manifest = {
        "base_source_sha": BASE_SOURCE_SHA,
        "debug_rev": DEBUG_REV,
        "modules": [module for module, _ in MODULES],
        "status": "PASS",
    }
    EVIDENCE.mkdir(parents=True, exist_ok=True)
    payload = json.dumps(manifest, indent=2, sort_keys=True) + "\n"
    (EVIDENCE / "manifest.json").write_text(
        payload, encoding="utf-8", newline="\n"
    )
    print(
        "C6D_NEXT_REAL_SLICE_RETRY_MANIFEST_SHA256="
        + hashlib.sha256(payload.encode()).hexdigest(),
        flush=True,
    )
    print("C6D_NEXT_REAL_SLICE_RETRY_WARM_DEBUG_OK", flush=True)
    print("FINAL_STATUS=PASS", flush=True)
    return 0


if __name__ == "__main__":
    try:
        exit_code = main()
    except BaseException as exc:
        print("FINAL_STATUS=FAIL", flush=True)
        print("FAILURE=" + repr(exc), flush=True)
        raise
    if exit_code:
        raise SystemExit(exit_code)
