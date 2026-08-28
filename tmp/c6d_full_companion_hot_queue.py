#!/usr/bin/env python3
"""Hot diagnostic queue for the C6d full-companion compression chain.

Run only inside the retained Colab checkout after the independent cold
source-coercivity/Green gate has emitted FINAL_STATUS=PASS.  This runner keeps
the existing `.lake` graph, checks out one exact published SHA, and stops on
the first compiler or audit error.  A PASS is diagnostic evidence only and
does not authorize removal of PRE-VALIDATION marks.
"""

from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import time


SOURCE_SHA = "c59a28b553a161afd99d34bc4b0aebbad09b5182"
ROOT = Path("/content/hrpoly-c6d-source-coercivity-green")
EVIDENCE = Path("/content/hrpoly-c6d-full-companion-hot-evidence")
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
MODULES = [
    ("BalabanCMP99RegionalDirichletGaugePrecisionCompression", 2),
    ("BalabanCMP99SourceActiveRegionFullCompanion", 5),
    ("BalabanCMP99SourceGeneratedMassCompression", 3),
    ("BalabanCMP99SourceGeneratedPhysicalPrecisionCompression", 3),
    ("BalabanCMP99SourceActiveRegionFullCompanionPrecision", 6),
    ("BalabanCMP99SourceActiveRegionFullCompanionAmbientPrecision", 6),
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
    run("hot_fetch_exact_sha", ["git", "fetch", "origin", SOURCE_SHA])
    run("hot_checkout_exact_sha", ["git", "checkout", "--detach", SOURCE_SHA])
    head = run("hot_verify_head", ["git", "rev-parse", "HEAD"]).strip()
    if head != SOURCE_SHA:
        raise RuntimeError("HOT_SOURCE_SHA_MISMATCH=" + head)
    run(
        "hot_text_guard",
        [
            "python3",
            "scripts/check_lean_overlay_text.py",
            "--paths-from",
            "tmp/c6d-regional-dirichlet-compression-overlay-paths.txt",
            "--require-prevalidation",
        ],
    )
    for index, (module, expected_axioms) in enumerate(MODULES, start=1):
        for suffix in ("", "Audit"):
            target = module + suffix
            stage = f"hot_{index:02d}_{target.lower()}"
            output = run(
                stage,
                [
                    "lake",
                    "env",
                    "lean",
                    f"YangMills/RG/{target}.lean",
                    "-o",
                    f".lake/build/lib/lean/YangMills/RG/{target}.olean",
                ],
            )
            if suffix == "Audit":
                verify_axioms(output, expected_axioms, module)
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
