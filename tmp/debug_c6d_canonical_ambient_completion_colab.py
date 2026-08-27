#!/usr/bin/env python3
"""Hot Colab diagnostic for the post-Eq360 C6d dictionary scratch pairs.

This is deliberately not seal evidence.  It reuses the `.lake` tree of the
completed C6d cold checkout only to turn elaboration errors into a short
diagnostic cycle.  A later promotion still needs its own fresh cold gate.
"""

from __future__ import annotations

import argparse
import os
from pathlib import Path
import re
import shutil
import subprocess
import time


REMOTE = "https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME.git"
COLD_ROOT = Path("/content/hrpoly-c6d-next-real-slice")
DEBUG_ROOT = Path("/content/hrpoly-c6d-canonical-ambient-completion-debug")
PAIRS = (
    (
        "tmp/BalabanCMP99ActiveRegionCanonicalAmbientCompletion.draft.lean",
        "tmp/BalabanCMP99ActiveRegionCanonicalAmbientCompletionAudit.draft.lean",
    ),
    (
        "tmp/BalabanCMP99SourceWeightedGaugePrecisionDictionary.draft.lean",
        "tmp/BalabanCMP99SourceWeightedGaugePrecisionDictionaryAudit.draft.lean",
    ),
)
EXPECTED_AXIOM_HEADERS = 10
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def run(command: list[str], *, cwd: Path | None = None) -> str:
    started = time.perf_counter()
    print("CMD=" + repr(command), flush=True)
    child = subprocess.run(
        command,
        cwd=cwd,
        env=os.environ.copy(),
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
    )
    elapsed = time.perf_counter() - started
    print(child.stdout, flush=True)
    print(
        f"EXIT={child.returncode} SECONDS={elapsed:.3f}",
        flush=True,
    )
    if child.returncode != 0:
        raise RuntimeError("FIRST_ERROR=" + " ".join(command))
    return child.stdout


def require_source_sha(value: str) -> str:
    if re.fullmatch(r"[0-9a-f]{40}", value) is None:
        raise RuntimeError("SOURCE_SHA_INVALID")
    return value


def parse_axioms(output: str) -> None:
    if output.count("depends on axioms:") != EXPECTED_AXIOM_HEADERS:
        raise RuntimeError(
            "AXIOM_HEADER_COUNT="
            f"{output.count('depends on axioms:')} WANT={EXPECTED_AXIOM_HEADERS}"
        )
    if "sorryAx" in output or "ofReduceBool" in output:
        raise RuntimeError("FORBIDDEN_AXIOM_SENTINEL")
    flattened = " ".join(output.replace("\r", "").split())
    lists = re.findall(r"depends on axioms:\s*\[([^]]*)\]", flattened)
    if len(lists) != EXPECTED_AXIOM_HEADERS:
        raise RuntimeError(
            f"AXIOM_LIST_COUNT={len(lists)} WANT={EXPECTED_AXIOM_HEADERS}"
        )
    for index, payload in enumerate(lists, start=1):
        seen = {piece.strip() for piece in payload.split(",") if piece.strip()}
        extra = seen - ALLOWED_AXIOMS
        if extra:
            raise RuntimeError(f"AXIOM_BLOCK_{index}_FORBIDDEN={sorted(extra)}")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--source-sha", required=True, type=require_source_sha)
    args = parser.parse_args()

    if not COLD_ROOT.is_dir() or not (COLD_ROOT / ".lake").is_dir():
        raise RuntimeError("COLD_CHECKOUT_OR_CACHE_MISSING")
    shutil.rmtree(DEBUG_ROOT, ignore_errors=True)
    run(["git", "clone", "--no-checkout", REMOTE, str(DEBUG_ROOT)])
    run(["git", "checkout", "--detach", args.source_sha], cwd=DEBUG_ROOT)
    head = run(["git", "rev-parse", "HEAD"], cwd=DEBUG_ROOT).strip()
    if head != args.source_sha:
        raise RuntimeError(f"SOURCE_HEAD={head} WANT={args.source_sha}")
    for relative in (item for pair in PAIRS for item in pair):
        if not (DEBUG_ROOT / relative).is_file():
            raise RuntimeError("SOURCE_BLOB_MISSING=" + relative)

    run(["cp", "-al", str(COLD_ROOT / ".lake"), str(DEBUG_ROOT / ".lake")])
    (DEBUG_ROOT / ".lake/build/lib/lean/tmp").mkdir(parents=True, exist_ok=True)

    audit_outputs: list[str] = []
    for source, audit in PAIRS:
        source_output = ".lake/build/lib/lean/tmp/" + Path(source).stem + ".olean"
        audit_output = ".lake/build/lib/lean/tmp/" + Path(audit).stem + ".olean"
        run(
            ["lake", "env", "lean", source, "-o", source_output],
            cwd=DEBUG_ROOT,
        )
        audit_outputs.append(
            run(
                ["lake", "env", "lean", audit, "-o", audit_output],
                cwd=DEBUG_ROOT,
            )
        )
    parse_axioms("\n".join(audit_outputs))
    print(
        "FINAL_STATUS=PASS "
        f"source_sha={args.source_sha} axiom_headers={EXPECTED_AXIOM_HEADERS} "
        "evidence_class=HOT_DIAGNOSTIC_NOT_SEAL",
        flush=True,
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
