#!/usr/bin/env python3
"""Bounded warm debug for the C6d common-target real-slice tower pair.

Run only after the pinned C6d next-real-slice cold gate has emitted its final
verdict and its evidence archive has been preserved.  This diagnostic reuses
that checkout/build state, fetches exactly two scratch blobs from one Git
checkpoint, and stops at the first Lean error.  It is not cold evidence and
cannot retire PRE-VALIDATION.
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
import re
import subprocess
import time
import urllib.request


DEBUG_REV = "c6d-terminal-pair-warm-v1"
BASE_SOURCE_SHA = "81cc22e41d46cce150c2a263c85e4acb90087153"
SCRATCH_SHA = "3aa88db211865698a14e9f4d812aa3430dcce0ac"
ROOT = Path("/content/hrpoly-c6d-next-real-slice")
EVIDENCE = Path("/content/hrpoly-c6d-terminal-pair-debug")
FILES = {
    "tmp/BalabanCMP99SourcePhysicalRealSliceTowerPair.draft.lean":
        "85ac5913c06f0df89d2f712f3cac5bc4f8bd1687d0bb3b2d7dff7d7641319d36",
    "tmp/BalabanCMP99SourcePhysicalRealSliceTowerPairAudit.draft.lean":
        "fd1a11f5a36934309923c78a226ef02eb269d09c73af38088d4a697b56526e35",
}
RAW = (
    "https://raw.githubusercontent.com/lluiseriksson/"
    "THE-ERIKSSON-PROGRAMME/{sha}/{path}"
)
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
FORBIDDEN = ("sorryAx", "ofReduceBool", "Lean.ofReduceBool")


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


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


def main() -> int:
    print("DEBUG_REV=" + DEBUG_REV, flush=True)
    if not ROOT.is_dir():
        raise RuntimeError("C6D_TERMINAL_PAIR_ROOT_MISSING")
    head = subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=ROOT, text=True
    ).strip()
    print("BASE_SOURCE_SHA=" + head, flush=True)
    if head != BASE_SOURCE_SHA:
        raise RuntimeError("C6D_TERMINAL_PAIR_BASE_SOURCE_MISMATCH")

    for relative, wanted in FILES.items():
        url = RAW.format(sha=SCRATCH_SHA, path=relative)
        with urllib.request.urlopen(url) as response:
            data = response.read()
        measured = sha256(data)
        print(f"SCRATCH_BLOB={relative} SHA256={measured}", flush=True)
        if measured != wanted:
            raise RuntimeError("C6D_TERMINAL_PAIR_BLOB_MISMATCH=" + relative)
        target = ROOT / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(data)

    run(
        "c6d_terminal_pair_materialize_dependencies",
        [
            "lake", "build",
            "YangMills.RG.BalabanCMP99SourcePhysicalRealSliceTower",
            "YangMills.RG.BalabanCMP99Eq359ComplexRegionalTowerPair",
        ],
    )

    output_dir = ROOT / ".lake/build/lib/lean/tmp"
    output_dir.mkdir(parents=True, exist_ok=True)
    source = "tmp/BalabanCMP99SourcePhysicalRealSliceTowerPair.draft.lean"
    audit = "tmp/BalabanCMP99SourcePhysicalRealSliceTowerPairAudit.draft.lean"
    run(
        "c6d_terminal_pair_source",
        [
            "lake", "env", "lean", source, "-o",
            ".lake/build/lib/lean/tmp/"
            "BalabanCMP99SourcePhysicalRealSliceTowerPair.draft.olean",
        ],
    )
    audit_output = run(
        "c6d_terminal_pair_audit",
        [
            "lake", "env", "lean", audit, "-o",
            ".lake/build/lib/lean/tmp/"
            "BalabanCMP99SourcePhysicalRealSliceTowerPairAudit.draft.olean",
        ],
    )
    compact = re.sub(r"\s+", "", audit_output)
    for forbidden in FORBIDDEN:
        if forbidden in compact:
            raise RuntimeError("C6D_TERMINAL_PAIR_FORBIDDEN=" + forbidden)
    blocks = re.findall(r"'[^']+'dependsonaxioms:\[(.*?)\]", compact)
    no_axiom = re.findall(r"'[^']+'doesnotdependonanyaxioms", compact)
    if len(blocks) + len(no_axiom) != 5:
        raise RuntimeError(
            "C6D_TERMINAL_PAIR_AXIOM_COUNT="
            + str(len(blocks) + len(no_axiom))
        )
    for body in blocks:
        names = {name for name in body.split(",") if name}
        if not names.issubset(ALLOWED):
            raise RuntimeError(
                "C6D_TERMINAL_PAIR_NONSTANDARD=" + ",".join(sorted(names))
            )
    print("C6D_TERMINAL_PAIR_WARM_DEBUG_OK", flush=True)
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
