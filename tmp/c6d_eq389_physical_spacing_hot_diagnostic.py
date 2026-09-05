#!/usr/bin/env python3
"""Hot-only diagnostic for two spacing losses and the typed-chain fibre.

Run only after the retained-runtime C6d D2 cold queue emits literal PASS and
its cold evidence has been downloaded.  The existing `.lake` graph is reused.
A PASS remains diagnostic: it cannot remove PRE-VALIDATION, move `20/41`,
attain window 15, or instantiate `TermSource`.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import time


DEFAULT_ROOT = Path("/content/hrpoly-c6d-d2-owner-rescaling")
EVIDENCE_NAME = "hrpoly-c6d-eq389-spacing-and-fibre-hot-evidence"
FIRST = "BalabanCMP99Eq389CovariantLinkPhysicalSpacing.draft"
SECOND = "BalabanCMP99Eq389CutoffLaplacianPhysicalSpacing.draft"
THIRD = "BalabanCMP99SourceGeneratedCountingMassArbitraryChainVaryingOutput.draft"
EXPECTED_AXIOM_HEADERS = 7
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def run(root: Path, evidence: Path, stage: str, command: list[str]) -> str:
    started = time.perf_counter()
    print("STAGE=" + stage + " CMD=" + json.dumps(command), flush=True)
    child = subprocess.run(
        command,
        cwd=root,
        env=os.environ.copy(),
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
    )
    elapsed = time.perf_counter() - started
    output = child.stdout
    print(output, flush=True)
    evidence.mkdir(parents=True, exist_ok=True)
    (evidence / f"{stage}.stdout").write_text(
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


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--source-sha", required=True)
    parser.add_argument("--root", type=Path, default=DEFAULT_ROOT)
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    root = args.root.resolve()
    evidence = Path("/content") / EVIDENCE_NAME
    print("HOT_DIAGNOSTIC_ONLY=1", flush=True)
    print("SOURCE_SHA=" + args.source_sha, flush=True)
    print("ROOT=" + str(root), flush=True)
    if not (root / ".git").is_dir():
        raise RuntimeError("RETAINED_CHECKOUT_MISSING")
    run(root, evidence, "spacing_fetch_exact_sha", [
        "git", "fetch", "origin", args.source_sha,
    ])
    run(root, evidence, "spacing_checkout_exact_sha", [
        "git", "checkout", "--detach", args.source_sha,
    ])
    head = run(root, evidence, "spacing_verify_head", [
        "git", "rev-parse", "HEAD",
    ]).strip()
    if head != args.source_sha:
        raise RuntimeError("HOT_SOURCE_SHA_MISMATCH=" + head)
    for manifest in (
        "tmp/c6d-eq389-physical-spacing-draft-paths.txt",
        "tmp/c6d-eq389-physical-spacing-second-species-draft-paths.txt",
        "tmp/c6d-eq389-arbitrary-chain-varying-output-draft-paths.txt",
    ):
        stem = Path(manifest).stem
        run(root, evidence, "spacing_text_guard_" + stem, [
            "python3", "scripts/check_lean_overlay_text.py", "--paths-from", manifest,
        ])
    all_paths = [
        f"tmp/{FIRST}.lean",
        f"tmp/{FIRST}Audit.lean",
        f"tmp/{SECOND}.lean",
        f"tmp/{SECOND}Audit.lean",
        f"tmp/{THIRD}.lean",
        f"tmp/{THIRD}Audit.lean",
    ]
    run(root, evidence, "spacing_import_prefix_guard", [
        "python3", "scripts/check_lean_import_prefix.py", *all_paths,
    ])
    run(root, evidence, "spacing_first_species_focal", [
        "lake", "env", "lean", f"tmp/{FIRST}.lean",
    ])
    first_audit = run(root, evidence, "spacing_first_species_audit", [
        "lake", "env", "lean", f"tmp/{FIRST}Audit.lean",
    ])
    run(root, evidence, "spacing_second_species_focal", [
        "lake", "env", "lean", f"tmp/{SECOND}.lean",
    ])
    second_audit = run(root, evidence, "spacing_second_species_audit", [
        "lake", "env", "lean", f"tmp/{SECOND}Audit.lean",
    ])
    run(root, evidence, "typed_chain_fibre_focal", [
        "lake", "env", "lean", f"tmp/{THIRD}.lean",
    ])
    third_audit = run(root, evidence, "typed_chain_fibre_audit", [
        "lake", "env", "lean", f"tmp/{THIRD}Audit.lean",
    ])
    verify_axioms(first_audit + "\n" + second_audit + "\n" + third_audit)
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
