#!/usr/bin/env python3
"""Fail-closed retained-checkout diagnostic for the physical uniform owner bound.

Run only after the physical period/owner cold gate has emitted PASS and its
evidence archive exists.  The script downloads two immutable draft blobs,
verifies their Git blob identities, materializes disposable promoted names in
the retained checkout, and runs one focal plus its exact axiom audit.
"""

from __future__ import annotations

import hashlib
import os
from pathlib import Path
import re
import subprocess
import sys
import time
import urllib.request


DRAFT_SHA = "d9d44d539c050f1312f2d9653bd6a418cea610d3"
EXPECTED_HEAD = "1b9979c1371c68b6aaa9722afaa1314c41adfa49"
ROOT = Path("/content/hrpoly-cmp89-physical-owner-geometry-cold-1b9979c1")
RAW_ROOT = (
    "https://raw.githubusercontent.com/lluiseriksson/"
    "THE-ERIKSSON-PROGRAMME/" + DRAFT_SHA + "/tmp/"
)
FILES = {
    "BalabanCMP89NeumannRectangularPhysicalUniformOwnerBound.draft.lean": (
        "YangMills/RG/BalabanCMP89NeumannRectangularPhysicalUniformOwnerBound.lean",
        "2207815ad13b78669fb240cf65c78e8e240212ca",
    ),
    "BalabanCMP89NeumannRectangularPhysicalUniformOwnerBoundAudit.draft.lean": (
        "YangMills/RG/BalabanCMP89NeumannRectangularPhysicalUniformOwnerBoundAudit.lean",
        "08f3080c7d38f2e3af3d71b6e83dd9d375f23bdb",
    ),
}
EXPECTED_DECL = (
    "YangMills.RG."
    "norm_cmp89Eq248PhysicalRegionalGreen_le_physicalOwner_uniform_draft"
)
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def git_blob_id(data: bytes) -> str:
    prefix = f"blob {len(data)}\0".encode()
    return hashlib.sha1(prefix + data).hexdigest()


def run(stage: str, command: list[str]) -> str:
    print(f"STAGE={stage} CMD={command!r}", flush=True)
    started = time.perf_counter()
    child = subprocess.Popen(
        command,
        cwd=ROOT,
        env=os.environ.copy(),
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
    )
    assert child.stdout is not None
    chunks: list[str] = []
    while True:
        line = child.stdout.readline()
        if line:
            print(line, end="", flush=True)
            chunks.append(line)
        elif child.poll() is not None:
            break
    exit_code = child.wait()
    elapsed = time.perf_counter() - started
    print(f"STAGE={stage} EXIT={exit_code} SECONDS={elapsed:.3f}", flush=True)
    if exit_code != 0:
        raise RuntimeError(f"FIRST_ERROR={stage}")
    return "".join(chunks)


def main() -> int:
    if not ROOT.is_dir():
        raise RuntimeError("RETAINED_ROOT_MISSING")
    head = subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=ROOT, text=True
    ).strip()
    if head != EXPECTED_HEAD:
        raise RuntimeError("HEAD_MISMATCH=" + head)
    evidence = Path(
        "/content/hrpoly-cmp89-physical-owner-geometry-cold-1b9979c1-evidence.tar.gz"
    )
    if not evidence.is_file():
        raise RuntimeError("COLD_EVIDENCE_ARCHIVE_MISSING")

    for source_name, (destination, expected_blob) in FILES.items():
        data = urllib.request.urlopen(RAW_ROOT + source_name, timeout=60).read()
        actual_blob = git_blob_id(data)
        print(f"DRAFT_BLOB={source_name} GIT_BLOB={actual_blob}", flush=True)
        if actual_blob != expected_blob:
            raise RuntimeError("DRAFT_BLOB_MISMATCH=" + source_name)
        target = ROOT / destination
        if target.exists():
            raise RuntimeError("TARGET_ALREADY_EXISTS=" + destination)
        target.write_bytes(data)

    run(
        "uniform_owner_focal",
        [
            "lake", "build",
            "YangMills.RG.BalabanCMP89NeumannRectangularPhysicalUniformOwnerBound",
        ],
    )
    audit = run(
        "uniform_owner_audit",
        [
            "lake", "env", "lean",
            "YangMills/RG/"
            "BalabanCMP89NeumannRectangularPhysicalUniformOwnerBoundAudit.lean",
        ],
    )
    compact = re.sub(r"\s+", "", audit)
    if "sorryAx" in compact or "ofReduceBool" in compact:
        raise RuntimeError("FORBIDDEN_AXIOM")
    blocks = re.findall(r"'([^']+)'dependsonaxioms:\[([^\]]*)\]", compact)
    found = {name: body for name, body in blocks}
    if set(found) != {EXPECTED_DECL}:
        raise RuntimeError("AXIOM_DECLARATION_MISMATCH=" + repr(sorted(found)))
    axioms = {item for item in found[EXPECTED_DECL].split(",") if item}
    if not axioms.issubset(ALLOWED_AXIOMS):
        raise RuntimeError("AXIOM_SET=" + repr(sorted(axioms)))
    print("AXIOM_GATE=" + EXPECTED_DECL + " AXIOMS=" + ",".join(sorted(axioms)))
    print("FINAL_STATUS=PASS", flush=True)
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except Exception as error:
        print("ERROR=" + repr(error), flush=True)
        print("FINAL_STATUS=FAIL", flush=True)
        raise
