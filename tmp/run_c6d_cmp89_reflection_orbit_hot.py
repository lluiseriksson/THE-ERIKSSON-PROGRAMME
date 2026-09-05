#!/usr/bin/env python3
"""Hot diagnostic for the exact CMP89 (2.42) reflection-orbit algebra.

This retained-runtime run is diagnostic evidence only. It overlays two exact
Git blobs on the preserved C6d checkout after the reflection-branch diagnostic,
applies the textual PRE-VALIDATION guard, and builds focal plus audit
stop-on-first-error. It does not change HEAD or the Git index and cannot retire
PRE-VALIDATION.
"""

from __future__ import annotations

import hashlib
from pathlib import Path
import subprocess
import time
import urllib.request


BASE_SOURCE = "77d9f4b4d923ab1c804ca9dd6679ea304a9d3a92"
OVERLAY_SOURCE = "0428cc5721239578f5c9a8205ec547b61a23ee85"
ROOT = Path("/content/hrpoly-c6d-green-owner-prefix/repo")
FILES = {
    "YangMills/RG/BalabanCMP89NeumannReflectionOrbitAlgebra.lean":
        "bbcf22ae84afc23bd18ee87dbcd23d9dba2078dabd1e2671d47133f0bacd12c8",
    "YangMills/RG/BalabanCMP89NeumannReflectionOrbitAlgebraAudit.lean":
        "db7b306768515de00331d93dc5bfc36df87330bb06b50b647ebe7a15e3dca029",
}


def run(stage: str, command: list[str]) -> str:
    print(f"HOT_STAGE={stage} CMD={command!r}", flush=True)
    started = time.perf_counter()
    output_path = Path("/content") / f"c6d-cmp89-reflection-orbit-{stage}.stdout"
    with output_path.open("w", encoding="utf-8", newline="\n") as stream:
        child = subprocess.Popen(
            command,
            cwd=ROOT,
            text=True,
            stdout=stream,
            stderr=subprocess.STDOUT,
        )
        next_heartbeat = started + 30
        while True:
            try:
                returncode = child.wait(timeout=1)
                break
            except subprocess.TimeoutExpired:
                now = time.perf_counter()
                if now >= next_heartbeat:
                    stream.flush()
                    print(
                        f"HOT_STAGE={stage} HEARTBEAT_SECONDS={now - started:.3f}",
                        flush=True,
                    )
                    next_heartbeat = now + 30
    output = output_path.read_text(encoding="utf-8")
    print(output, end="", flush=True)
    elapsed = time.perf_counter() - started
    print(f"HOT_STAGE={stage} EXIT={returncode} SECONDS={elapsed:.3f}", flush=True)
    if returncode != 0:
        raise RuntimeError(f"HOT_FIRST_ERROR={stage}")
    return output


def main() -> None:
    if not ROOT.is_dir():
        raise RuntimeError(f"HOT_REPO_MISSING={ROOT}")
    head = subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=ROOT, text=True
    ).strip()
    print(f"HOT_BASE_HEAD={head}", flush=True)
    if head != BASE_SOURCE:
        raise RuntimeError("HOT_BASE_HEAD_MISMATCH")

    dependency = ROOT / "YangMills/RG/BalabanCMP89NeumannReflectionBranchSum.lean"
    if not dependency.is_file():
        raise RuntimeError("HOT_REFLECTION_BRANCH_DEPENDENCY_MISSING")

    for relative, expected in FILES.items():
        url = (
            "https://raw.githubusercontent.com/lluiseriksson/"
            "THE-ERIKSSON-PROGRAMME/" + OVERLAY_SOURCE + "/" + relative
        )
        with urllib.request.urlopen(url) as response:
            payload = response.read()
        actual = hashlib.sha256(payload).hexdigest()
        print(f"HOT_BLOB={relative} SHA256={actual}", flush=True)
        if actual != expected:
            raise RuntimeError(f"HOT_BLOB_HASH_MISMATCH={relative}")
        destination = ROOT / relative
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_bytes(payload)

    manifest = Path("/content/c6d-cmp89-reflection-orbit-paths.txt")
    manifest.write_text("\n".join(FILES) + "\n", encoding="utf-8", newline="\n")
    run(
        "text_guard",
        [
            "python",
            "scripts/check_lean_overlay_text.py",
            "--paths-from",
            str(manifest),
            "--require-prevalidation",
        ],
    )
    run(
        "focal",
        [
            "lake",
            "build",
            "YangMills.RG.BalabanCMP89NeumannReflectionOrbitAlgebra",
        ],
    )
    audit = run(
        "audit",
        [
            "lake",
            "env",
            "lean",
            "YangMills/RG/BalabanCMP89NeumannReflectionOrbitAlgebraAudit.lean",
        ],
    )
    normalized = "".join(audit.split())
    axiom_headers = (
        audit.count("depends on axioms:")
        + audit.count("does not depend on any axioms")
    )
    if axiom_headers != 9:
        raise RuntimeError("HOT_AXIOM_HEADER_COUNT_MISMATCH")
    for forbidden in ("sorryAx", "ofReduceBool"):
        if forbidden in normalized:
            raise RuntimeError(f"HOT_FORBIDDEN_AXIOM={forbidden}")
    print("HOT_C6D_CMP89_REFLECTION_ORBIT_PASS", flush=True)


if __name__ == "__main__":
    main()
