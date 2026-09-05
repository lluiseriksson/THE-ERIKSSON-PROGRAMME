#!/usr/bin/env python3
"""Retained-runtime diagnostic for the uniform Eq. (3.42) value adapter.

This is deliberately a hot diagnostic, not cold seal evidence.  It may run
only after the C6d Green owner-prefix archive and executed notebook have been
downloaded.  The script overlays two exact Git blobs on that completed cold
checkout, builds the focal and audit stop-on-first-error, and emits a distinct
HOT sentinel.  It never edits the Git index or changes HEAD.
"""

from __future__ import annotations

import hashlib
import os
from pathlib import Path
import subprocess
import time
import urllib.request


BASE_SOURCE = "77d9f4b4d923ab1c804ca9dd6679ea304a9d3a92"
OVERLAY_SOURCE = "4e1152f5f89dbe5a291b5dd2d588911310c6baed"
ROOT = Path("/content/hrpoly-c6d-green-owner-prefix/repo")
FILES = {
    "YangMills/RG/BalabanCMP99Eq342UniformCertificateFromValueBound.lean":
        "b749caab4e31df7c6d35862af8fa414d8753c691c8be6d71cb5b322c2d91a05f",
    "YangMills/RG/BalabanCMP99Eq342UniformCertificateFromValueBoundAudit.lean":
        "faa513d255be294eef1c6f0b0c54e376088d89ec6c62e19713d44b3a3712df79",
}


def run(stage: str, command: list[str]) -> str:
    print(f"HOT_STAGE={stage} CMD={command!r}", flush=True)
    started = time.perf_counter()
    output_path = Path("/content") / f"c6d-uniform-value-{stage}.stdout"
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
    print(
        f"HOT_STAGE={stage} EXIT={returncode} SECONDS={elapsed:.3f}",
        flush=True,
    )
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

    manifest = Path("/content/c6d-uniform-certificate-from-value-paths.txt")
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
            "YangMills.RG.BalabanCMP99Eq342UniformCertificateFromValueBound",
        ],
    )
    audit = run(
        "audit",
        [
            "lake",
            "env",
            "lean",
            "YangMills/RG/BalabanCMP99Eq342UniformCertificateFromValueBoundAudit.lean",
        ],
    )
    normalized = "".join(audit.split())
    if audit.count("axioms") != 1:
        raise RuntimeError("HOT_AXIOM_HEADER_COUNT_MISMATCH")
    for forbidden in ("sorryAx", "ofReduceBool"):
        if forbidden in normalized:
            raise RuntimeError(f"HOT_FORBIDDEN_AXIOM={forbidden}")
    print("HOT_C6D_UNIFORM_CERTIFICATE_FROM_VALUE_PASS", flush=True)


if __name__ == "__main__":
    main()
