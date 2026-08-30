#!/usr/bin/env python3
"""Retained-runtime diagnostic for the CMP89 Neumann regional precision.

This is a hot diagnostic, never cold seal evidence.  It may run only after
the active C6d cold gate has completed and its evidence has been preserved.
The script overlays two exact Git blobs, checks their textual contract, and
builds the focal plus audit stop-on-first-error.  It never changes HEAD or the
Git index.
"""

from __future__ import annotations

import hashlib
from pathlib import Path
import subprocess
import time
import urllib.request


BASE_SOURCE = "77d9f4b4d923ab1c804ca9dd6679ea304a9d3a92"
OVERLAY_SOURCE = "ad8299fbed9afcf840bd30dc7d2aa8ac145f0ef0"
ROOT = Path("/content/hrpoly-c6d-green-owner-prefix/repo")
FILES = {
    "YangMills/RG/BalabanCMP89SourceNeumannRegionalPrecision.lean":
        "4eefd5c2460a0bb3c91651b7344382de00dc4d318e4153926f045c442a46ae83",
    "YangMills/RG/BalabanCMP89SourceNeumannRegionalPrecisionAudit.lean":
        "eb8cb9d56a7f1dd3bdff5b423a5deb8effa4bb98b524963e8dcf9e3d80cd9838",
}


def run(stage: str, command: list[str]) -> str:
    print(f"HOT_STAGE={stage} CMD={command!r}", flush=True)
    started = time.perf_counter()
    output_path = Path("/content") / f"c6d-cmp89-neumann-{stage}.stdout"
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

    manifest = Path("/content/c6d-cmp89-neumann-paths.txt")
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
            "YangMills.RG.BalabanCMP89SourceNeumannRegionalPrecision",
        ],
    )
    audit = run(
        "audit",
        [
            "lake",
            "env",
            "lean",
            "YangMills/RG/BalabanCMP89SourceNeumannRegionalPrecisionAudit.lean",
        ],
    )
    normalized = "".join(audit.split())
    if audit.count("axioms") != 2:
        raise RuntimeError("HOT_AXIOM_HEADER_COUNT_MISMATCH")
    for forbidden in ("sorryAx", "ofReduceBool"):
        if forbidden in normalized:
            raise RuntimeError(f"HOT_FORBIDDEN_AXIOM={forbidden}")
    print("HOT_C6D_CMP89_NEUMANN_PRECISION_PASS", flush=True)


if __name__ == "__main__":
    main()
