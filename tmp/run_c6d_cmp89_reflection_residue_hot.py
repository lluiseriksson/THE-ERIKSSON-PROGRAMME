#!/usr/bin/env python3
"""Hot diagnostic for the exact CMP89 rectangular reflection residues."""

from __future__ import annotations

import hashlib
from pathlib import Path
import re
import subprocess
import time
import urllib.request


BASE_SOURCE = "77d9f4b4d923ab1c804ca9dd6679ea304a9d3a92"
OVERLAY_SOURCE = "dd27cd6081b0e276d3059a7fdcfb36fb0f634178"
ROOT = Path("/content/hrpoly-c6d-green-owner-prefix/repo")
FILES = {
    "YangMills/RG/BalabanCMP89NeumannReflectionResidueDictionary.lean":
        "c0ec1c415f2c57ee0a808253195c37a93894c9b5734e0b4c0a19553e123fe074",
    "YangMills/RG/BalabanCMP89NeumannReflectionResidueDictionaryAudit.lean":
        "fcad25708a00fe0d440cb6fa3b682829b7cd62e2df3ec0f15cbbe021cc933f43",
}


def run(stage: str, command: list[str]) -> str:
    print(f"HOT_STAGE={stage} CMD={command!r}", flush=True)
    started = time.perf_counter()
    output_path = Path("/content") / f"c6d-cmp89-reflection-residue-{stage}.stdout"
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

    dependency = ROOT / "YangMills/RG/BalabanCMP89NeumannReflectionScaleDictionary.lean"
    if not dependency.is_file():
        raise RuntimeError("HOT_REFLECTION_SCALE_DEPENDENCY_MISSING")

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

    manifest = Path("/content/c6d-cmp89-reflection-residue-paths.txt")
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
            "YangMills.RG.BalabanCMP89NeumannReflectionResidueDictionary",
        ],
    )
    audit = run(
        "audit",
        [
            "lake",
            "env",
            "lean",
            "YangMills/RG/BalabanCMP89NeumannReflectionResidueDictionaryAudit.lean",
        ],
    )
    normalized = "".join(audit.split())
    readout_count = (
        normalized.count("dependsonaxioms:[")
        + normalized.count("doesnotdependonanyaxioms")
    )
    if readout_count != 8:
        raise RuntimeError("HOT_AXIOM_HEADER_COUNT_MISMATCH")
    for forbidden in ("sorryAx", "ofReduceBool"):
        if forbidden in normalized:
            raise RuntimeError(f"HOT_FORBIDDEN_AXIOM={forbidden}")
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    for body in re.findall(r"dependsonaxioms:\[([^]]*)\]", normalized):
        unexpected = {name for name in body.split(",") if name} - allowed
        if unexpected:
            raise RuntimeError(
                "HOT_UNEXPECTED_AXIOMS=" + ",".join(sorted(unexpected))
            )
    print("HOT_C6D_CMP89_REFLECTION_RESIDUE_PASS", flush=True)


if __name__ == "__main__":
    main()
