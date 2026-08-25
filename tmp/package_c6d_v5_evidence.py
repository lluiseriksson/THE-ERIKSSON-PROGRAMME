#!/usr/bin/env python3
"""Validate and preserve one executed C6d-v6 notebook fail-closed."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
VERIFIER = ROOT / "tmp" / "verify_c6d_root_transitive_axioms.py"
HASH_MARKERS = (
    "EVIDENCE_SHA256",
    "EVIDENCE_ARCHIVE_SHA256",
)


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest().upper()


def transcript(path: Path) -> str:
    notebook = json.loads(path.read_text(encoding="utf-8"))
    chunks: list[str] = []
    for cell in notebook.get("cells", []):
        for output in cell.get("outputs", []):
            text = output.get("text", "")
            if isinstance(text, list):
                chunks.extend(str(part) for part in text)
            elif isinstance(text, str):
                chunks.append(text)
    return "".join(chunks)


def exact_marker(text: str, name: str) -> str:
    values = re.findall(rf"(?m)^{re.escape(name)}=([A-Fa-f0-9]+)\s*$", text)
    if len(values) != 1:
        raise RuntimeError(f"C6D_EVIDENCE_MARKER_COUNT={name}:{len(values)} WANT=1")
    return values[0].upper()


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--notebook", type=Path, required=True)
    parser.add_argument("--destination", type=Path, required=True)
    args = parser.parse_args()

    notebook = args.notebook.resolve()
    destination = args.destination.resolve()
    if not notebook.is_file():
        raise RuntimeError(f"C6D_NOTEBOOK_MISSING={notebook}")
    if destination.exists():
        raise RuntimeError(f"C6D_EVIDENCE_DESTINATION_EXISTS={destination}")
    text = transcript(notebook)
    runner_hashes = {name: exact_marker(text, name) for name in HASH_MARKERS}

    destination.parent.mkdir(parents=True, exist_ok=True)
    staging = Path(tempfile.mkdtemp(prefix=".c6d-v6-evidence-", dir=destination.parent))
    try:
        copied = staging / "executed-c6d-v6.ipynb"
        verifier_json = staging / "c6d-root-transitive-axioms.json"
        shutil.copyfile(notebook, copied)
        child = subprocess.run(
            [
                sys.executable,
                str(VERIFIER),
                "--repo",
                str(ROOT),
                "--notebook",
                str(copied),
                "--json-out",
                str(verifier_json),
            ],
            cwd=ROOT,
            check=False,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
        )
        if child.returncode != 0:
            raise RuntimeError(
                "C6D_EVIDENCE_VERIFIER_FAILED "
                f"exit={child.returncode} stdout={child.stdout!r} stderr={child.stderr!r}"
            )
        verifier_result = json.loads(verifier_json.read_text(encoding="utf-8"))
        if verifier_result.get("status") != "C6D_ROOT_TRANSITIVE_AXIOMS_OK":
            raise RuntimeError("C6D_EVIDENCE_VERIFIER_STATUS_MISMATCH")
        manifest = {
            "status": "C6D_V6_EVIDENCE_PACKAGE_OK",
            "source_sha": verifier_result["source_sha"],
            "runner_revision": verifier_result["runner_revision"],
            "runner_hashes": runner_hashes,
            "files": {
                copied.name: sha256(copied),
                verifier_json.name: sha256(verifier_json),
            },
        }
        manifest_path = staging / "manifest.json"
        manifest_path.write_text(
            json.dumps(manifest, indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
            newline="\n",
        )
        sums = staging / "SHA256SUMS"
        sums.write_text(
            "".join(
                f"{sha256(path)}  {path.name}\n"
                for path in sorted(staging.iterdir(), key=lambda item: item.name)
                if path.name != "SHA256SUMS"
            ),
            encoding="utf-8",
            newline="\n",
        )
        staging.replace(destination)
    except Exception:
        shutil.rmtree(staging, ignore_errors=True)
        raise

    print(
        "C6D_V6_EVIDENCE_PACKAGE_OK "
        f"destination={destination} manifest_sha256={sha256(destination / 'manifest.json')} "
        f"notebook_sha256={sha256(destination / 'executed-c6d-v6.ipynb')}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
