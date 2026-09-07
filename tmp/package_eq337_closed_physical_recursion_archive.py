#!/usr/bin/env python3
"""Verify and preserve a durable closed-recursion Colab archive."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile


ROOT = Path(__file__).resolve().parents[1]
VERIFIER = ROOT / "tmp" / "verify_eq337_closed_physical_recursion_archive.py"


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest().upper()


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--archive", type=Path, required=True)
    parser.add_argument("--destination", type=Path, required=True)
    parser.add_argument("--source-sha", required=True)
    parser.add_argument("--runner-rev", required=True)
    args = parser.parse_args()
    archive = args.archive.resolve()
    destination = args.destination.resolve()
    if not archive.is_file():
        raise RuntimeError(f"EQ337_CLOSED_ARCHIVE_MISSING={archive}")
    if destination.exists():
        raise RuntimeError(f"EQ337_CLOSED_ARCHIVE_DESTINATION_EXISTS={destination}")
    destination.parent.mkdir(parents=True, exist_ok=True)
    staging = Path(tempfile.mkdtemp(prefix=".eq337-closed-archive-", dir=destination.parent))
    try:
        copied = staging / "hrpoly-eq337-closed-physical-recursion-evidence.tar.gz"
        verifier_json = staging / "eq337-closed-physical-recursion-axioms.json"
        shutil.copyfile(archive, copied)
        child = subprocess.run(
            [
                sys.executable,
                str(VERIFIER),
                "--repo", str(ROOT),
                "--archive", str(copied),
                "--source-sha", args.source_sha,
                "--runner-rev", args.runner_rev,
                "--json-out", str(verifier_json),
            ],
            cwd=ROOT,
            check=False,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
        )
        if child.returncode != 0:
            raise RuntimeError(
                "EQ337_CLOSED_ARCHIVE_VERIFIER_FAILED "
                f"exit={child.returncode} stdout={child.stdout!r} stderr={child.stderr!r}"
            )
        result = json.loads(verifier_json.read_text(encoding="utf-8"))
        if result.get("status") != "EQ337_CLOSED_PHYSICAL_RECURSION_EVIDENCE_OK":
            raise RuntimeError("EQ337_CLOSED_ARCHIVE_VERIFIER_STATUS")
        manifest = {
            "status": "EQ337_CLOSED_PHYSICAL_RECURSION_ARCHIVE_PACKAGE_OK",
            "source_sha": result["source_sha"],
            "runner_revision": result["runner_revision"],
            "transport": result["transport"],
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
        "EQ337_CLOSED_PHYSICAL_RECURSION_ARCHIVE_PACKAGE_OK "
        f"destination={destination} manifest_sha256={sha256(destination / 'manifest.json')} "
        f"archive_sha256={sha256(destination / copied.name)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
