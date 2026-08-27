#!/usr/bin/env python3
"""Verify and preserve a durable next C6d real-slice Colab archive."""

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
VERIFIER = ROOT / "tmp" / "verify_c6d_next_real_slice_archive.py"


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
        raise RuntimeError(f"C6D_NEXT_REAL_SLICE_ARCHIVE_MISSING={archive}")
    if destination.exists():
        raise RuntimeError(
            f"C6D_NEXT_REAL_SLICE_ARCHIVE_DESTINATION_EXISTS={destination}"
        )
    destination.parent.mkdir(parents=True, exist_ok=True)
    staging = Path(
        tempfile.mkdtemp(prefix=".c6d-next-real-slice-archive-", dir=destination.parent)
    )
    try:
        copied = staging / "hrpoly-c6d-next-real-slice-evidence.tar.gz"
        verifier_json = staging / "c6d-next-real-slice-axioms.json"
        shutil.copyfile(archive, copied)
        child = subprocess.run(
            [
                sys.executable,
                str(VERIFIER),
                "--repo",
                str(ROOT),
                "--archive",
                str(copied),
                "--source-sha",
                args.source_sha,
                "--runner-rev",
                args.runner_rev,
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
                "C6D_NEXT_REAL_SLICE_ARCHIVE_VERIFIER_FAILED "
                f"exit={child.returncode} stdout={child.stdout!r} "
                f"stderr={child.stderr!r}"
            )
        result = json.loads(verifier_json.read_text(encoding="utf-8"))
        if result.get("status") != "C6D_NEXT_REAL_SLICE_EVIDENCE_OK":
            raise RuntimeError("C6D_NEXT_REAL_SLICE_ARCHIVE_VERIFIER_STATUS")
        manifest = {
            "status": "C6D_NEXT_REAL_SLICE_ARCHIVE_PACKAGE_OK",
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
        "C6D_NEXT_REAL_SLICE_ARCHIVE_PACKAGE_OK "
        f"destination={destination} "
        f"manifest_sha256={sha256(destination / 'manifest.json')} "
        f"archive_sha256={sha256(destination / copied.name)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
