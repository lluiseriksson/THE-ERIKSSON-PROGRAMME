#!/usr/bin/env python3
"""Lightweight parser/blob tests for the split diameter seal."""

from __future__ import annotations

import importlib.util
import json
from pathlib import Path
import tarfile


ROOT = Path(__file__).resolve().parents[1]
VERIFIER = ROOT / "tmp" / "verify_c6d_terminal_block_diameter_from_green_v4_evidence.py"
FAIL_ARCHIVE = (
    ROOT
    / "validation-evidence"
    / "c6d-terminal-block-diameter-root-fail-a2715bf8-20260829-v4"
    / "hrpoly-c6d-terminal-block-diameter-evidence.tar.gz"
)
FAIL_ROOT_STAGE = "02_c6d_terminal_block_diameter_yang_mills_core_root"


def load_verifier():
    spec = importlib.util.spec_from_file_location("diameter_green_v4_verifier", VERIFIER)
    if spec is None or spec.loader is None:
        raise RuntimeError("DIAMETER_GREEN_V4_TEST_IMPORT_FAILED")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def root_text() -> str:
    with tarfile.open(FAIL_ARCHIVE, "r:gz") as archive:
        members = archive.getmembers()
        evidence = next(m for m in members if m.name.endswith("/evidence.json"))
        payload = json.load(archive.extractfile(evidence))
        index = next(
            i for i, record in enumerate(payload["records"])
            if record["stage"] == FAIL_ROOT_STAGE
        )
        prefix = evidence.name.rsplit("/", 1)[0]
        member_name = f"{prefix}/{index:03d}-{FAIL_ROOT_STAGE}.stdout"
        member = next(m for m in members if m.name == member_name)
        extracted = archive.extractfile(member)
        if extracted is None:
            raise RuntimeError("DIAMETER_GREEN_V4_TEST_ROOT_LOG_UNREADABLE")
        return extracted.read().decode("utf-8")


def main() -> int:
    verifier = load_verifier()
    verifier.require_blob_identity()
    verifier.require_diameter_in_root(root_text())
    print("DIAMETER_GREEN_V4_LIGHTWEIGHT_TEST_OK blobs=2 declarations=4")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
