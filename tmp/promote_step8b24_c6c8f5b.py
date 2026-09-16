#!/usr/bin/env python3
"""Fail-closed materializer for the C6c.8 f2g--f5b scratch closure.

The default mode is read-only.  ``--apply`` writes exactly the forty
LF-normalized promoted files pinned by
``audit_step8b24_c6c8f5b_promotion_preview.py``.  It never overwrites an
existing target and it leaves every PRE-VALIDATION notice in place.

This script is transport instrumentation only.  A successful materialization
is not Lean, Lake, or axiom-oracle evidence.
"""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
PREVIEW_PATH = ROOT / "tmp" / "audit_step8b24_c6c8f5b_promotion_preview.py"


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest().upper()


def load_preview():
    spec = importlib.util.spec_from_file_location("c6c8f5b_preview", PREVIEW_PATH)
    if spec is None or spec.loader is None:
        raise SystemExit("C6C8F5B_PREVIEW_IMPORT_FAILED")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--apply",
        action="store_true",
        help="materialize the exact pinned promoted paths",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    preview = load_preview()

    paths = preview.read_paths()
    rows = preview.read_closure(paths)
    preview.check_new_surface()
    digest = preview.manifest_digest(rows)
    if digest != preview.PROMOTED_MANIFEST_SHA256:
        raise SystemExit(f"C6C8F5B_PROMOTED_MANIFEST_MISMATCH={digest}")

    if not args.apply:
        print(
            "C6C8F5B_MATERIALIZATION_PREVIEW_OK "
            f"files={len(rows)} manifest_sha256={digest}"
        )
        return 0

    created: list[Path] = []
    try:
        for relative, data in rows:
            target = ROOT / relative
            if target.exists():
                raise RuntimeError(f"C6C8F5B_TARGET_EXISTS={relative}")
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(data)
            created.append(target)

        written = [(p.relative_to(ROOT).as_posix(), p.read_bytes()) for p in created]
        actual = preview.manifest_digest(written)
        if actual != digest:
            raise RuntimeError(f"C6C8F5B_WRITTEN_MANIFEST_MISMATCH={actual}")
        if any(data.count(b"PRE-VALIDATION:") != 1 for _, data in written):
            raise RuntimeError("C6C8F5B_WRITTEN_PREVALIDATION_MISMATCH")
    except Exception:
        for target in reversed(created):
            target.unlink(missing_ok=True)
        raise

    print(
        "C6C8F5B_MATERIALIZATION_OK "
        f"files={len(created)} manifest_sha256={digest}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
