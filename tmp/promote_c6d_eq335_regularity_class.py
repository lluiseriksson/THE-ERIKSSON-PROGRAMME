#!/usr/bin/env python3
"""Fail-closed materializer for the four-file CMP99 (3.35) class layer.

The default mode is read-only.  ``--apply`` first requires the two exact
geometric prerequisite modules from the forty-file C6c.8 prefix, then writes
the four pinned LF-normalized files without overwriting any target.  This is
transport instrumentation, not compiler evidence.
"""

from __future__ import annotations

import argparse
import importlib.util
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
PREVIEW_PATH = ROOT / "tmp" / "audit_c6d_eq335_regularity_class_promotion_preview.py"


def load_preview():
    spec = importlib.util.spec_from_file_location("c6d_eq335_preview", PREVIEW_PATH)
    if spec is None or spec.loader is None:
        raise SystemExit("C6D_EQ335_PREVIEW_IMPORT_FAILED")
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
    rows = preview.read_layer(paths)
    preview.check_surface(paths)
    digest = preview.manifest_digest(rows)
    if digest != preview.PROMOTED_MANIFEST_SHA256:
        raise SystemExit(f"C6D_EQ335_PROMOTED_MANIFEST_MISMATCH={digest}")

    if not args.apply:
        print(
            "C6D_EQ335_MATERIALIZATION_PREVIEW_OK "
            f"files={len(rows)} manifest_sha256={digest}"
        )
        return 0

    missing = [
        relative
        for relative in preview.PREREQUISITE_TARGETS
        if not (ROOT / relative).is_file()
    ]
    if missing:
        raise SystemExit(f"C6D_EQ335_PREREQUISITES_MISSING={missing!r}")

    created: list[Path] = []
    try:
        for relative, data in rows:
            target = ROOT / relative
            if target.exists():
                raise RuntimeError(f"C6D_EQ335_TARGET_EXISTS={relative}")
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(data)
            created.append(target)
        written = [(p.relative_to(ROOT).as_posix(), p.read_bytes()) for p in created]
        actual = preview.manifest_digest(written)
        if actual != digest:
            raise RuntimeError(f"C6D_EQ335_WRITTEN_MANIFEST_MISMATCH={actual}")
        if any(data.count(b"PRE-VALIDATION:") != 1 for _, data in written):
            raise RuntimeError("C6D_EQ335_WRITTEN_PREVALIDATION_MISMATCH")
    except Exception:
        for target in reversed(created):
            target.unlink(missing_ok=True)
        raise

    print(
        "C6D_EQ335_MATERIALIZATION_OK "
        f"files={len(created)} manifest_sha256={digest}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
