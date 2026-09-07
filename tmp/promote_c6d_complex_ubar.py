#!/usr/bin/env python3
"""Fail-closed promotion of the six-file complex Ubar boundary.

The materializer is read-only unless ``--apply`` is supplied.  Promotion is
blocked until the Eq. (3.37) complex-coordinate prerequisite has had its
PRE-VALIDATION marker retired.  It never edits ``YangMillsCore.lean`` and
rolls back every destination it creates if a later write fails.
"""

from __future__ import annotations

import argparse
import importlib.util
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
PREVIEW = ROOT / "tmp" / "audit_c6d_complex_ubar_promotion_preview.py"
PREREQUISITES = (
    ROOT / "YangMills" / "RG" / "BalabanCMP99Eq337PhysicalComplexPerturbedBackground.lean",
    ROOT / "YangMills" / "RG" / "BalabanCMP99Eq337PhysicalComplexPerturbedBackgroundAudit.lean",
)


def load_preview():
    spec = importlib.util.spec_from_file_location("c6d_complex_ubar_preview", PREVIEW)
    if spec is None or spec.loader is None:
        raise RuntimeError("C6D_COMPLEX_UBAR_PREVIEW_IMPORT_FAILED")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def require_sealed_prerequisites() -> None:
    for path in PREREQUISITES:
        if not path.is_file():
            raise RuntimeError(f"C6D_COMPLEX_UBAR_PREREQUISITE_MISSING={path}")
        if "PRE-VALIDATION:" in path.read_text(encoding="utf-8-sig"):
            raise RuntimeError(
                "C6D_COMPLEX_UBAR_PREREQUISITE_NOT_SEALED="
                + str(path.relative_to(ROOT))
            )


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--apply", action="store_true")
    args = parser.parse_args()

    preview = load_preview()
    paths = preview.read_paths()
    rows = preview.read_layer(paths)
    preview.check_surface(paths)
    digest = preview.manifest_digest(rows)
    if digest != preview.PROMOTED_MANIFEST_SHA256:
        raise RuntimeError(f"C6D_COMPLEX_UBAR_PROMOTED_MANIFEST_MISMATCH={digest}")
    require_sealed_prerequisites()

    if not args.apply:
        print(
            "C6D_COMPLEX_UBAR_MATERIALIZATION_PREVIEW_OK "
            f"files={len(rows)} declarations={len(preview.EXPECTED)} "
            f"manifest_sha256={digest}"
        )
        return 0

    written: list[Path] = []
    try:
        for relative, data in rows:
            destination = ROOT / relative
            if destination.exists():
                raise RuntimeError(f"C6D_COMPLEX_UBAR_TARGET_EXISTS={relative}")
            destination.write_bytes(data)
            written.append(destination)
        for relative, data in rows:
            if (ROOT / relative).read_bytes() != data:
                raise RuntimeError(f"C6D_COMPLEX_UBAR_POSTWRITE_MISMATCH={relative}")
    except Exception:
        for path in reversed(written):
            path.unlink(missing_ok=True)
        raise

    print(
        "C6D_COMPLEX_UBAR_MATERIALIZATION_APPLY_OK "
        f"files={len(rows)} declarations={len(preview.EXPECTED)} "
        f"manifest_sha256={digest}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
