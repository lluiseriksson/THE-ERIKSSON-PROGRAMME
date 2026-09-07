#!/usr/bin/env python3
"""Fail-closed selective seal for the C6d ambient/compression boundary."""

from __future__ import annotations

import argparse
import importlib.util
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
BASE_PATH = ROOT / "tmp" / "seal_c6d_source_coercivity_green_prevalidation.py"
VERIFIER_PATH = ROOT / "tmp" / "verify_c6d_ambient_compression_cold_evidence.py"
PATH_MANIFEST = ROOT / "tmp" / "c6d-ambient-compression-cold-boundary-paths.txt"

spec = importlib.util.spec_from_file_location(
    "c6d_source_coercivity_green_seal_base", BASE_PATH
)
if spec is None or spec.loader is None:
    raise RuntimeError("C6D_AMBIENT_COMPRESSION_SEAL_BASE_IMPORT_FAILED")
base = importlib.util.module_from_spec(spec)
spec.loader.exec_module(base)
base.VERIFIER_PATH = VERIFIER_PATH
base.PATH_MANIFEST = PATH_MANIFEST


def scoped_paths(verifier) -> list[str]:
    paths = [
        line.strip()
        for line in PATH_MANIFEST.read_text(encoding="utf-8-sig").splitlines()
        if line.strip() and not line.lstrip().startswith("#")
    ]
    expected: list[str] = []
    for module in verifier.MODULES:
        expected.extend(
            (
                f"YangMills/RG/{module}.lean",
                f"YangMills/RG/{module}Audit.lean",
            )
        )
    if len(paths) != 22 or len(set(paths)) != 22 or paths != expected:
        raise RuntimeError(
            "C6D_AMBIENT_COMPRESSION_SEAL_SCOPE="
            f"paths={len(paths)}/{len(set(paths))} expected={len(expected)}"
        )
    return paths


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("archive", type=Path)
    parser.add_argument("executed_notebook", type=Path)
    parser.add_argument("--apply", action="store_true")
    args = parser.parse_args()

    verifier = base.load_verifier()
    paths = scoped_paths(verifier)
    base.require_evidence(
        verifier,
        args.archive.resolve(),
        args.executed_notebook.resolve(),
    )
    base.require_exact_scope(paths, verifier.SOURCE_SHA)

    originals: dict[str, bytes] = {}
    sealed_rows: list[tuple[str, bytes]] = []
    for relative in paths:
        original, sealed = base.transformed_bytes(relative, verifier.SOURCE_SHA)
        originals[relative] = original
        sealed_rows.append((relative, sealed))

    expected_digest = base.manifest_digest(sealed_rows)
    if not args.apply:
        print(
            "C6D_AMBIENT_COMPRESSION_SEAL_PREVIEW_OK "
            f"files={len(paths)} source_sha={verifier.SOURCE_SHA} "
            f"sealed_manifest_sha256={expected_digest}"
        )
        return 0

    written: list[str] = []
    try:
        for relative, sealed in sealed_rows:
            (ROOT / relative).write_bytes(sealed)
            written.append(relative)
        for relative in paths:
            current = (ROOT / relative).read_bytes()
            if b"PRE-VALIDATION" in current:
                raise RuntimeError(
                    f"C6D_AMBIENT_COMPRESSION_POSTWRITE_PRE_REMAINS={relative}"
                )
        actual_digest = base.manifest_digest(
            [(relative, (ROOT / relative).read_bytes()) for relative in paths]
        )
        if actual_digest != expected_digest:
            raise RuntimeError(
                "C6D_AMBIENT_COMPRESSION_POSTWRITE_DIGEST="
                f"{actual_digest} EXPECTED={expected_digest}"
            )
    except Exception:
        for relative in reversed(written):
            (ROOT / relative).write_bytes(originals[relative])
        raise

    print(
        "C6D_AMBIENT_COMPRESSION_SEAL_APPLY_OK "
        f"files={len(paths)} source_sha={verifier.SOURCE_SHA} "
        f"sealed_manifest_sha256={expected_digest}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
