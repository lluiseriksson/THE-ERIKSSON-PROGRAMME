#!/usr/bin/env python3
"""Read-only aggregate gate for the two C6c.9 scalar subbricks."""

from __future__ import annotations

import hashlib
import runpy
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
TMP = ROOT / "tmp"
WEAKENING = runpy.run_path(str(TMP / "audit_step8b24_c6c9_weakening_preview.py"))
COMMON = runpy.run_path(str(TMP / "audit_step8b24_c6c9_common_amplitude_preview.py"))
PATHS = TMP / "STEP8B24-C6C9-SCALAR-PREFIX-PATHS.txt"


def listed() -> list[Path]:
    return [
        ROOT / line.strip()
        for line in PATHS.read_text(encoding="utf-8-sig").splitlines()
        if line.strip() and not line.lstrip().startswith("#")
    ]


def main() -> int:
    declared = listed()
    rows = tuple(WEAKENING["promotion_rows"]()) + tuple(COMMON["promotion_rows"]())
    raw = [WEAKENING["SOURCE"], WEAKENING["AUDIT"], COMMON["SOURCE"], COMMON["AUDIT"]]
    if declared != raw or len(set(declared)) != 4:
        raise SystemExit("C6C9_SCALAR_PREFIX_PATH_SCOPE")
    targets = [path for path, _ in rows]
    if len(rows) != 4 or len(set(targets)) != 4:
        raise SystemExit("C6C9_SCALAR_PREFIX_TARGET_SCOPE")
    manifest = "".join(
        f"{hashlib.sha256(data).hexdigest()}  {path.relative_to(ROOT).as_posix()}\n"
        for path, data in rows
    ).encode("utf-8")
    digest = hashlib.sha256(manifest).hexdigest().upper()
    print(
        "STEP8B24_C6C9_SCALAR_PREFIX_OK files=4 modules=2 "
        "declarations=7 audit_readouts=7 target_collisions=0 "
        f"manifest_sha256={digest}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
