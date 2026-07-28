"""Stable SHA-256 helpers for text artifacts crossing Git EOL normalization."""

from __future__ import annotations

import hashlib
from pathlib import Path


def sha256_lf(path: Path) -> str:
    raw = path.read_bytes()
    return hashlib.sha256(raw.replace(b"\r\n", b"\n")).hexdigest()


def sha256_variants(path: Path) -> set[str]:
    """Return raw, LF and CRLF digests for one textual dependency."""

    raw = path.read_bytes()
    lf = raw.replace(b"\r\n", b"\n")
    crlf = lf.replace(b"\n", b"\r\n")
    return {
        hashlib.sha256(raw).hexdigest(),
        hashlib.sha256(lf).hexdigest(),
        hashlib.sha256(crlf).hexdigest(),
    }


def validate_recorded_dependencies(
    recorded: dict[str, str],
    expected_paths: tuple[str, ...] | list[str],
    root: Path,
) -> None:
    """Require the exact dependency set and accept only EOL-equivalent bytes."""

    if set(recorded) != set(expected_paths):
        raise AssertionError("dependency path set drift")
    for relative in expected_paths:
        if recorded[relative].lower() not in sha256_variants(root / relative):
            raise AssertionError(f"dependency content drift: {relative}")
