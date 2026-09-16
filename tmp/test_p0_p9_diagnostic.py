#!/usr/bin/env python3
"""Self-test the P0--P9 static gate: exact bytes pass, one-byte drift fails."""

from __future__ import annotations

from pathlib import Path
import shutil
import subprocess
import sys
import tempfile


ROOT = Path(__file__).resolve().parents[1]


def run(root: Path) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [sys.executable, str(root / "tmp/audit_p0_p9_diagnostic.py")],
        cwd=root,
        capture_output=True,
        text=True,
        encoding="utf-8",
    )


def main() -> int:
    positive = run(ROOT)
    if positive.returncode != 0:
        raise SystemExit("P0_P9_SELFTEST_POSITIVE_FAILED=" + positive.stdout + positive.stderr)

    with tempfile.TemporaryDirectory(prefix="p0-p9-gate-") as raw:
        clone = Path(raw)
        (clone / "tmp").mkdir()
        (clone / "scripts").mkdir()
        for name in (
            "P0-P8-SCRATCH-PATHS.txt",
            "P0-P8-SCRATCH-MANIFEST.sha256",
            "P0-P9-SCRATCH-PATHS.txt",
            "P0-P9-SCRATCH-MANIFEST.sha256",
            "audit_p0_p8_diagnostic.py",
            "audit_p0_p9_diagnostic.py",
        ):
            shutil.copy2(ROOT / "tmp" / name, clone / "tmp" / name)
        paths = (ROOT / "tmp/P0-P9-SCRATCH-PATHS.txt").read_text(
            encoding="utf-8-sig"
        ).splitlines()
        for relative in paths:
            source = ROOT / relative
            target = clone / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(source, target)

        target = clone / "tmp/P9SourceSeparatedPrefixCombesThomas.lean"
        target.write_bytes(target.read_bytes() + b"\n-- deliberate one-byte-class drift\n")
        negative = run(clone)
        if negative.returncode == 0 or "P0_P9_BLOB_DRIFT=" not in (
            negative.stdout + negative.stderr
        ):
            raise SystemExit(
                "P0_P9_SELFTEST_TAMPER_NOT_REJECTED="
                + negative.stdout
                + negative.stderr
            )

    print("P0_P9_DIAGNOSTIC_SELFTEST_OK positive=pass tamper=fail_closed files=39")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
