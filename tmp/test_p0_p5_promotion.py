#!/usr/bin/env python3
"""Synthetic positive/tamper test for the P0--P5 static promotion gate."""
from __future__ import annotations

import shutil
import subprocess
import sys
import tempfile
import hashlib
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def run_gate(fixture: Path) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [sys.executable, str(fixture / "tmp" / "audit_p0_p5_promotion.py")],
        cwd=fixture,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        check=False,
    )


def make_fixture(parent: Path) -> Path:
    fixture = parent / "repo"
    (fixture / "tmp").mkdir(parents=True)
    (fixture / "YangMills" / "RG").mkdir(parents=True)
    paths = [
        line
        for line in (ROOT / "tmp" / "P0-P5-SCRATCH-PATHS.txt")
        .read_text(encoding="utf-8")
        .splitlines()
        if line
    ]
    for relative in paths:
        target = fixture / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(ROOT / relative, target)
    for name in (
        "P0-P5-SCRATCH-PATHS.txt",
        "P0-P5-SCRATCH-MANIFEST.sha256",
        "audit_p0_p5_promotion.py",
    ):
        shutil.copyfile(ROOT / "tmp" / name, fixture / "tmp" / name)
    return fixture


def main() -> int:
    with tempfile.TemporaryDirectory(prefix="p0-p5-static-") as directory:
        fixture = make_fixture(Path(directory))
        positive = run_gate(fixture)
        if positive.returncode != 0 or "P0_P5_PROMOTION_STATIC_OK" not in positive.stdout:
            raise SystemExit("P0_P5_SELFTEST_POSITIVE_FAILED\n" + positive.stdout)

        audit = fixture / "tmp" / "P3PhysicalGreenRecurrenceAudit.lean"
        original_audit = audit.read_text(encoding="utf-8")
        audit.write_text(
            original_audit.replace(
                "import tmp.P3PhysicalGreenRecurrence",
                "import tmp.P3PhysicalOperatorDictionary",
                1,
            ),
            encoding="utf-8",
            newline="\n",
        )
        manifest = fixture / "tmp" / "P0-P5-SCRATCH-MANIFEST.sha256"
        manifest_text = manifest.read_text(encoding="utf-8")
        tampered_hash = hashlib.sha256(audit.read_bytes()).hexdigest()
        manifest.write_text(
            "\n".join(
                (f"{tampered_hash}  tmp/P3PhysicalGreenRecurrenceAudit.lean"
                 if line.endswith("  tmp/P3PhysicalGreenRecurrenceAudit.lean") else line)
                for line in manifest_text.splitlines()
            ) + "\n",
            encoding="utf-8",
            newline="\n",
        )
        import_tamper = run_gate(fixture)
        if (import_tamper.returncode == 0 or
                "sibling audit import mismatch" not in import_tamper.stdout):
            raise SystemExit("P0_P5_SELFTEST_IMPORT_TAMPER_FAILED\n" + import_tamper.stdout)
        audit.write_text(original_audit, encoding="utf-8", newline="\n")
        manifest.write_text(manifest_text, encoding="utf-8", newline="\n")

        source = fixture / "tmp" / "P4bFiniteTelescoping.lean"
        source.write_bytes(source.read_bytes() + b"\n")
        byte_tamper = run_gate(fixture)
        if byte_tamper.returncode == 0 or "manifest byte drift" not in byte_tamper.stdout:
            raise SystemExit("P0_P5_SELFTEST_BYTE_TAMPER_FAILED\n" + byte_tamper.stdout)

    print(
        "P0_P5_PROMOTION_SELFTEST_OK positive=pass "
        "audit_import_tamper=fail_closed byte_tamper=fail_closed files=33"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
