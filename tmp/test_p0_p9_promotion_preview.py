#!/usr/bin/env python3
"""Positive/tamper self-test for the full P0--P9 promotion gates."""

from __future__ import annotations

import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
IMPORT = re.compile(r"(?m)^import\s+(YangMills\.[^\s]+)")
EXISTING = (
    "BalabanCMP99SourceCanonicalPrefixTower.lean",
    "BalabanCMP99SourceCanonicalPrefixTowerAudit.lean",
    "BalabanCMP99SourcePrefixPoincare.lean",
    "BalabanCMP99SourcePrefixPoincareAudit.lean",
)
HELPERS = (
    "audit_p0_p5_promotion.py",
    "audit_p0_p5_promotion_preview.py",
    "audit_p0_p9_promotion.py",
    "audit_p0_p9_promotion_preview.py",
    "audit_step8b23_promotion_preview.py",
    "audit_step8b24_promotion_preview.py",
)


def run(fixture: Path, name: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [sys.executable, str(fixture / "tmp" / name)],
        cwd=fixture,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        check=False,
    )


def make_fixture(parent: Path) -> Path:
    fixture = parent / "repo"
    (fixture / "tmp").mkdir(parents=True)
    (fixture / "scripts").mkdir(parents=True)
    (fixture / "YangMills" / "RG").mkdir(parents=True)
    paths = [
        line
        for line in (ROOT / "tmp" / "P0-P9-SCRATCH-PATHS.txt")
        .read_text(encoding="utf-8")
        .splitlines()
        if line
    ]
    for relative in paths:
        target = fixture / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(ROOT / relative, target)
    for name in (
        "P0-P9-SCRATCH-PATHS.txt",
        "P0-P9-SCRATCH-MANIFEST.sha256",
        *HELPERS,
    ):
        shutil.copyfile(ROOT / "tmp" / name, fixture / "tmp" / name)
    shutil.copyfile(
        ROOT / "scripts" / "check_lean_overlay_text.py",
        fixture / "scripts" / "check_lean_overlay_text.py",
    )
    for name in EXISTING:
        shutil.copyfile(
            ROOT / "YangMills" / "RG" / name,
            fixture / "YangMills" / "RG" / name,
        )

    external: set[str] = set()
    for relative in paths:
        text = (ROOT / relative).read_text(encoding="utf-8-sig")
        external.update(IMPORT.findall(text))
    for module in sorted(external):
        relative = Path(*module.split(".")).with_suffix(".lean")
        source = ROOT / relative
        target = fixture / relative
        if target.exists():
            continue
        if not source.is_file():
            raise RuntimeError(f"missing fixture dependency: {module}")
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, target)
    return fixture


def expect_ok(fixture: Path) -> None:
    static = run(fixture, "audit_p0_p9_promotion.py")
    if static.returncode != 0 or "P0_P9_PROMOTION_STATIC_OK" not in static.stdout:
        raise SystemExit("P0_P9_STATIC_POSITIVE_FAILED\n" + static.stdout)
    preview = run(fixture, "audit_p0_p9_promotion_preview.py")
    if preview.returncode != 0 or "P0_P9_PROMOTION_PREVIEW_OK" not in preview.stdout:
        raise SystemExit("P0_P9_PREVIEW_POSITIVE_FAILED\n" + preview.stdout)


def main() -> int:
    with tempfile.TemporaryDirectory(prefix="p0-p9-promotion-") as directory:
        root = Path(directory)
        fixture = make_fixture(root / "positive")
        expect_ok(fixture)

        fixture = make_fixture(root / "source-tamper")
        source = fixture / "tmp" / "P8SourceSeparatedRegionalPrefixGreen.lean"
        source.write_bytes(source.read_bytes() + b"\n")
        result = run(fixture, "audit_p0_p9_promotion_preview.py")
        if result.returncode == 0 or "raw manifest byte drift" not in result.stdout:
            raise SystemExit("P0_P9_SOURCE_TAMPER_FAILED\n" + result.stdout)

        fixture = make_fixture(root / "existing-drift")
        existing = (
            fixture
            / "YangMills"
            / "RG"
            / "BalabanCMP99SourcePrefixPoincare.lean"
        )
        existing.write_bytes(existing.read_bytes() + b"\nexample : True := by trivial\n")
        result = run(fixture, "audit_p0_p9_promotion_preview.py")
        if result.returncode == 0 or "already-promoted visible code drift" not in result.stdout:
            raise SystemExit("P0_P9_EXISTING_DRIFT_FAILED\n" + result.stdout)

        fixture = make_fixture(root / "collision")
        collision = (
            fixture
            / "YangMills"
            / "RG"
            / "BalabanCMP89SourceSeparatedAmbientPrefixPrecision.lean"
        )
        collision.write_text("-- occupied\n", encoding="utf-8", newline="\n")
        result = run(fixture, "audit_p0_p9_promotion_preview.py")
        if result.returncode == 0 or "tracked target already exists" not in result.stdout:
            raise SystemExit("P0_P9_COLLISION_FAILED\n" + result.stdout)

    print(
        "P0_P9_PROMOTION_SELFTEST_OK positive=pass "
        "source_tamper=fail_closed existing_drift=fail_closed "
        "target_collision=fail_closed files=39"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
