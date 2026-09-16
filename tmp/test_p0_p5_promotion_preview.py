#!/usr/bin/env python3
"""Positive/tamper self-test for the deterministic P0--P5 preview."""

from __future__ import annotations

import shutil
import subprocess
import sys
import tempfile
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]


def run_preview(fixture: Path) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [sys.executable, str(fixture / "tmp" / "audit_p0_p5_promotion_preview.py")],
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
        "audit_p0_p5_promotion_preview.py",
        "audit_step8b23_promotion_preview.py",
        "audit_step8b24_promotion_preview.py",
    ):
        shutil.copyfile(ROOT / "tmp" / name, fixture / "tmp" / name)
    shutil.copyfile(
        ROOT / "scripts" / "check_lean_overlay_text.py",
        fixture / "scripts" / "check_lean_overlay_text.py",
    )
    for name in (
        "BalabanCMP99SourceRetainedGeneratedTerminalBridge.lean",
        "BalabanCMP99SourceTowerCoarseCovariance.lean",
        "BalabanCMP99SourceSeparatedGeneratedPhysicalAmbientDictionary.lean",
        "FinitePiLpTypedKernelReindexAlgebra.lean",
    ):
        shutil.copyfile(
            ROOT / "YangMills" / "RG" / name,
            fixture / "YangMills" / "RG" / name,
        )
    return fixture


def main() -> int:
    with tempfile.TemporaryDirectory(prefix="p0-p5-preview-") as directory:
        fixture = make_fixture(Path(directory))
        positive = run_preview(fixture)
        if positive.returncode != 0 or "P0_P5_PROMOTION_PREVIEW_OK" not in positive.stdout:
            raise SystemExit("P0_P5_PREVIEW_SELFTEST_POSITIVE_FAILED\n" + positive.stdout)

        source = fixture / "tmp" / "P4bFiniteTelescoping.lean"
        source.write_bytes(source.read_bytes() + b"\n")
        source_tamper = run_preview(fixture)
        if (
            source_tamper.returncode == 0
            or "raw manifest byte drift" not in source_tamper.stdout
        ):
            raise SystemExit(
                "P0_P5_PREVIEW_SELFTEST_SOURCE_TAMPER_FAILED\n" + source_tamper.stdout
            )

        fixture = make_fixture(Path(directory) / "second")
        manifest = fixture / "tmp" / "P0-P5-SCRATCH-MANIFEST.sha256"
        manifest.write_bytes(manifest.read_bytes() + b"\n")
        manifest_tamper = run_preview(fixture)
        if (
            manifest_tamper.returncode == 0
            or "raw manifest digest drift" not in manifest_tamper.stdout
        ):
            raise SystemExit(
                "P0_P5_PREVIEW_SELFTEST_MANIFEST_TAMPER_FAILED\n"
                + manifest_tamper.stdout
            )

        fixture = make_fixture(Path(directory) / "third")
        collision = (
            fixture
            / "YangMills"
            / "RG"
            / "BalabanCMP99SourceCanonicalPrefixTower.lean"
        )
        collision.write_text("-- occupied\n", encoding="utf-8", newline="\n")
        collision_tamper = run_preview(fixture)
        if (
            collision_tamper.returncode == 0
            or "tracked target already exists" not in collision_tamper.stdout
        ):
            raise SystemExit(
                "P0_P5_PREVIEW_SELFTEST_COLLISION_FAILED\n" + collision_tamper.stdout
            )

    print(
        "P0_P5_PROMOTION_PREVIEW_SELFTEST_OK positive=pass "
        "source_tamper=fail_closed manifest_tamper=fail_closed "
        "target_collision=fail_closed files=33"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
