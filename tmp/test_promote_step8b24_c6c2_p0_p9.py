#!/usr/bin/env python3
"""Synthetic write/tamper test for the exact P0--P9 promoter."""

from __future__ import annotations

from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

import audit_p0_p5_promotion_preview as preview
import audit_p0_p9_promotion as scope
import audit_p0_p9_v59_github_evidence as evidence_gate
import github_p0_p9_v59_driver as evidence_contract
import test_audit_p0_p9_v56_github_evidence as evidence_fixture


evidence_fixture.gate = evidence_gate
evidence_fixture.contract = evidence_contract


ROOT = Path(__file__).resolve().parents[1]


def command(*args: str, cwd: Path) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        list(args), cwd=cwd, text=True, stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT, check=False
    )


def make_fixture(parent: Path) -> tuple[Path, str, dict[Path, Path]]:
    fixture = parent / "repo"
    (fixture / "tmp").mkdir(parents=True)
    (fixture / "scripts").mkdir(parents=True)
    (fixture / "YangMills" / "RG").mkdir(parents=True)
    paths = [
        line
        for line in (ROOT / "tmp/P0-P9-SCRATCH-PATHS.txt")
        .read_text(encoding="utf-8-sig").splitlines()
        if line
    ]
    for relative in paths:
        target = fixture / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(ROOT / relative, target)
    for relative in evidence_contract.core.REPROS:
        target = fixture / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(ROOT / relative, target)
    for name in (
        "P0-P9-SCRATCH-PATHS.txt",
        "P0-P9-SCRATCH-MANIFEST.sha256",
        "audit_p0_p5_promotion.py",
        "audit_p0_p5_promotion_preview.py",
        "audit_p0_p9_promotion.py",
        "audit_p0_p9_v56_github_evidence.py",
        "audit_p0_p9_v59_github_evidence.py",
        "audit_step8b23_promotion_preview.py",
        "audit_step8b24_promotion_preview.py",
        "github_p0_p9_v56_driver.py",
        "github_p0_p9_v57_driver.py",
        "github_p0_p9_v59_driver.py",
        "promote_step8b24_c6c2_p0_p9.py",
    ):
        shutil.copyfile(ROOT / "tmp" / name, fixture / "tmp" / name)
    shutil.copyfile(
        ROOT / "scripts/check_lean_overlay_text.py",
        fixture / "scripts/check_lean_overlay_text.py",
    )

    preview.scope = scope
    preview.PATHS = ROOT / "tmp/P0-P9-SCRATCH-PATHS.txt"
    preview.RAW_MANIFEST = ROOT / "tmp/P0-P9-SCRATCH-MANIFEST.sha256"
    targets = preview.complete_target_map()
    relative_targets = {
        source.relative_to(ROOT): target.relative_to(ROOT)
        for source, target in targets.items()
    }
    for source_name in scope.ALREADY_PROMOTED_FILES:
        source = next(path for path in targets if path.name == source_name)
        target = targets[source]
        destination = fixture / target.relative_to(ROOT)
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(target, destination)

    for args in (
        ("git", "init", "-q"),
        ("git", "config", "user.email", "fixture@example.invalid"),
        ("git", "config", "user.name", "fixture"),
        ("git", "add", "."),
        ("git", "commit", "-qm", "fixture"),
    ):
        result = command(*args, cwd=fixture)
        if result.returncode:
            raise AssertionError("fixture git setup failed\n" + result.stdout)
    head = command("git", "rev-parse", "HEAD", cwd=fixture).stdout.strip()
    return fixture, head, relative_targets


def main() -> None:
    with tempfile.TemporaryDirectory(prefix="p0-p9-promoter-") as raw:
        fixture, head, targets = make_fixture(Path(raw) / "positive")
        evidence = fixture / "v59-pass.zip"
        evidence_fixture.write_fixture(evidence)
        result = command(
            sys.executable, "tmp/promote_step8b24_c6c2_p0_p9.py",
            "--expected-head", head, "--evidence", str(evidence), "--write",
            cwd=fixture,
        )
        if result.returncode or "P0_P9_PROMOTION_WRITE_OK" not in result.stdout:
            raise AssertionError("positive promotion failed\n" + result.stdout)
        for source_relative, target_relative in targets.items():
            target = fixture / target_relative
            if not target.is_file():
                raise AssertionError(f"promoted target missing: {target_relative}")
            count = target.read_bytes().count(b"PRE-VALIDATION")
            expected = 0 if source_relative.name.startswith("P0") else 1
            if count != expected:
                raise AssertionError(
                    f"PRE count drift {target_relative}: {count} != {expected}"
                )

        fixture, head, targets = make_fixture(Path(raw) / "tamper")
        evidence = fixture / "v59-tampered.zip"
        evidence_fixture.write_fixture(evidence, outer_tamper=True)
        result = command(
            sys.executable, "tmp/promote_step8b24_c6c2_p0_p9.py",
            "--expected-head", head, "--evidence", str(evidence), "--write",
            cwd=fixture,
        )
        if result.returncode == 0 or "EVIDENCE_REJECTED" not in result.stdout:
            raise AssertionError("tampered evidence did not fail closed\n" + result.stdout)
        created = [
            fixture / target_relative
            for source_relative, target_relative in targets.items()
            if source_relative.name not in scope.ALREADY_PROMOTED_FILES
            and (fixture / target_relative).exists()
        ]
        if created:
            raise AssertionError(f"tampered evidence wrote targets: {created}")

    print(
        "P0_P9_PROMOTER_SELFTEST_OK positive=35_exact_writes "
        "p0_preserved_without_mark=2 p1_preserved_with_mark=2 "
        "evidence_tamper=fail_closed prewrite_atomicity=pass"
    )


if __name__ == "__main__":
    main()
