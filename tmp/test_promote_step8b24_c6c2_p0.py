#!/usr/bin/env python3
"""Synthetic positive/tamper test for the fail-closed P0 promoter."""

from __future__ import annotations

import hashlib
import importlib.util
import json
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
RUN = "31991954503"
SOURCE_SHA = "534493728038813f3772f8b3b073237f4da1884e"


def command(*args: str, cwd: Path) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        list(args),
        cwd=cwd,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        check=False,
    )


def make_fixture(parent: Path) -> tuple[Path, str]:
    fixture = parent / "repo"
    (fixture / "tmp").mkdir(parents=True)
    (fixture / "scripts").mkdir(parents=True)
    (fixture / "YangMills" / "RG").mkdir(parents=True)
    (fixture / "docs").mkdir(parents=True)
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
        "P0-P9-SCRATCH-PATHS.txt",
        "audit_p0_p9_executed_notebook.py",
        "audit_p0_p5_promotion.py",
        "audit_p0_p5_promotion_preview.py",
        "audit_step8b23_promotion_preview.py",
        "audit_step8b24_promotion_preview.py",
        "generate_step8b24_c6c2_p0_validation_runner.py",
        "promote_step8b24_c6c2_p0.py",
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

    source_path = ROOT / "YangMills/RG/BalabanCMP99FlatFiniteGridAliasing.lean"
    audit_path = ROOT / "YangMills/RG/BalabanCMP99FlatFiniteGridAliasingAudit.lean"
    source = source_path.read_bytes()
    audit = audit_path.read_bytes()
    if b"PRE-VALIDATION" in source or b"PRE-VALIDATION" in audit:
        raise SystemExit("P0_PROMOTER_SELFTEST_STEP8B22_RAW_SCOPE_DRIFT")
    (fixture / source_path.relative_to(ROOT)).write_bytes(source)
    (fixture / audit_path.relative_to(ROOT)).write_bytes(audit)
    (fixture / "YangMillsCore.lean").write_text(
        "import YangMills.RG.BalabanCMP99FlatFiniteGridAliasingAudit\n",
        encoding="utf-8",
        newline="\n",
    )
    evidence = f"cold run {RUN}; source {SOURCE_SHA}\n"
    (fixture / "docs/HRPOLY-CMP102-CMP116-VERTICAL-SLICE.md").write_text(
        evidence, encoding="utf-8", newline="\n"
    )
    (fixture / "docs/VERIFICATION-LEDGER.md").write_text(
        evidence, encoding="utf-8", newline="\n"
    )

    for args in (
        ("git", "init", "-q"),
        ("git", "config", "user.email", "fixture@example.invalid"),
        ("git", "config", "user.name", "fixture"),
        ("git", "add", "."),
        ("git", "commit", "-qm", "fixture"),
    ):
        result = command(*args, cwd=fixture)
        if result.returncode != 0:
            raise SystemExit("P0_PROMOTER_SELFTEST_GIT_SETUP_FAILED\n" + result.stdout)
    head = command("git", "rev-parse", "HEAD", cwd=fixture).stdout.strip()
    return fixture, head


def make_green_evidence(fixture: Path) -> Path:
    audit_path = fixture / "tmp" / "audit_p0_p9_executed_notebook.py"
    spec = importlib.util.spec_from_file_location("fixture_p0_p9_audit", audit_path)
    if spec is None or spec.loader is None:
        raise RuntimeError("cannot load fixture notebook auditor")
    audit = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(audit)
    rows = [
        f"RUNNER_TRANSPORT_SHA256={audit.RUNNER_SHA256}",
        f"BASE_RUNNER_TRANSPORT_SHA256={audit.BASE_RUNNER_SHA256}",
        f"P0_P9_PATHS_TRANSPORT_SHA256={audit.PATHS_SHA256}",
        f"P0_P9_MANIFEST_TRANSPORT_SHA256={audit.MANIFEST_SHA256}",
        f"RUNNER_REV={audit.RUNNER_REV}",
        "RUNTIME=CPU RAM_GIB=50.99",
        f"HEAD is now at {audit.SOURCE_SHA[:9]}",
        "LEAN_OVERLAY_TEXT_OK files=39",
        "LEAN_IMPORT_PREFIX_OK files=39",
    ]
    for stage in sorted(audit.REQUIRED_CORE_STAGES | audit.expected_queue_stages()):
        rows.append(f"STAGE={stage} EXIT=0 SECONDS=1.000")
    rows.extend("depends on axioms: [propext, Quot.sound]" for _ in range(199))
    rows.extend(
        [
            "EVIDENCE_SHA256=" + "1" * 64,
            "EVIDENCE_ARCHIVE_SHA256=" + "2" * 64,
            "FINAL_STATUS=PASS",
            "LAUNCHER_EXIT=0",
            "LAUNCHER_RUNTIME_RELEASE_REQUESTED=1",
        ]
    )
    notebook = {
        "cells": [
            {
                "cell_type": "code",
                "execution_count": 1,
                "metadata": {},
                "outputs": [
                    {
                        "name": "stdout",
                        "output_type": "stream",
                        "text": "\n".join(rows) + "\n",
                    }
                ],
                "source": ["# immutable launcher\n"],
            }
        ],
        "metadata": {},
        "nbformat": 4,
        "nbformat_minor": 5,
    }
    target = fixture / "tmp" / "p0-p9-green.executed.ipynb"
    target.write_text(json.dumps(notebook), encoding="utf-8")
    return target


def main() -> int:
    with tempfile.TemporaryDirectory(prefix="p0-promoter-") as directory:
        fixture, head = make_fixture(Path(directory))
        dry = command(
            sys.executable,
            "tmp/promote_step8b24_c6c2_p0.py",
            "--expected-head",
            head,
            cwd=fixture,
        )
        if dry.returncode != 0 or "P0_PROMOTION_DRY_RUN_OK" not in dry.stdout:
            raise SystemExit("P0_PROMOTER_SELFTEST_DRY_RUN_FAILED\n" + dry.stdout)
        missing_evidence = command(
            sys.executable,
            "tmp/promote_step8b24_c6c2_p0.py",
            "--expected-head",
            head,
            "--write",
            cwd=fixture,
        )
        if (
            missing_evidence.returncode == 0
            or "P0_PROMOTION_EXECUTED_NOTEBOOK_REQUIRED" not in missing_evidence.stdout
        ):
            raise SystemExit(
                "P0_PROMOTER_SELFTEST_MISSING_EVIDENCE_FAILED\n"
                + missing_evidence.stdout
            )
        evidence = make_green_evidence(fixture)
        write = command(
            sys.executable,
            "tmp/promote_step8b24_c6c2_p0.py",
            "--expected-head",
            head,
            "--evidence",
            str(evidence),
            "--write",
            cwd=fixture,
        )
        if write.returncode != 0 or "P0_PROMOTION_WRITE_OK" not in write.stdout:
            raise SystemExit("P0_PROMOTER_SELFTEST_WRITE_FAILED\n" + write.stdout)
        expected = {
            "BalabanCMP99SourceCanonicalPrefixTower.lean": (
                "37BC3079D0AA92F8BE13F50E6FAE14B436ED27A7A9208B8B85FC703E01B4206F"
            ),
            "BalabanCMP99SourceCanonicalPrefixTowerAudit.lean": (
                "C667A038AB0CB336BB93FD8D38AA450DF7AE401893240F49CF763743293B3B6A"
            ),
        }
        for name, digest in expected.items():
            target = fixture / "YangMills" / "RG" / name
            if not target.is_file():
                raise SystemExit(f"P0_PROMOTER_SELFTEST_TARGET_MISSING={name}")
            data = target.read_bytes()
            if hashlib.sha256(data).hexdigest().upper() != digest:
                raise SystemExit(f"P0_PROMOTER_SELFTEST_TARGET_HASH_DRIFT={name}")
            if data.count(b"PRE-VALIDATION:") != 1:
                raise SystemExit(f"P0_PROMOTER_SELFTEST_PRE_COUNT={name}")
        if (fixture / "YangMills/RG/BalabanCMP99SourcePrefixPoincare.lean").exists():
            raise SystemExit("P0_PROMOTER_SELFTEST_SCOPE_LEAK_TO_P1")

        for args in (
            (
                "git",
                "add",
                "YangMills/RG/BalabanCMP99SourceCanonicalPrefixTower.lean",
                "YangMills/RG/BalabanCMP99SourceCanonicalPrefixTowerAudit.lean",
            ),
            ("git", "commit", "-qm", "promote P0 fixture"),
        ):
            result = command(*args, cwd=fixture)
            if result.returncode != 0:
                raise SystemExit(
                    "P0_PROMOTER_SELFTEST_SOURCE_COMMIT_FAILED\n" + result.stdout
                )
        source_sha = command("git", "rev-parse", "HEAD", cwd=fixture).stdout.strip()
        runner_path = fixture / "tmp" / "generated_p0_runner.py"
        generated = command(
            sys.executable,
            "tmp/generate_step8b24_c6c2_p0_validation_runner.py",
            "--source-sha",
            source_sha,
            "--output",
            str(runner_path),
            cwd=fixture,
        )
        if (
            generated.returncode != 0
            or "STEP8B24_C6C2_P0_RUNNER_GENERATED" not in generated.stdout
        ):
            raise SystemExit(
                "P0_PROMOTER_SELFTEST_RUNNER_GENERATION_FAILED\n" + generated.stdout
            )
        runner = runner_path.read_text(encoding="utf-8")
        if runner.count(source_sha) != 1 or runner.count("PRE-VALIDATION") != 0:
            raise SystemExit("P0_PROMOTER_SELFTEST_GENERATED_RUNNER_SCOPE_DRIFT")
        if runner.count("canonical_prefix_tower_focal") != 1:
            raise SystemExit("P0_PROMOTER_SELFTEST_GENERATED_FOCAL_SCOPE_DRIFT")
        if runner.count("canonical_prefix_tower_audit") != 1:
            raise SystemExit("P0_PROMOTER_SELFTEST_GENERATED_AUDIT_SCOPE_DRIFT")
        compile(runner, str(runner_path), "exec")

        fixture, head = make_fixture(Path(directory) / "tamper")
        sealed = fixture / "YangMills/RG/BalabanCMP99FlatFiniteGridAliasing.lean"
        sealed.write_bytes(sealed.read_bytes() + b"\n")
        for args in (
            ("git", "add", sealed.relative_to(fixture).as_posix()),
            ("git", "commit", "-qm", "tamper sealed prerequisite"),
        ):
            result = command(*args, cwd=fixture)
            if result.returncode != 0:
                raise SystemExit(
                    "P0_PROMOTER_SELFTEST_TAMPER_COMMIT_FAILED\n" + result.stdout
                )
        head = command("git", "rev-parse", "HEAD", cwd=fixture).stdout.strip()
        tamper = command(
            sys.executable,
            "tmp/promote_step8b24_c6c2_p0.py",
            "--expected-head",
            head,
            cwd=fixture,
        )
        if tamper.returncode == 0 or "STEP8B22_SEALED_BLOB_MISMATCH" not in tamper.stdout:
            raise SystemExit("P0_PROMOTER_SELFTEST_PREREQUISITE_TAMPER_FAILED\n" + tamper.stdout)

    print(
        "P0_PROMOTER_SELFTEST_OK dry_run=pass write=two_exact_files "
        "evidence_gate=fail_closed scope_leak=none runner=syntax_and_scope_pass "
        "prerequisite_tamper=fail_closed"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
