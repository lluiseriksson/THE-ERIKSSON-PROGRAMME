#!/usr/bin/env python3
"""Lightweight synthetic test for the Eq351 sign-no-go evidence packager."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tarfile
import tempfile


ROOT = Path(__file__).resolve().parents[1]
PACKAGER = ROOT / "tmp/package_cmp99_eq351_diagonal_sign_nogo_evidence.py"
SOURCE = "b36fa9758083c2f91d8beff72ec92c18a04ee052"
RUNNER_REV = "cmp99-eq351-diagonal-sign-nogo-v6"
ASSET_SHA = "bf3e0a4025e47a0bea9ed907d12dcccd3d3590b1d8ad6c55a915298b01ad9d3e"
MATHLIB_SHA = "07642720480157414db592fa85b626dafb71355b"
PATHS = (
    "YangMills/RG/BalabanCMP99Eq351DiagonalSignNoGo.lean",
    "YangMills/RG/BalabanCMP99Eq351DiagonalSignNoGoAudit.lean",
    "tmp/CMP99-EQ351-DIAGONAL-SIGN-NOGO-PREVALIDATION-PATHS.txt",
)


def main() -> int:
    with tempfile.TemporaryDirectory(prefix="eq351-sign-nogo-test-") as raw:
        temp = Path(raw)
        evidence = temp / "hrpoly-cmp99-eq351-diagonal-sign-nogo-evidence"
        evidence.mkdir()
        (evidence / "result.json").write_text(
            json.dumps(
                {
                    "runner_rev": RUNNER_REV,
                    "source_sha": SOURCE,
                    "status": "PASS",
                    "stage": "audit",
                    "seconds": 1.25,
                }
            ),
            encoding="utf-8",
        )
        hashes = {
            path: hashlib.sha256(
                subprocess.check_output(
                    ["git", "cat-file", "blob", f"{SOURCE}:{path}"], cwd=ROOT
                )
            ).hexdigest()
            for path in PATHS
        }
        (evidence / "source-hashes.json").write_text(
            json.dumps(hashes), encoding="utf-8"
        )
        (evidence / "mathlib_head.log").write_text(MATHLIB_SHA + "\n", encoding="utf-8")
        (evidence / "focal.log").write_text(
            "Build completed successfully (42 jobs).\n", encoding="utf-8"
        )
        (evidence / "audit.log").write_text(
            "'a' depends on axioms: [propext, Quot.sound]\n"
            "'b' depends on axioms: [propext, Classical.choice, Quot.sound]\n"
            "'c' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
            encoding="utf-8",
        )
        archive = temp / "evidence.tar.gz"
        with tarfile.open(archive, "w:gz") as tar:
            tar.add(evidence, arcname=evidence.name)
        archive_sha = hashlib.sha256(archive.read_bytes()).hexdigest()
        transcript = (
            f"RUNNER_REV={RUNNER_REV} SOURCE_SHA={SOURCE}\n"
            f"TOOLCHAIN_ASSET_SHA256={ASSET_SHA}\n"
            "FINAL_STATUS=PASS STAGE=audit TOTAL_SECONDS=1.25\n"
            f"EVIDENCE_SHA256={archive_sha}\n"
        )
        notebook = temp / "executed.ipynb"
        notebook.write_text(
            json.dumps(
                {
                    "cells": [
                        {
                            "cell_type": "code",
                            "outputs": [{"output_type": "stream", "name": "stdout", "text": transcript}],
                            "source": [],
                        }
                    ],
                    "metadata": {},
                    "nbformat": 4,
                    "nbformat_minor": 5,
                }
            ),
            encoding="utf-8",
        )
        destination = temp / "package"
        child = subprocess.run(
            [
                sys.executable,
                str(PACKAGER),
                "--notebook", str(notebook),
                "--archive", str(archive),
                "--destination", str(destination),
            ],
            cwd=ROOT,
            check=False,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
        )
        if child.returncode != 0:
            raise AssertionError(child.stdout)
        manifest = json.loads((destination / "manifest.json").read_text(encoding="utf-8"))
        assert manifest["status"] == "EQ351_DIAGONAL_SIGN_NOGO_EVIDENCE_PACKAGE_OK"
        assert manifest["source_sha"] == SOURCE
        assert len(manifest["axiom_blocks"]) == 3
        assert "EQ351_DIAGONAL_SIGN_NOGO_EVIDENCE_PACKAGE_OK" in child.stdout
    print("EQ351_DIAGONAL_SIGN_NOGO_PACKAGER_SELFTEST_OK")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
