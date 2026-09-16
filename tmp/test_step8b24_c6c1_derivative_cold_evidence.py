#!/usr/bin/env python3
"""Synthetic positive/tamper test for the D1--D4d evidence validator."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
import runpy
import tarfile
import tempfile
import zipfile


ROOT = Path(__file__).resolve().parents[1]
AUDIT = runpy.run_path(
    str(ROOT / "tmp" / "audit_step8b24_c6c1_derivative_cold_evidence.py")
)
GENERATOR = runpy.run_path(
    str(ROOT / "tmp" / "generate_step8b24_c6c1_derivative_validation_runner.py")
)
SOURCE = "a" * 40
WORKFLOW = "b" * 40


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write(path: Path, text: str) -> None:
    path.write_text(text, encoding="utf-8", newline="\n")


def synthetic_manifest() -> list[tuple[str, str]]:
    return [
        (hashlib.sha256(("synthetic:" + path).encode()).hexdigest(), path)
        for path in GENERATOR["source_paths"]()
    ]


def make_fixture(base: Path, manifest: list[tuple[str, str]]) -> tuple[Path, Path]:
    root = base / "extracted"
    evidence = root / "evidence"
    evidence.mkdir(parents=True)
    write(
        evidence / "checkpoint.txt",
        f"SOURCE_SHA={SOURCE}\nACTUAL_HEAD={SOURCE}\n"
        f"WORKFLOW_SHA={WORKFLOW}\nCOLD_MODE=true\n",
    )
    write(
        evidence / "source-blobs.sha256",
        "".join(f"{digest}  {path}\n" for digest, path in manifest),
    )
    write(evidence / "overlay-paths.txt", "".join(path + "\n" for _, path in manifest))
    write(
        evidence / "toolchain.txt",
        f"TOOLCHAIN_URL={AUDIT['TOOLCHAIN_URL']}\n"
        f"TOOLCHAIN_ASSET_SHA256={AUDIT['TOOLCHAIN_ASSET_SHA256']}\n"
        f"{'c' * 64}  /tmp/toolchain/bin/lean\n"
        f"{'d' * 64}  /tmp/toolchain/bin/lake\n"
        "Lean (version 4.29.0-rc6, synthetic)\nLake version synthetic\n",
    )
    write(evidence / "mathlib.txt", f"MATHLIB_SHA={AUDIT['MATHLIB_SHA']}\n")
    write(evidence / "text-guard.log", "LEAN_OVERLAY_TEXT_OK files=14\n")
    write(evidence / "import-prefix-guard.log", "LEAN_IMPORT_PREFIX_OK files=14\n")
    write(evidence / "lake-update.log", "synthetic\n")
    write(evidence / "cache-get.log", "synthetic\n")

    stage_lines: list[str] = []
    axioms: dict[str, list[list[str]]] = {}
    stamp = 0
    for focal, audit, _module_path, count in AUDIT["stage_rows"]():
        for stage, command in ((focal, "lake build x"), (audit, "lake env lean y")):
            stage_lines.append(
                f"STAGE={stage} STARTED=2026-08-17T00:{stamp // 60:02d}:{stamp % 60:02d}Z "
                f"CMD={command}\n"
            )
            stamp += 1
            stage_lines.append(
                f"STAGE={stage} EXIT=0 ENDED=2026-08-17T00:{stamp // 60:02d}:{stamp % 60:02d}Z\n"
            )
        write(evidence / f"{focal}.log", "Build completed successfully (321 jobs).\n")
        block = ["Classical.choice", "Quot.sound", "propext"]
        write(
            evidence / f"{audit}.log",
            "".join(
                f"'synthetic{i}' depends on axioms: [propext, Classical.choice, Quot.sound]\n"
                for i in range(count)
            ),
        )
        axioms[audit] = [block] * count
    write(evidence / "stages.txt", "".join(stage_lines))
    write(evidence / "axioms.json", json.dumps(axioms, sort_keys=True, indent=2) + "\n")
    write(evidence / "FINAL_STATUS", "FINAL_STATUS=PASS\n")

    targets = sorted(path for path in evidence.iterdir() if path.is_file())
    write(
        evidence / "SHA256SUMS",
        "".join(f"{sha(path)}  evidence/{path.name}\n" for path in targets),
    )
    inner_name = AUDIT["INNER_ARCHIVE"]
    inner = root / inner_name
    with tarfile.open(inner, "w:gz") as packed:
        for path in sorted(evidence.iterdir()):
            packed.add(path, arcname=f"evidence/{path.name}")
    write(evidence / "ARCHIVE_SHA256", f"{sha(inner)}  {inner_name}\n")

    outer = base / "artifact.zip"
    with zipfile.ZipFile(outer, "w", compression=zipfile.ZIP_DEFLATED) as packed:
        for path in sorted(root.rglob("*")):
            if path.is_file():
                packed.write(path, path.relative_to(root).as_posix())
    return root, outer


def main() -> int:
    manifest = synthetic_manifest()
    assert len(manifest) == 14
    with tempfile.TemporaryDirectory(prefix="step8b24-derivative-evidence-test-") as raw:
        root, outer = make_fixture(Path(raw), manifest)
        result = AUDIT["validate"](root, outer, SOURCE, WORKFLOW, manifest)
        assert len(result["stages"]) == 14
        assert len(result["jobs"]) == 7

        write(root / "evidence" / "FINAL_STATUS", "FINAL_STATUS=FAIL\n")
        try:
            AUDIT["validate"](root, outer, SOURCE, WORKFLOW, manifest)
        except ValueError as error:
            assert "FINAL_STATUS" in str(error)
        else:
            raise AssertionError("tampered FINAL_STATUS did not fail closed")

    print(
        "STEP8B24_C6C1_DERIVATIVE_COLD_EVIDENCE_SELFTEST_OK positive=pass "
        "tamper=fail_closed files=14 stages=14 axiom_blocks=33"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
