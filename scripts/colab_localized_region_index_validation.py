#!/usr/bin/env python3
"""Fresh-Colab validator for the proof-carrying localized-region index.

This is evidence infrastructure only.  ``FINAL_STATUS`` is derived from the
recorded child exit codes and the axiom-line count; it is never reconstructed
by reparsing the visible tail of the transcript.
"""

from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tarfile
import time


RUNNER_REV = "localized-region-index-v2"
SOURCE_SHA = "a0bb88dd48c80b72d8e0b60a5715eed9221fef75"
REPO = "https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME.git"
ASSET_URL = (
    "https://github.com/leanprover/lean4/releases/download/v4.29.0-rc6/"
    "lean-4.29.0-rc6-linux.tar.zst"
)
ASSET_SHA = "bf3e0a4025e47a0bea9ed907d12dcccd3d3590b1d8ad6c55a915298b01ad9d3e"
MATHLIB_SHA = "07642720480157414db592fa85b626dafb71355b"
TOOLCHAIN = "leanprover/lean4:v4.29.0-rc6"
TARGET = "YangMills.RG.BalabanCMP116Eq226CenteredConditionedPhysicalContourToUV"
AUDIT_FILE = "LocalizedRegionIndexAudit.lean"
AXIOM_DECLARATIONS = [
    "YangMills.RG.cmp116Eq226CenteredConditionedPhysicalContour_lemma3ActivityEstimate_of_boundaries",
    "YangMills.RG.cmp116Eq226CenteredConditionedPhysicalContour_rawMetricDecay_of_boundaries",
    "YangMills.RG.cmp116Eq226CenteredConditionedPhysicalContour_KPCriterion_of_boundaries",
    "YangMills.RG.cmp116Eq226CenteredConditionedPhysicalContour_singleScaleUVDecay_boundedHoles_of_boundaries",
]
EXPECTED_AXIOM_LINES = len(AXIOM_DECLARATIONS)
ROOT = Path("/content/hrpoly-localized-region-index")
EVIDENCE = Path("/content/hrpoly-localized-region-index-evidence")
TRANSCRIPT = EVIDENCE / "transcript.log"
START = time.perf_counter()
RESULT = {
    "focal_exit": None,
    "audit_exit": None,
    "axiom_lines_seen": 0,
    "axiom_lines_expected": EXPECTED_AXIOM_LINES,
    "axiom_content_ok": None,
}


def emit(value: object) -> None:
    text = str(value)
    print(text, flush=True)
    with TRANSCRIPT.open("a", encoding="utf-8") as out:
        out.write(text + "\n")


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def write_result(status: str, stage: str, seconds: float) -> None:
    payload = {
        "runner_rev": RUNNER_REV,
        "source_sha": SOURCE_SHA,
        "status": status,
        "stage": stage,
        "seconds": seconds,
        **RESULT,
    }
    temporary = EVIDENCE / "result.json.tmp"
    temporary.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    temporary.replace(EVIDENCE / "result.json")


def derived_status() -> str:
    focal = RESULT["focal_exit"]
    audit = RESULT["audit_exit"]
    if (focal is not None and focal != 0) or (audit is not None and audit != 0):
        return "FAIL"
    if RESULT["axiom_content_ok"] is False:
        return "FAIL"
    if focal is None or audit is None:
        return "INCOMPLETE"
    if RESULT["axiom_lines_seen"] != RESULT["axiom_lines_expected"]:
        return "INCOMPLETE"
    if RESULT["axiom_content_ok"] is not True:
        return "INCOMPLETE"
    return "PASS"


def archive(stage: str, code: int) -> None:
    elapsed = time.perf_counter() - START
    status = derived_status()
    write_result(status, stage, elapsed)
    emit(
        "PRIMARY_RESULTS "
        f"focal_exit={RESULT['focal_exit']} "
        f"audit_exit={RESULT['audit_exit']} "
        f"axiom_lines_seen={RESULT['axiom_lines_seen']} "
        f"axiom_lines_expected={RESULT['axiom_lines_expected']} "
        f"axiom_content_ok={RESULT['axiom_content_ok']}"
    )
    emit(f"FINAL_STATUS={status} STAGE={stage} TOTAL_SECONDS={elapsed:.3f}")
    tar_path = Path("/content/hrpoly-localized-region-index-evidence.tar.gz")
    with tarfile.open(tar_path, "w:gz") as tar:
        tar.add(EVIDENCE, arcname=EVIDENCE.name)
    emit(f"EVIDENCE_SHA256={sha256(tar_path)}")
    emit(f"EVIDENCE_PATH={tar_path}")
    raise SystemExit(code)


def run(name: str, command: list[str], *, cwd: Path | None = None,
        env: dict[str, str] | None = None) -> tuple[int, str]:
    emit(f"=== {name} START ===")
    started = time.perf_counter()
    child = subprocess.run(
        command,
        cwd=cwd,
        env=env,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
    )
    output = child.stdout or ""
    (EVIDENCE / f"{name}.log").write_text(output, encoding="utf-8")
    emit(output.rstrip())
    emit(
        f"=== {name} EXIT={child.returncode} "
        f"SECONDS={time.perf_counter() - started:.3f} ==="
    )
    return child.returncode, output


def require_zero(name: str, command: list[str], *, cwd: Path | None = None,
                 env: dict[str, str] | None = None) -> str:
    code, output = run(name, command, cwd=cwd, env=env)
    if code != 0:
        archive(name, code)
    return output


def main() -> None:
    if ROOT.exists():
        shutil.rmtree(ROOT)
    if EVIDENCE.exists():
        shutil.rmtree(EVIDENCE)
    EVIDENCE.mkdir()
    emit(f"RUNNER_REV={RUNNER_REV} SOURCE_SHA={SOURCE_SHA}")
    emit("RUNTIME=COLAB_CPU_HIGH_RAM_NO_GPU")
    emit("OPENED_UTC=" + time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()))
    emit("MEMTOTAL=" + Path("/proc/meminfo").read_text().splitlines()[0])

    preflight_zero = subprocess.run(["bash", "-lc", "exit 0"]).returncode
    preflight_nonzero = subprocess.run(["bash", "-lc", "exit 7"]).returncode
    sentinel_cases = [
        (0, 0, EXPECTED_AXIOM_LINES, True, "PASS"),
        (1, 0, EXPECTED_AXIOM_LINES, True, "FAIL"),
        (0, 1, EXPECTED_AXIOM_LINES, True, "FAIL"),
        (0, 0, EXPECTED_AXIOM_LINES - 1, True, "INCOMPLETE"),
    ]
    sentinel_ok = True
    for focal, audit, count, content, expected in sentinel_cases:
        saved = RESULT.copy()
        RESULT.update(
            focal_exit=focal,
            audit_exit=audit,
            axiom_lines_seen=count,
            axiom_content_ok=content,
        )
        sentinel_ok = sentinel_ok and derived_status() == expected
        RESULT.clear()
        RESULT.update(saved)
    emit(
        f"PREFLIGHT_EXIT_ZERO={preflight_zero} "
        f"PREFLIGHT_EXIT_NONZERO={preflight_nonzero} "
        f"SENTINEL_CASES_OK={sentinel_ok}"
    )
    if preflight_zero != 0 or preflight_nonzero != 7 or not sentinel_ok:
        archive("preflight", 98)

    if shutil.which("zstd") is None:
        require_zero(
            "install_zstd",
            ["bash", "-lc", "apt-get update -qq && apt-get install -y -qq zstd"],
        )
    asset = Path("/content/lean-4.29.0-rc6-linux.tar.zst")
    if not asset.exists():
        require_zero(
            "download_toolchain",
            [
                "curl", "--fail", "--location", "--retry", "5",
                "--retry-delay", "2", "-o", str(asset), ASSET_URL,
            ],
        )
    actual_asset_sha = sha256(asset)
    emit("TOOLCHAIN_ASSET_SHA256=" + actual_asset_sha)
    if actual_asset_sha != ASSET_SHA:
        archive("toolchain_hash", 97)
    toolroot = Path("/content/lean-4.29.0-rc6-linux")
    if not toolroot.exists():
        require_zero(
            "extract_toolchain",
            ["tar", "--use-compress-program=unzstd", "-xf", str(asset), "-C", "/content"],
        )
    bindir = toolroot / "bin"
    if not (bindir / "lake").exists():
        archive("toolchain_layout", 96)
    env = os.environ.copy()
    env["PATH"] = str(bindir) + os.pathsep + env.get("PATH", "")
    emit("LEAN_EXE_SHA256=" + sha256(bindir / "lean"))
    emit("LAKE_EXE_SHA256=" + sha256(bindir / "lake"))
    require_zero("lean_version", [str(bindir / "lean"), "--version"], env=env)
    require_zero("lake_version", [str(bindir / "lake"), "--version"], env=env)

    ROOT.mkdir()
    require_zero("git_init", ["git", "init", "-q"], cwd=ROOT, env=env)
    require_zero("git_remote", ["git", "remote", "add", "origin", REPO], cwd=ROOT, env=env)
    require_zero(
        "git_fetch",
        ["git", "-c", "http.version=HTTP/1.1", "fetch", "--depth", "1", "origin", SOURCE_SHA],
        cwd=ROOT,
        env=env,
    )
    require_zero("git_checkout", ["git", "checkout", "-q", "--detach", "FETCH_HEAD"], cwd=ROOT, env=env)
    head = require_zero("git_head", ["git", "rev-parse", "HEAD"], cwd=ROOT, env=env).strip()
    if head != SOURCE_SHA:
        archive("source_head", 95)
    if (ROOT / "lean-toolchain").read_text().strip() != TOOLCHAIN:
        archive("lean_toolchain_pin", 94)
    manifest_before = sha256(ROOT / "lake-manifest.json")
    emit("MANIFEST_SHA256_BEFORE=" + manifest_before)
    require_zero("cache_get", [str(bindir / "lake"), "exe", "cache", "get"], cwd=ROOT, env=env)
    manifest_after = sha256(ROOT / "lake-manifest.json")
    emit("MANIFEST_SHA256_AFTER=" + manifest_after)
    if manifest_after != manifest_before:
        archive("manifest_drift", 93)
    mathlib = require_zero(
        "mathlib_head",
        ["git", "-C", str(ROOT / ".lake/packages/mathlib"), "rev-parse", "HEAD"],
        env=env,
    ).strip()
    if mathlib != MATHLIB_SHA:
        archive("mathlib_pin", 92)
    require_zero(
        "core_import_guard",
        ["python3", "scripts/check_core_imports_tracked.py"],
        cwd=ROOT,
        env=env,
    )

    focal_exit, _ = run("focal", [str(bindir / "lake"), "build", TARGET], cwd=ROOT, env=env)
    RESULT["focal_exit"] = focal_exit
    write_result(derived_status(), "focal_recorded", time.perf_counter() - START)
    if focal_exit != 0:
        archive("focal", focal_exit)

    audit = ROOT / AUDIT_FILE
    audit.write_text(
        f"import {TARGET}\n" +
        "".join(f"#print axioms {declaration}\n" for declaration in AXIOM_DECLARATIONS),
        encoding="utf-8",
    )
    audit_exit, audit_output = run(
        "audit", [str(bindir / "lake"), "env", "lean", audit.name], cwd=ROOT, env=env
    )
    RESULT["audit_exit"] = audit_exit
    ansi_escape = re.compile(r"\x1b(?:[@-Z\\-_]|\[[0-?]*[ -/]*[@-~])")
    clean_audit = ansi_escape.sub("", audit_output).replace("\r", "")
    axiom_headers_seen = clean_audit.count("depends on axioms:")
    axiom_blocks = list(
        re.finditer(r"depends on axioms:\s*(\[[^\]]*\])", clean_audit, flags=re.MULTILINE)
    )
    RESULT["axiom_lines_seen"] = len(axiom_blocks)
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    content_ok = axiom_headers_seen == len(axiom_blocks)
    for match in axiom_blocks:
        emit(re.sub(r"\s+", " ", match.group(0)))
        axioms = {
            name.strip()
            for name in match.group(1).removeprefix("[").removesuffix("]").split(",")
            if name.strip()
        }
        content_ok = content_ok and bool(axioms) and axioms.issubset(allowed)
    RESULT["axiom_content_ok"] = content_ok
    write_result(derived_status(), "audit_recorded", time.perf_counter() - START)
    if audit_exit != 0:
        archive("audit", audit_exit)
    if not content_ok:
        archive("audit_axioms", 91)
    if len(axiom_blocks) != EXPECTED_AXIOM_LINES:
        archive("audit_evidence_incomplete", 90)

    status_output = require_zero("git_status", ["git", "status", "--porcelain"], cwd=ROOT, env=env)
    if status_output.strip() != f"?? {AUDIT_FILE}":
        archive("unexpected_checkout_state", 89)
    archive("complete", 0)


if __name__ == "__main__":
    main()
