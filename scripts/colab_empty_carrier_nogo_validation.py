#!/usr/bin/env python3
"""Fresh-Colab validator for the empty localized-carrier no-go checkpoint.

This file is transport/evidence infrastructure only.  It is intentionally a
child of SOURCE_SHA and always compiles that parent source checkpoint.
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


RUNNER_REV = "empty-carrier-nogo-v1"
SOURCE_SHA = "477c1f66f492d6c09b8472eeb5237d3df99e68df"
REPO = "https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME.git"
ASSET_URL = (
    "https://github.com/leanprover/lean4/releases/download/v4.29.0-rc6/"
    "lean-4.29.0-rc6-linux.tar.zst"
)
ASSET_SHA = "bf3e0a4025e47a0bea9ed907d12dcccd3d3590b1d8ad6c55a915298b01ad9d3e"
MATHLIB_SHA = "07642720480157414db592fa85b626dafb71355b"
TOOLCHAIN = "leanprover/lean4:v4.29.0-rc6"
TARGET = "YangMills.RG.BalabanCMP116Eq226CenteredConditionedPhysicalTermSource"
ROOT = Path("/content/hrpoly-empty-carrier-nogo")
EVIDENCE = Path("/content/hrpoly-empty-carrier-nogo-evidence")
TRANSCRIPT = EVIDENCE / "transcript.log"
START = time.perf_counter()


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


def archive(status: str, stage: str, code: int) -> None:
    elapsed = time.perf_counter() - START
    emit(f"FINAL_STATUS={status} STAGE={stage} TOTAL_SECONDS={elapsed:.3f}")
    (EVIDENCE / "result.json").write_text(
        json.dumps(
            {
                "runner_rev": RUNNER_REV,
                "source_sha": SOURCE_SHA,
                "status": status,
                "stage": stage,
                "seconds": elapsed,
            },
            indent=2,
        ),
        encoding="utf-8",
    )
    tar_path = Path("/content/hrpoly-empty-carrier-nogo-evidence.tar.gz")
    with tarfile.open(tar_path, "w:gz") as tar:
        tar.add(EVIDENCE, arcname=EVIDENCE.name)
    emit(f"EVIDENCE_SHA256={sha256(tar_path)}")
    emit(f"EVIDENCE_PATH={tar_path}")
    raise SystemExit(code)


def run(name: str, command: list[str], *, cwd: Path | None = None,
        env: dict[str, str] | None = None) -> str:
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
    emit(f"=== {name} EXIT={child.returncode} SECONDS={time.perf_counter() - started:.3f} ===")
    if child.returncode != 0:
        archive("FAIL", name, child.returncode)
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
    emit(f"PREFLIGHT_EXIT_ZERO={preflight_zero} PREFLIGHT_EXIT_NONZERO={preflight_nonzero}")
    if preflight_zero != 0 or preflight_nonzero != 7:
        archive("FAIL", "preflight", 98)

    if shutil.which("zstd") is None:
        run("install_zstd", ["bash", "-lc", "apt-get update -qq && apt-get install -y -qq zstd"])
    asset = Path("/content/lean-4.29.0-rc6-linux.tar.zst")
    if not asset.exists():
        run(
            "download_toolchain",
            ["curl", "--fail", "--location", "--retry", "5", "--retry-delay", "2",
             "-o", str(asset), ASSET_URL],
        )
    actual_asset_sha = sha256(asset)
    emit("TOOLCHAIN_ASSET_SHA256=" + actual_asset_sha)
    if actual_asset_sha != ASSET_SHA:
        archive("FAIL", "toolchain_hash", 97)
    toolroot = Path("/content/lean-4.29.0-rc6-linux")
    if not toolroot.exists():
        run(
            "extract_toolchain",
            ["tar", "--use-compress-program=unzstd", "-xf", str(asset), "-C", "/content"],
        )
    bindir = toolroot / "bin"
    if not (bindir / "lake").exists():
        archive("FAIL", "toolchain_layout", 96)
    env = os.environ.copy()
    env["PATH"] = str(bindir) + os.pathsep + env.get("PATH", "")
    emit("LEAN_EXE_SHA256=" + sha256(bindir / "lean"))
    emit("LAKE_EXE_SHA256=" + sha256(bindir / "lake"))
    run("lean_version", [str(bindir / "lean"), "--version"], env=env)
    run("lake_version", [str(bindir / "lake"), "--version"], env=env)

    ROOT.mkdir()
    run("git_init", ["git", "init", "-q"], cwd=ROOT, env=env)
    run("git_remote", ["git", "remote", "add", "origin", REPO], cwd=ROOT, env=env)
    run(
        "git_fetch",
        ["git", "-c", "http.version=HTTP/1.1", "fetch", "--depth", "1", "origin", SOURCE_SHA],
        cwd=ROOT,
        env=env,
    )
    run("git_checkout", ["git", "checkout", "-q", "--detach", "FETCH_HEAD"], cwd=ROOT, env=env)
    head = run("git_head", ["git", "rev-parse", "HEAD"], cwd=ROOT, env=env).strip()
    if head != SOURCE_SHA:
        archive("FAIL", "source_head", 95)
    if (ROOT / "lean-toolchain").read_text().strip() != TOOLCHAIN:
        archive("FAIL", "lean_toolchain_pin", 94)
    manifest_before = sha256(ROOT / "lake-manifest.json")
    emit("MANIFEST_SHA256_BEFORE=" + manifest_before)
    run("cache_get", [str(bindir / "lake"), "exe", "cache", "get"], cwd=ROOT, env=env)
    manifest_after = sha256(ROOT / "lake-manifest.json")
    emit("MANIFEST_SHA256_AFTER=" + manifest_after)
    if manifest_after != manifest_before:
        archive("FAIL", "manifest_drift", 93)
    mathlib = run(
        "mathlib_head",
        ["git", "-C", str(ROOT / ".lake/packages/mathlib"), "rev-parse", "HEAD"],
        env=env,
    ).strip()
    if mathlib != MATHLIB_SHA:
        archive("FAIL", "mathlib_pin", 92)
    run("core_import_guard", ["python3", "scripts/check_core_imports_tracked.py"], cwd=ROOT, env=env)

    run("focal", [str(bindir / "lake"), "build", TARGET], cwd=ROOT, env=env)
    audit = ROOT / "EmptyCarrierNoGoAudit.lean"
    audit.write_text(
        "import YangMills.RG.BalabanCMP116Eq226CenteredConditionedPhysicalTermSource\n"
        "#print axioms YangMills.RG.cmp116SourcePhysicalLocalizedCoordinates_empty\n"
        "#print axioms YangMills.RG.not_nonempty_cmp116Eq226CenteredConditionedPhysicalTermSource_empty_Z0\n",
        encoding="utf-8",
    )
    audit_output = run("audit", [str(bindir / "lake"), "env", "lean", audit.name], cwd=ROOT, env=env)
    clean = re.sub(r"\x1b\[[0-9;]*m", "", audit_output).replace("\r", "")
    compact = "".join(clean.split())
    axiom_headers = compact.count("dependsonaxioms:")
    axiom_blocks = re.findall(r"dependsonaxioms:(\[[^\]]*\])", compact)
    emit("AUDIT_AXIOM_HEADERS=" + str(axiom_headers))
    emit("AUDIT_AXIOM_BLOCKS=" + str(len(axiom_blocks)))
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    forbidden = {"sorryAx", "Lean.ofReduceBool", "ofReduceBool"}
    if axiom_headers != 2 or len(axiom_blocks) != 2:
        archive("FAIL", "audit_count", 90)
    if any(name in compact for name in forbidden):
        archive("FAIL", "audit_forbidden", 91)
    for block in axiom_blocks:
        axioms = {
            name.strip()
            for name in block.removeprefix("[").removesuffix("]").split(",")
            if name.strip()
        }
        emit("AUDIT_AXIOMS=" + ",".join(sorted(axioms)))
        if not axioms.issubset(allowed):
            archive("FAIL", "audit_axioms", 91)
    status = run("git_status", ["git", "status", "--porcelain"], cwd=ROOT, env=env)
    if status.strip() != "?? EmptyCarrierNoGoAudit.lean":
        archive("FAIL", "unexpected_checkout_state", 89)
    archive("PASS", "audit", 0)


if __name__ == "__main__":
    main()
