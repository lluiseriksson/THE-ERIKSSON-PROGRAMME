#!/usr/bin/env python3
"""Fresh-Colab validator for the CMP99 (3.51) diagonal-sign no-go.

Transport/evidence infrastructure only.  This runner is a child of
``SOURCE_SHA`` and always compiles that exact PRE-VALIDATION checkpoint.
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


RUNNER_REV = "cmp99-eq351-diagonal-sign-nogo-v2"
SOURCE_SHA = "176c0d46ea91ae2325d2cf26a526d76198ed0fa8"
REPO = "https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME.git"
ASSET_URL = (
    "https://github.com/leanprover/lean4/releases/download/v4.29.0-rc6/"
    "lean-4.29.0-rc6-linux.tar.zst"
)
ASSET_SHA = "bf3e0a4025e47a0bea9ed907d12dcccd3d3590b1d8ad6c55a915298b01ad9d3e"
MATHLIB_SHA = "07642720480157414db592fa85b626dafb71355b"
TOOLCHAIN = "leanprover/lean4:v4.29.0-rc6"
TARGET = "YangMills.RG.BalabanCMP99Eq351DiagonalSignNoGo"
AUDIT = "YangMills/RG/BalabanCMP99Eq351DiagonalSignNoGoAudit.lean"
PATHS = "tmp/CMP99-EQ351-DIAGONAL-SIGN-NOGO-PREVALIDATION-PATHS.txt"
ROOT = Path("/content/hrpoly-cmp99-eq351-diagonal-sign-nogo")
EVIDENCE = Path("/content/hrpoly-cmp99-eq351-diagonal-sign-nogo-evidence")
TRANSCRIPT = EVIDENCE / "transcript.log"
ARCHIVE = Path("/content/hrpoly-cmp99-eq351-diagonal-sign-nogo-evidence.tar.gz")
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
    with tarfile.open(ARCHIVE, "w:gz") as tar:
        tar.add(EVIDENCE, arcname=EVIDENCE.name)
    emit(f"EVIDENCE_SHA256={sha256(ARCHIVE)}")
    emit(f"EVIDENCE_PATH={ARCHIVE}")
    raise SystemExit(code)


def run(
    name: str,
    command: list[str],
    *,
    cwd: Path | None = None,
    env: dict[str, str] | None = None,
) -> str:
    emit(f"STAGE={name} CMD={json.dumps(command)}")
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
    emit(f"STAGE={name} EXIT={child.returncode} SECONDS={time.perf_counter() - started:.3f}")
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
    zero = subprocess.run(["bash", "-lc", "exit 0"]).returncode
    nonzero = subprocess.run(["bash", "-lc", "exit 7"]).returncode
    emit(f"PREFLIGHT_EXIT_ZERO={zero} PREFLIGHT_EXIT_NONZERO={nonzero}")
    if zero != 0 or nonzero != 7:
        archive("FAIL", "preflight", 98)

    if shutil.which("zstd") is None:
        run("install_zstd", ["bash", "-lc", "apt-get update -qq && apt-get install -y -qq zstd"])
    asset = Path("/content/lean-4.29.0-rc6-linux.tar.zst")
    if not asset.exists():
        run(
            "download_toolchain",
            [
                "curl", "--fail", "--location", "--retry", "5",
                "--retry-delay", "2", "-o", str(asset), ASSET_URL,
            ],
        )
    if sha256(asset) != ASSET_SHA:
        archive("FAIL", "toolchain_hash", 97)
    emit("TOOLCHAIN_ASSET_SHA256=" + sha256(asset))
    toolroot = Path("/content/lean-4.29.0-rc6-linux")
    if not toolroot.exists():
        run("extract_toolchain", ["tar", "--use-compress-program=unzstd", "-xf", str(asset), "-C", "/content"])
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
    source_hashes = {
        str(path.relative_to(ROOT)): sha256(path)
        for path in [
            ROOT / "YangMills/RG/BalabanCMP99Eq351DiagonalSignNoGo.lean",
            ROOT / "YangMills/RG/BalabanCMP99Eq351DiagonalSignNoGoAudit.lean",
            ROOT / PATHS,
        ]
    }
    (EVIDENCE / "source-hashes.json").write_text(
        json.dumps(source_hashes, indent=2, sort_keys=True), encoding="utf-8"
    )
    manifest_before = sha256(ROOT / "lake-manifest.json")
    emit("MANIFEST_SHA256_BEFORE=" + manifest_before)
    run("text_guard", ["python3", "scripts/check_lean_overlay_text.py", "--paths-from", PATHS, "--require-prevalidation"], cwd=ROOT, env=env)
    lean_paths = (ROOT / PATHS).read_text(encoding="utf-8").splitlines()
    run("import_prefix_guard", ["python3", "scripts/check_lean_import_prefix.py", *lean_paths], cwd=ROOT, env=env)
    run("cache_get", [str(bindir / "lake"), "exe", "cache", "get"], cwd=ROOT, env=env)
    manifest_after = sha256(ROOT / "lake-manifest.json")
    emit("MANIFEST_SHA256_AFTER=" + manifest_after)
    if manifest_after != manifest_before:
        archive("FAIL", "manifest_drift", 93)
    mathlib = run("mathlib_head", ["git", "-C", str(ROOT / ".lake/packages/mathlib"), "rev-parse", "HEAD"], env=env).strip()
    if mathlib != MATHLIB_SHA:
        archive("FAIL", "mathlib_pin", 92)
    run("core_import_guard", ["python3", "scripts/check_core_imports_tracked.py"], cwd=ROOT, env=env)

    run("focal", [str(bindir / "lake"), "build", TARGET], cwd=ROOT, env=env)
    audit_output = run("audit", [str(bindir / "lake"), "env", "lean", AUDIT], cwd=ROOT, env=env)
    clean = re.sub(r"\x1b\[[0-9;]*m", "", audit_output).replace("\r", "")
    compact = "".join(clean.split())
    blocks = re.findall(r"dependsonaxioms:(\[[^\]]*\])", compact)
    headers = compact.count("dependsonaxioms:")
    emit("AUDIT_AXIOM_HEADERS=" + str(headers))
    emit("AUDIT_AXIOM_BLOCKS=" + str(len(blocks)))
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    forbidden = {"sorryAx", "Lean.ofReduceBool", "ofReduceBool"}
    if headers != 3 or len(blocks) != 3:
        archive("FAIL", "audit_count", 90)
    if any(name in compact for name in forbidden):
        archive("FAIL", "audit_forbidden", 91)
    for block in blocks:
        axioms = {
            name.strip()
            for name in block.removeprefix("[").removesuffix("]").split(",")
            if name.strip()
        }
        emit("AUDIT_AXIOMS=" + ",".join(sorted(axioms)))
        if not axioms.issubset(allowed):
            archive("FAIL", "audit_axioms", 91)
    status = run("git_status", ["git", "status", "--porcelain"], cwd=ROOT, env=env)
    if status.strip():
        archive("FAIL", "unexpected_checkout_state", 89)
    archive("PASS", "audit", 0)


if __name__ == "__main__":
    main()
