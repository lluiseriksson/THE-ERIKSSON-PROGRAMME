#!/usr/bin/env python3
"""Fresh Colab gate for the CMP89 physical uniform-owner endpoint."""

from __future__ import annotations

import datetime as dt
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tarfile
import time
import traceback


RUNNER_REV = "cmp89-neumann-physical-uniform-owner-v1"
SOURCE_SHA = "389d2626250f4b729253e74e6bc885166cb795fc"
REPO_URL = "https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME.git"
EXPECTED_TOOLCHAIN = "leanprover/lean4:v4.29.0-rc6"
EXPECTED_MATHLIB = "07642720480157414db592fa85b626dafb71355b"
TOOLCHAIN_URL = (
    "https://github.com/leanprover/lean4/releases/download/v4.29.0-rc6/"
    "lean-4.29.0-rc6-linux.tar.zst"
)
TOOLCHAIN_SHA256 = (
    "bf3e0a4025e47a0bea9ed907d12dcccd3d3590b1d8ad6c55a915298b01ad9d3e"
)
CONTENT = Path("/content")
ROOT = CONTENT / "hrpoly-cmp89-physical-uniform-owner-cold-389d2626"
EVIDENCE = CONTENT / "hrpoly-cmp89-physical-uniform-owner-cold-389d2626-evidence"
ARCHIVE = CONTENT / "hrpoly-cmp89-physical-uniform-owner-cold-389d2626-evidence.tar.gz"
ASSET = CONTENT / "lean-4.29.0-rc6-linux.tar.zst"
TOOLROOT = CONTENT / "lean-4.29.0-rc6-linux"
BINDIR = TOOLROOT / "lean-4.29.0-rc6-linux" / "bin"
PATH_MANIFEST = CONTENT / "hrpoly-cmp89-physical-uniform-owner-paths.txt"

SOURCE_BLOBS = {
    "YangMills/RG/BalabanCMP89NeumannRectangularPhysicalUniformOwnerBound.lean":
        "87c5d81251d3f39ee5a7c98752fe29082c6f87d75706890d5a928601b8587677",
    "YangMills/RG/BalabanCMP89NeumannRectangularPhysicalUniformOwnerBoundAudit.lean":
        "b3902220518ac6b4ec55fc4c2b31f0f0461ed04848244e8678dce16531f51f37",
    "YangMillsCore.lean":
        "2708fd98c7d782a317238dfe09fb4e81d9ea8344a04136c374f986e2bf15e4ef",
}
EXPECTED_DECLARATIONS = [
    "YangMills.RG."
    "norm_cmp89Eq248PhysicalRegionalGreen_le_physicalOwner_uniform_draft",
]
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
RECORDS: list[dict[str, object]] = []


def utc_now() -> str:
    return dt.datetime.now(dt.timezone.utc).isoformat()


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def tail(text: str, lines: int = 100) -> str:
    return "\n".join(text.splitlines()[-lines:])


def run(stage: str, command: list[str], *, cwd: Path | None = None) -> str:
    print("STAGE=" + stage + " CMD=" + json.dumps(command), flush=True)
    started = time.perf_counter()
    EVIDENCE.mkdir(parents=True, exist_ok=True)
    stdout_path = EVIDENCE / f"{len(RECORDS):03d}-{stage}.stdout"
    with stdout_path.open("w", encoding="utf-8", newline="\n") as stream:
        child = subprocess.Popen(
            command,
            cwd=cwd,
            env=os.environ.copy(),
            text=True,
            stdout=stream,
            stderr=subprocess.STDOUT,
        )
        next_heartbeat = started + 60
        while True:
            try:
                exit_code = child.wait(timeout=1)
                break
            except subprocess.TimeoutExpired:
                now = time.perf_counter()
                if now >= next_heartbeat:
                    stream.flush()
                    print(
                        f"STAGE={stage} HEARTBEAT_SECONDS={now - started:.3f}",
                        flush=True,
                    )
                    next_heartbeat = now + 60
    elapsed = time.perf_counter() - started
    output = stdout_path.read_text(encoding="utf-8")
    jobs = None
    matches = re.findall(r"Build completed successfully \((\d+) jobs\)", output)
    if matches:
        jobs = int(matches[-1])
    RECORDS.append({
        "stage": stage,
        "exit": exit_code,
        "seconds": elapsed,
        "jobs": jobs,
        "output_sha256": sha256(stdout_path),
    })
    print(tail(output, 120 if exit_code else 40), flush=True)
    print(
        f"STAGE={stage} EXIT={exit_code} SECONDS={elapsed:.3f} JOBS={jobs}",
        flush=True,
    )
    if exit_code != 0:
        raise RuntimeError("FIRST_ERROR=" + stage)
    return output


def parse_axioms_exact(output: str) -> None:
    compact = re.sub(r"\s+", "", output)
    for forbidden in ("sorryAx", "ofReduceBool"):
        if forbidden in compact:
            raise RuntimeError("FORBIDDEN_AXIOM=" + forbidden)
    blocks = re.findall(r"'([^']+)'dependsonaxioms:\[([^\]]*)\]", compact)
    found = {name: body for name, body in blocks}
    if set(found) != set(EXPECTED_DECLARATIONS):
        raise RuntimeError(
            "AXIOM_DECLARATIONS_MISMATCH="
            + json.dumps({
                "found": sorted(found),
                "expected": EXPECTED_DECLARATIONS,
            })
        )
    for name in EXPECTED_DECLARATIONS:
        axioms = {item for item in found[name].split(",") if item}
        if not axioms.issubset(ALLOWED_AXIOMS):
            raise RuntimeError("AXIOM_SET=" + name + ":" + json.dumps(sorted(axioms)))
        print("AXIOM_GATE=" + name + " AXIOMS=" + ",".join(sorted(axioms)), flush=True)


def ensure_toolchain() -> None:
    if not (BINDIR / "lake").is_file():
        if not ASSET.is_file():
            run(
                "download_toolchain",
                [
                    "curl", "--fail", "--location", "--retry", "5",
                    "--retry-all-errors", "--retry-delay", "2",
                    "-o", str(ASSET), TOOLCHAIN_URL,
                ],
            )
        if sha256(ASSET) != TOOLCHAIN_SHA256:
            raise RuntimeError("TOOLCHAIN_ASSET_HASH_MISMATCH")
        if shutil.which("unzstd") is None:
            run("apt_update", ["apt-get", "update", "-qq"])
            run("apt_zstd", ["apt-get", "install", "-y", "-qq", "zstd"])
        if TOOLROOT.exists():
            raise RuntimeError("PARTIAL_TOOLCHAIN_ROOT_EXISTS")
        TOOLROOT.mkdir(parents=True)
        run(
            "extract_toolchain",
            ["tar", "--use-compress-program=unzstd", "-xf", str(ASSET), "-C", str(TOOLROOT)],
        )
    if sha256(ASSET) != TOOLCHAIN_SHA256:
        raise RuntimeError("TOOLCHAIN_ASSET_HASH_MISMATCH")
    if not (BINDIR / "lean").is_file() or not (BINDIR / "lake").is_file():
        raise RuntimeError("TOOLCHAIN_EXECUTABLE_MISSING")
    os.environ["PATH"] = str(BINDIR) + os.pathsep + os.environ["PATH"]
    print("TOOLCHAIN_ASSET_URL=" + TOOLCHAIN_URL, flush=True)
    print("TOOLCHAIN_ASSET_SHA256=" + TOOLCHAIN_SHA256, flush=True)
    run("lean_version", ["lean", "--version"])
    run("lake_version", ["lake", "--version"])
    print("LEAN_SHA256=" + sha256(BINDIR / "lean"), flush=True)
    print("LAKE_SHA256=" + sha256(BINDIR / "lake"), flush=True)


def make_evidence(status: str, opened: str) -> tuple[str, str, str]:
    payload = {
        "runner_rev": RUNNER_REV,
        "source_sha": SOURCE_SHA,
        "source_blobs": SOURCE_BLOBS,
        "mathlib_sha": EXPECTED_MATHLIB,
        "toolchain_asset_sha256": TOOLCHAIN_SHA256,
        "restored_project_build": False,
        "status": status,
        "opened_utc": opened,
        "closed_utc": utc_now(),
        "records": RECORDS,
    }
    evidence_json = EVIDENCE / "evidence.json"
    evidence_json.write_text(
        json.dumps(payload, sort_keys=True, indent=2) + "\n",
        encoding="utf-8",
    )
    manifest = EVIDENCE / "MANIFEST.sha256"
    entries = []
    for path in sorted(EVIDENCE.iterdir()):
        if path.is_file() and path != manifest:
            entries.append(f"{sha256(path)}  {path.name}")
    manifest.write_text("\n".join(entries) + "\n", encoding="utf-8")
    with tarfile.open(ARCHIVE, "w:gz") as archive:
        archive.add(EVIDENCE, arcname=EVIDENCE.name)
    return sha256(evidence_json), sha256(manifest), sha256(ARCHIVE)


def main() -> int:
    opened = utc_now()
    status = "FAIL"
    print("RUNNER_REV=" + RUNNER_REV, flush=True)
    print("STAGE=runtime_open UTC=" + opened, flush=True)
    try:
        import psutil

        ram_gib = psutil.virtual_memory().total / 2**30
        print(f"RUNTIME=CPU RAM_GIB={ram_gib:.2f}", flush=True)
        if Path("/dev/nvidia0").exists():
            raise RuntimeError("GPU_RUNTIME_NOT_AUTHORIZED")
        if ram_gib < 40:
            raise RuntimeError("HIGH_RAM_REQUIRED")
        for path in (ROOT, EVIDENCE, ARCHIVE):
            if path.exists():
                raise RuntimeError("FRESH_PATH_ALREADY_EXISTS=" + str(path))

        ensure_toolchain()
        run("clone", ["git", "clone", "--no-tags", REPO_URL, str(ROOT)])
        run("checkout", ["git", "checkout", "--detach", SOURCE_SHA], cwd=ROOT)
        head = run("head", ["git", "rev-parse", "HEAD"], cwd=ROOT).strip()
        if head != SOURCE_SHA:
            raise RuntimeError("HEAD_MISMATCH=" + head)
        for relative, expected in SOURCE_BLOBS.items():
            actual = sha256(ROOT / relative)
            print(f"SOURCE_BLOB={relative} SHA256={actual}", flush=True)
            if actual != expected:
                raise RuntimeError("SOURCE_BLOB_HASH_MISMATCH=" + relative)

        source_paths = [path for path in SOURCE_BLOBS if path != "YangMillsCore.lean"]
        PATH_MANIFEST.write_text("\n".join(source_paths) + "\n", encoding="utf-8")
        run(
            "overlay_text_guard",
            [
                "python3", "scripts/check_lean_overlay_text.py",
                "--paths-from", str(PATH_MANIFEST), "--require-prevalidation",
            ],
            cwd=ROOT,
        )
        run(
            "import_prefix_guard",
            ["python3", "scripts/check_lean_import_prefix.py", *SOURCE_BLOBS],
            cwd=ROOT,
        )
        if (ROOT / "lean-toolchain").read_text(encoding="utf-8").strip() != EXPECTED_TOOLCHAIN:
            raise RuntimeError("LEAN_TOOLCHAIN_FILE_MISMATCH")
        manifest_before = sha256(ROOT / "lake-manifest.json")
        toolchain_before = sha256(ROOT / "lean-toolchain")
        run("lake_update", ["lake", "update"], cwd=ROOT)
        if sha256(ROOT / "lake-manifest.json") != manifest_before:
            raise RuntimeError("MANIFEST_DRIFT")
        if sha256(ROOT / "lean-toolchain") != toolchain_before:
            raise RuntimeError("TOOLCHAIN_FILE_DRIFT")
        mathlib = run(
            "mathlib_pin",
            ["git", "-C", ".lake/packages/mathlib", "rev-parse", "HEAD"],
            cwd=ROOT,
        ).strip()
        if mathlib != EXPECTED_MATHLIB:
            raise RuntimeError("MATHLIB_PIN_MISMATCH=" + mathlib)
        run("cache_get", ["lake", "exe", "cache", "get"], cwd=ROOT)
        run(
            "physical_uniform_owner_focal",
            [
                "lake", "build",
                "YangMills.RG.BalabanCMP89NeumannRectangularPhysicalUniformOwnerBound",
            ],
            cwd=ROOT,
        )
        audit = run(
            "physical_uniform_owner_audit",
            [
                "lake", "env", "lean",
                "YangMills/RG/"
                "BalabanCMP89NeumannRectangularPhysicalUniformOwnerBoundAudit.lean",
            ],
            cwd=ROOT,
        )
        parse_axioms_exact(audit)
        status = "PASS"
    except Exception as error:
        print("ERROR=" + repr(error), flush=True)
        traceback.print_exc()
    finally:
        evidence_hash, manifest_hash, archive_hash = make_evidence(status, opened)
        print("EVIDENCE_JSON_SHA256=" + evidence_hash, flush=True)
        print("EVIDENCE_MANIFEST_SHA256=" + manifest_hash, flush=True)
        print("EVIDENCE_ARCHIVE=" + str(ARCHIVE), flush=True)
        print("EVIDENCE_ARCHIVE_SHA256=" + archive_hash, flush=True)
        print("FINAL_STATUS=" + status, flush=True)
        print("RUNTIME_RETAINED_FOR_EVIDENCE_DOWNLOAD=1", flush=True)
    return 0 if status == "PASS" else 1


if __name__ == "__main__":
    raise SystemExit(main())
