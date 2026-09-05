#!/usr/bin/env python3
"""Cold Colab gate for the CMP89 physical rectangle/owner geometry.

The runner checks out one immutable source object in a fresh directory,
restores no project build state, verifies exact pins and source blobs, then
validates the reflection-period floor and physical CMP99-owner geometry plus
their exact axiom audits.  Passing does not construct CMP89 (2.42), produce a
uniform physical B0/delta0 pair, attain window 15, or move 20/41.
"""

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


RUNNER_REV = "cmp89-neumann-physical-owner-geometry-v1"
SOURCE_SHA = "1b9979c1371c68b6aaa9722afaa1314c41adfa49"
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
ROOT = CONTENT / "hrpoly-cmp89-physical-owner-geometry-cold-1b9979c1"
EVIDENCE = CONTENT / "hrpoly-cmp89-physical-owner-geometry-cold-1b9979c1-evidence"
ARCHIVE = CONTENT / "hrpoly-cmp89-physical-owner-geometry-cold-1b9979c1-evidence.tar.gz"
ASSET = CONTENT / "lean-4.29.0-rc6-linux.tar.zst"
TOOLROOT = CONTENT / "lean-4.29.0-rc6-linux"
BINDIR = TOOLROOT / "lean-4.29.0-rc6-linux" / "bin"
PATH_MANIFEST = CONTENT / "hrpoly-cmp89-physical-owner-geometry-paths.txt"

SOURCE_BLOBS = {
    "YangMills/RG/BalabanCMP89NeumannRectangularPeriodFloor.lean":
        "07a2e869fac8ae7a61a3b632db78e5a22b8a39cadae88c2ee520718e73e4da6d",
    "YangMills/RG/BalabanCMP89NeumannRectangularPeriodFloorAudit.lean":
        "0b36ae4340c37011314f23a86d798632d9cb205db1112b1f239e9808cd512df3",
    "YangMills/RG/BalabanCMP89NeumannRectangularPhysicalOwnerGeometry.lean":
        "e7cd4de4371073d091e4c8294e00b1d600595fd4953874d5099939c987cb5906",
    "YangMills/RG/BalabanCMP89NeumannRectangularPhysicalOwnerGeometryAudit.lean":
        "db3c18f5a4f2df1b1cf8a2b287c80ed713131ee19301a6c985b86333df323997",
    "YangMillsCore.lean":
        "93e72352260f51f3d2393d90f58455726f2bf44d926d37c9760c773c24f54c46",
}

PERIOD_AXIOMS = [
    "YangMills.RG.cmp89NeumannReflectionPeriodNat_ge_scale_of_side_floor_draft",
]
GEOMETRY_AXIOMS = [
    "YangMills.RG.cmp89SourceNeumannRectanglePointToFinBox_draft",
    "YangMills.RG.cmp89SourceNeumannRectanglePointToFinBox_val_draft",
    "YangMills.RG.finTorusDist_cmp89RectangleEmbedding_le_natAbs_sub_draft",
    "YangMills.RG.finBoxDist_cmp89RectangleEmbedding_le_l1_draft",
    "YangMills.RG.cmp89RectanglePhysicalOwner_mul_dist_le_l1_add_boundary_draft",
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


def parse_axioms_exact(output: str, expected: list[str]) -> None:
    compact = re.sub(r"\s+", "", output)
    for forbidden in ("sorryAx", "ofReduceBool"):
        if forbidden in compact:
            raise RuntimeError("FORBIDDEN_AXIOM=" + forbidden)
    blocks = re.findall(r"'([^']+)'dependsonaxioms:\[([^\]]*)\]", compact)
    found = {name: body for name, body in blocks}
    if set(found) != set(expected):
        raise RuntimeError(
            "AXIOM_DECLARATIONS_MISMATCH="
            + json.dumps({"found": sorted(found), "expected": expected})
        )
    for name in expected:
        axioms = {item for item in found[name].split(",") if item}
        if not axioms.issubset(ALLOWED_AXIOMS):
            raise RuntimeError(
                "AXIOM_SET=" + name + ":" + json.dumps(sorted(axioms))
            )
        print(
            "AXIOM_GATE=" + name + " AXIOMS=" + ",".join(sorted(axioms)),
            flush=True,
        )


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
        json.dumps(payload, sort_keys=True, indent=2) + "\n", encoding="utf-8"
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
            "period_floor_focal",
            ["lake", "build", "YangMills.RG.BalabanCMP89NeumannRectangularPeriodFloor"],
            cwd=ROOT,
        )
        period_audit = run(
            "period_floor_audit",
            [
                "lake", "env", "lean",
                "YangMills/RG/BalabanCMP89NeumannRectangularPeriodFloorAudit.lean",
            ],
            cwd=ROOT,
        )
        parse_axioms_exact(period_audit, PERIOD_AXIOMS)

        run(
            "physical_owner_geometry_focal",
            ["lake", "build", "YangMills.RG.BalabanCMP89NeumannRectangularPhysicalOwnerGeometry"],
            cwd=ROOT,
        )
        geometry_audit = run(
            "physical_owner_geometry_audit",
            [
                "lake", "env", "lean",
                "YangMills/RG/BalabanCMP89NeumannRectangularPhysicalOwnerGeometryAudit.lean",
            ],
            cwd=ROOT,
        )
        parse_axioms_exact(geometry_audit, GEOMETRY_AXIOMS)
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
