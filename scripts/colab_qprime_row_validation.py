#!/usr/bin/env python3
"""Fresh-clone Colab gate for the signed CMP99 first-species brick.

This validation runner compiles the immutable PRE-VALIDATION source checkpoint
named by ``SOURCE_SHA``.  It is infrastructure only: the source object and its
two Lean blobs are hash-gated before any Lean command is run.
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


RUNNER_REV = "signed-covariant-link-v6"
SOURCE_SHA = "46734245d55a2ae309a01e6b371b35418189dd0f"
REPO_URL = "https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME.git"
EXPECTED_TOOLCHAIN = "leanprover/lean4:v4.29.0-rc6"
EXPECTED_MATHLIB = "07642720480157414db592fa85b626dafb71355b"
TOOLCHAIN_URL = (
    "https://github.com/leanprover/lean4/releases/download/v4.29.0-rc6/"
    "lean-4.29.0-rc6-linux.tar.zst"
)
TOOLCHAIN_SHA256 = "bf3e0a4025e47a0bea9ed907d12dcccd3d3590b1d8ad6c55a915298b01ad9d3e"
ROOT = Path("/content/hrpoly-signed-covariant-link")
EVIDENCE = Path("/content/hrpoly-signed-covariant-link-evidence")
ARCHIVE = Path("/content/hrpoly-signed-covariant-link-evidence.tar.gz")
ASSET = Path("/content/lean-4.29.0-rc6-linux.tar.zst")
TOOLROOT = Path("/content/lean-4.29.0-rc6-linux")
PATH_MANIFEST = Path("/content/hrpoly-signed-covariant-link-paths.txt")

SOURCE_BLOBS = {
    "YangMills/RG/BalabanCMP99Eq389SignedCovariantLinkPhysicalBound.lean":
        "11447809e24a3a1dc8675215b89dd241075f19753dff146eb126050282a99a6f",
    "YangMills/RG/BalabanCMP99Eq389SignedCovariantLinkPhysicalBoundAudit.lean":
        "63fd60cb8f7ffe7599b26b3fa82f30471a123e0a03d077dbcc182bb88ce6824f",
}

QUEUE = [
    (
        "signed_covariant_link_focal",
        [
            "lake", "build",
            "YangMills.RG.BalabanCMP99Eq389SignedCovariantLinkPhysicalBound",
        ],
        None,
    ),
    (
        "signed_covariant_link_audit",
        [
            "lake", "env", "lean",
            "YangMills/RG/BalabanCMP99Eq389SignedCovariantLinkPhysicalBoundAudit.lean",
        ],
        15,
    ),
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


def run(stage: str, command: list[str], *, cwd: Path | None = None) -> str:
    started = time.perf_counter()
    print("STAGE=" + stage + " CMD=" + json.dumps(command), flush=True)
    child = subprocess.run(
        command,
        cwd=cwd,
        env=os.environ.copy(),
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
    )
    elapsed = time.perf_counter() - started
    output = child.stdout
    print(output, flush=True)
    RECORDS.append(
        {
            "stage": stage,
            "exit": child.returncode,
            "seconds": elapsed,
            "output_sha256": hashlib.sha256(output.encode()).hexdigest(),
        }
    )
    print(
        "STAGE=" + stage + " EXIT=" + str(child.returncode)
        + " SECONDS=%.3f" % elapsed,
        flush=True,
    )
    if child.returncode != 0:
        raise RuntimeError("FIRST_ERROR=" + stage)
    return output


def parse_axioms(output: str, expected: int) -> None:
    compact = re.sub(r"\s+", "", output)
    for forbidden in ("sorryAx", "ofReduceBool"):
        if forbidden in compact:
            raise RuntimeError("FORBIDDEN_AXIOM=" + forbidden)
    blocks = re.findall(r"dependsonaxioms:\[([^\]]*)\]", compact)
    if len(blocks) != expected:
        raise RuntimeError(f"AXIOM_BLOCK_COUNT={len(blocks)} EXPECTED={expected}")
    for index, body in enumerate(blocks):
        names = {name for name in body.split(",") if name}
        if not names.issubset(ALLOWED_AXIOMS):
            raise RuntimeError(f"AXIOM_SET_{index}={sorted(names)}")


def verify_source_blobs() -> None:
    for relative, expected in SOURCE_BLOBS.items():
        actual = sha256(ROOT / relative)
        print(
            "SOURCE_BLOB=" + relative + " SHA256=" + actual,
            flush=True,
        )
        if actual != expected:
            raise RuntimeError("SOURCE_BLOB_HASH_MISMATCH=" + relative)


def make_evidence(status: str, opened: str) -> tuple[str, str]:
    payload = json.dumps(
        {
            "runner_rev": RUNNER_REV,
            "source_sha": SOURCE_SHA,
            "source_blobs": SOURCE_BLOBS,
            "mathlib_sha": EXPECTED_MATHLIB,
            "toolchain_asset_sha256": TOOLCHAIN_SHA256,
            "status": status,
            "opened_utc": opened,
            "closed_utc": utc_now(),
            "records": RECORDS,
        },
        sort_keys=True,
        separators=(",", ":"),
    )
    EVIDENCE.mkdir(parents=True, exist_ok=True)
    (EVIDENCE / "evidence.json").write_text(payload + "\n", encoding="utf-8")
    if ARCHIVE.exists():
        ARCHIVE.unlink()
    with tarfile.open(ARCHIVE, "w:gz") as archive:
        archive.add(EVIDENCE, arcname=EVIDENCE.name)
    return hashlib.sha256(payload.encode()).hexdigest(), sha256(ARCHIVE)


def main() -> int:
    opened = utc_now()
    status = "FAIL"
    print("RUNNER_REV=" + RUNNER_REV, flush=True)
    print("STAGE=runtime_open UTC=" + opened, flush=True)
    try:
        import psutil

        ram_gib = psutil.virtual_memory().total / 2**30
        print("RUNTIME=CPU RAM_GIB=%.2f" % ram_gib, flush=True)
        if Path("/dev/nvidia0").exists():
            raise RuntimeError("GPU_RUNTIME_NOT_AUTHORIZED")
        if ram_gib < 40:
            raise RuntimeError("HIGH_RAM_REQUIRED")

        for path in (ROOT, EVIDENCE, TOOLROOT):
            if path.exists():
                shutil.rmtree(path)
        for path in (ASSET, ARCHIVE, PATH_MANIFEST):
            if path.exists():
                path.unlink()

        run(
            "download_toolchain",
            [
                "curl", "--fail", "--location", "--retry", "5",
                "--retry-all-errors", "--retry-delay", "2",
                "-o", str(ASSET), TOOLCHAIN_URL,
            ],
        )
        asset_hash = sha256(ASSET)
        print("TOOLCHAIN_ASSET_SHA256=" + asset_hash, flush=True)
        if asset_hash != TOOLCHAIN_SHA256:
            raise RuntimeError("TOOLCHAIN_HASH_MISMATCH")
        if shutil.which("unzstd") is None:
            run("apt_update", ["apt-get", "update", "-qq"])
            run("install_zstd", ["apt-get", "install", "-y", "-qq", "zstd"])
        TOOLROOT.mkdir(parents=True)
        run(
            "extract_toolchain",
            [
                "tar", "--use-compress-program=unzstd", "-xf", str(ASSET),
                "-C", str(TOOLROOT),
            ],
        )
        lake_candidates = list(TOOLROOT.glob("*/bin/lake"))
        if len(lake_candidates) != 1:
            raise RuntimeError("LAKE_CANDIDATE_COUNT=" + str(len(lake_candidates)))
        bindir = lake_candidates[0].parent
        os.environ["PATH"] = str(bindir) + os.pathsep + os.environ["PATH"]
        run("lean_version", ["lean", "--version"])
        run("lake_version", ["lake", "--version"])
        print("LEAN_SHA256=" + sha256(bindir / "lean"), flush=True)
        print("LAKE_SHA256=" + sha256(bindir / "lake"), flush=True)

        run("clone", ["git", "clone", "--no-tags", REPO_URL, str(ROOT)])
        run("checkout", ["git", "checkout", "--detach", SOURCE_SHA], cwd=ROOT)
        head = run("head", ["git", "rev-parse", "HEAD"], cwd=ROOT).strip()
        if head != SOURCE_SHA:
            raise RuntimeError("HEAD_MISMATCH=" + head)
        verify_source_blobs()
        PATH_MANIFEST.write_text(
            "\n".join(SOURCE_BLOBS) + "\n", encoding="utf-8"
        )
        run(
            "overlay_text_guard",
            [
                "python3", "scripts/check_lean_overlay_text.py",
                "--paths-from", str(PATH_MANIFEST),
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

        for stage, command, expected_axioms in QUEUE:
            output = run(stage, command, cwd=ROOT)
            if expected_axioms is not None:
                parse_axioms(output, expected_axioms)
        status = "PASS"
    except Exception as error:
        print("ERROR=" + repr(error), flush=True)
        traceback.print_exc()
    finally:
        evidence_hash, archive_hash = make_evidence(status, opened)
        print("EVIDENCE_SHA256=" + evidence_hash, flush=True)
        print("EVIDENCE_ARCHIVE=" + str(ARCHIVE), flush=True)
        print("EVIDENCE_ARCHIVE_SHA256=" + archive_hash, flush=True)
        print("FINAL_STATUS=" + status, flush=True)
        try:
            from google.colab import runtime

            runtime.unassign()
            print("RUNTIME_UNASSIGN_REQUESTED=1", flush=True)
        except Exception as error:
            print("RUNTIME_UNASSIGN_ERROR=" + repr(error), flush=True)
    return 0 if status == "PASS" else 1


if __name__ == "__main__":
    raise SystemExit(main())
