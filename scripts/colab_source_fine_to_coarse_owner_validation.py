#!/usr/bin/env python3
"""Instrumental Colab gate for the separated fine-to-coarse owner dictionary.

The mathematical source checkpoint is immutable.  This wrapper reuses the
hash-pinned gate and replaces only ``lake update`` with deterministic package
materialization from the committed ``lake-manifest.json``.  Every network
operation has a hard timeout and every checked-out package SHA is verified.
"""

from __future__ import annotations

import hashlib
import importlib.util
import json
from pathlib import Path
import time
import urllib.request


SOURCE_SHA = "cb92d619c8ff95781d1f51ec9fad823b996120b4"
BASE_URL = (
    "https://raw.githubusercontent.com/lluiseriksson/"
    "THE-ERIKSSON-PROGRAMME/"
    "bcc852cee5e709bff91fad7de26fa21cff754e1f/"
    "scripts/colab_qprime_row_validation.py"
)
BASE_SHA256 = "d06b8a186c9fcefb54d6e21264d2467b6fb723b337be092d4c3380b875e47cee"
BASE_PATH = Path("/content/colab_qprime_row_validation.py")


def sha256_bytes(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest()


payload = urllib.request.urlopen(BASE_URL, timeout=60).read()
measured = sha256_bytes(payload)
print("BASE_RUNNER_SHA256=" + measured, flush=True)
if measured != BASE_SHA256:
    raise RuntimeError("BASE_RUNNER_HASH_MISMATCH")
BASE_PATH.write_bytes(payload)

spec = importlib.util.spec_from_file_location("owner_dictionary_base", BASE_PATH)
if spec is None or spec.loader is None:
    raise RuntimeError("BASE_RUNNER_IMPORT_SPEC_MISSING")
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)

runner.RUNNER_REV = "source-fine-to-coarse-owner-v3-length-composition"
runner.SOURCE_SHA = SOURCE_SHA
runner.ROOT = Path("/content/hrpoly-source-fine-to-coarse-owner")
runner.EVIDENCE = Path("/content/hrpoly-source-fine-to-coarse-owner-evidence")
runner.ARCHIVE = Path("/content/hrpoly-source-fine-to-coarse-owner-evidence.tar.gz")
runner.PATH_MANIFEST = Path("/content/hrpoly-source-fine-to-coarse-owner-paths.txt")
runner.SOURCE_BLOBS = {
    "YangMills/RG/BalabanCMP99SourceFineToCoarseCenteredOwnerDictionary.lean":
        "34c498be457f082018f0f9ee724b377b741f7d39a153e7d566560413cbe25fd6",
    "YangMills/RG/BalabanCMP99SourceFineToCoarseCenteredOwnerDictionaryAudit.lean":
        "42bac8e320df05f310c455fd498e90bf5be5ee43b67fb3872ceea1c08f2d0b90",
}
runner.QUEUE = [
    (
        "owner_dictionary_focal",
        [
            "lake", "build",
            "YangMills.RG.BalabanCMP99SourceFineToCoarseCenteredOwnerDictionary",
        ],
        None,
    ),
    (
        "owner_dictionary_audit",
        [
            "lake", "env", "lean",
            "YangMills/RG/BalabanCMP99SourceFineToCoarseCenteredOwnerDictionaryAudit.lean",
        ],
        4,
    ),
]

base_run = runner.run


def materialize_manifest_packages() -> str:
    started = time.perf_counter()
    manifest_path = runner.ROOT / "lake-manifest.json"
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    packages = manifest.get("packages")
    if not isinstance(packages, list):
        raise RuntimeError("MANIFEST_PACKAGES_NOT_LIST")
    package_root = runner.ROOT / ".lake" / "packages"
    package_root.mkdir(parents=True, exist_ok=True)
    print(
        "STAGE=lake_update MODE=PINNED_MANIFEST PACKAGE_COUNT="
        + str(len(packages)),
        flush=True,
    )
    for package in packages:
        name = package.get("name")
        url = package.get("url")
        rev = package.get("rev")
        if not all(isinstance(value, str) and value for value in (name, url, rev)):
            raise RuntimeError("INVALID_MANIFEST_PACKAGE=" + repr(package))
        destination = package_root / name
        if destination.exists():
            raise RuntimeError("PACKAGE_DESTINATION_EXISTS=" + name)
        safe_name = "".join(char if char.isalnum() else "_" for char in name)
        base_run(
            "package_init_" + safe_name,
            ["git", "init", str(destination)],
            cwd=runner.ROOT,
        )
        base_run(
            "package_remote_" + safe_name,
            ["git", "-C", str(destination), "remote", "add", "origin", url],
            cwd=runner.ROOT,
        )
        fetch_options = ["fetch", "--depth=1"]
        if name == "proofwidgets":
            # Its Lake release target resolves the cloud artifact through the
            # tag naming this exact revision; a SHA-only shallow fetch omits it.
            fetch_options.append("--tags")
        base_run(
            "package_fetch_" + safe_name,
            [
                "timeout", "300s", "git", "-c", "http.version=HTTP/1.1",
                "-C", str(destination), *fetch_options, "origin", rev,
            ],
            cwd=runner.ROOT,
        )
        base_run(
            "package_checkout_" + safe_name,
            ["git", "-C", str(destination), "checkout", "--detach", "FETCH_HEAD"],
            cwd=runner.ROOT,
        )
        actual = base_run(
            "package_pin_" + safe_name,
            ["git", "-C", str(destination), "rev-parse", "HEAD"],
            cwd=runner.ROOT,
        ).strip()
        if actual != rev:
            raise RuntimeError(
                "PACKAGE_PIN_MISMATCH=" + name + " ACTUAL=" + actual
            )
    elapsed = time.perf_counter() - started
    runner.RECORDS.append(
        {
            "stage": "lake_update",
            "exit": 0,
            "seconds": elapsed,
            "mode": "pinned_manifest_materialization",
        }
    )
    print("STAGE=lake_update EXIT=0 SECONDS=%.3f" % elapsed, flush=True)
    return ""


def patched_run(stage: str, command: list[str], *, cwd: Path | None = None) -> str:
    if stage == "lake_update":
        return materialize_manifest_packages()
    return base_run(stage, command, cwd=cwd)


runner.run = patched_run

if __name__ == "__main__":
    raise SystemExit(runner.main())
