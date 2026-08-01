#!/usr/bin/env python3
"""Drive-free Colab validator v7 for the hRpoly combined Eq. (1.43) checkpoint.

This is transport and evidence infrastructure only.  It compiles SOURCE_A in
two independent fresh clones.  The commit containing this runner is DRIVER_B
and is never used as the mathematical source checkout.
"""

from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
import math
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tarfile
import time
import traceback
import urllib.error
import urllib.request
import uuid


REPO_URL = "https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME.git"
BASE_HEAD = "072b0955a1ee524fefa0826da4d34a432e69e6df"
SOURCE_A = "1f86b3c4ff9ebf52ac8b6f4ca7f22aa3b5cc92ad"
EXPECTED_TOOLCHAIN = "leanprover/lean4:v4.29.0-rc6"
EXPECTED_MATHLIB = "07642720480157414db592fa85b626dafb71355b"
TOOLCHAIN_ASSET_URL = (
    "https://github.com/leanprover/lean4/releases/download/v4.29.0-rc6/"
    "lean-4.29.0-rc6-linux.tar.zst"
)
TOOLCHAIN_ASSET_SHA256 = "bf3e0a4025e47a0bea9ed907d12dcccd3d3590b1d8ad6c55a915298b01ad9d3e"

DRIVER_ONLY_PATHS = {
    "docs/COLAB-HRPOLY-VALIDATION-RUNBOOK-v6.md",
    "scripts/colab_hrpoly_validation_v6.py",
}

SOURCE_HASHES = {
    "YangMills/RG/BalabanCMP102Eq80PhysicalDomainFTCEq143SourceMetric.lean": "6dbaf33455b9b11a7ded7169d5ff127660f3794c8bf0c3ab5b19c8b37d59e171",
    "YangMills/RG/BalabanCMP102Eq80SourcePi4DomainEnumeration.lean": "49eb28e348754c8b489ca52727ab1bc0322edb2fe051350bf8543e34a36e657d",
    "YangMills/RG/BalabanCMP109Lemma1CoarsenedResidualFamily.lean": "207cee0900f5ae163394c9244c8364064b6cdbea6a585da87999caed637f34c5",
    "YangMills/RG/BalabanCMP116Eq143To219.lean": "5f890c02a5d9ad4e91aea85427dbd6ea23a538d8db8dc06f3479a545c39ddd03",
    "YangMills/RG/BalabanCMP116Eq219RootedResummation.lean": "119cd65a97f095b862861846dcc12e4efe04ecc03e26604c75103833432e08d3",
    "YangMills/RG/BalabanCMP116Eq219SourceGeometry.lean": "d2016d4e68229cbf727241cffb378effdbaac36b8e316db1596c44f6f9b3d732",
    "YangMills/RG/BalabanCMP116Eq220CenteredPhysicalQuadraticRate.lean": "b906cb3ac036ed9daa7d5b2a02c8712bf497b33d84a19a3dec76b20c1f2cdfce",
    "YangMills/RG/BalabanCMP116Eq220CenteredSourcePotential.lean": "94c4d0122472431b8b0d0facedcf8e7b1cfdd019e6f775ef9c4b3c0780486f88",
    "YangMills/RG/BalabanCMP116Eq226CenteredConditionedCombinedPartialTermSourceConstructor.lean": "8c2c933057ab94153181be96a196eb68fbbd74fbc63961aeba29a372344391e8",
    "YangMills/RG/BalabanCMP116Eq226CenteredConditionedCombinedPartialTermSourceConstructorAudit.lean": "b78c4b36c4f2befd8ecebe59248230abebcb6bfb503371a857218f21833417e7",
    "YangMills/RG/BalabanCMP116Eq226CenteredConditionedPhysicalTermSource.lean": "ef4f25752063d70f1d567402e01862b2ce9700d1a696d301b719d7b604385b4e",
    "YangMills/RG/BalabanCMP116Eq226OptimalInteractionAlpha.lean": "b53375f51ca6bed51ebc9447dc8c3c80dd075736f7de64a2a4c13671db9070f6",
    "YangMills/RG/BalabanCMP116Eq226OptimalInteractionAlphaAudit.lean": "cf61a70ceaca561a9aefa4ac6f3a661797a5c596508eb6d812be8b0488c6caf1",
    "YangMills/RG/BalabanCMP116Eq80Lemma1CombinedDomainDictionary.lean": "882b863769c024b154cb2e8afaa9b75268717c6506016779cc022d662304aaa2",
    "YangMills/RG/BalabanCMP116Eq80Lemma1CombinedQuadraticCore.lean": "187d4b5404045c91de2eb9204bde2b5edc4980b40c2880bcd1117d43c3a7bf90",
    "YangMills/RG/BalabanCMP116Eq80Lemma1CombinedKernelSupport.lean": "2f89a9bf85c3357eadf23c6cf60af2651c2e6b26ab78f652b91b1aa1a631f1c4",
    "YangMills/RG/BalabanCMP116Eq80Lemma1CombinedKernelSupportAudit.lean": "99818abaa2e80394c079704fbe63e4163bc68962b5d667709db521509d1538ec",
    "YangMills/RG/BalabanCMP116Eq80Lemma1CombinedHessianSupport.lean": "ec7a418608fbdafe5e80c0d66f9778921b3d6ff84795e048d0440d6196e3651d",
    "YangMills/RG/BalabanCMP116Eq80Lemma1CombinedHessianSupportAudit.lean": "da815b4d8a69941eedcec8a06cc569c0e011be3e496ec9f00bb120163dbf9eea",
    "YangMills/RG/BalabanCMP116Eq80Lemma1CombinedTerminalEq143.lean": "41b62ed3ba3fd1f29ce4f1c583ca702f9eebedfa73c0ebab264d0f0977013e7c",
    "YangMills/RG/BalabanCMP116Eq80Lemma1CombinedTerminalEq143Audit.lean": "61faefdfc7180aa06a47e6718cf8709c0f0501e7b21d47197d5a9ebb63deb8d1",
    "YangMills/RG/BalabanCMP116RadialTaylorBound.lean": "9f881eb9a260061e4f3b03aa9cc20eb94aaa072532f010e7f6b9f038767503fb",
    "YangMills/RG/BalabanCMP116SourceCenteredPhysicalAEInteraction.lean": "76af7e4a78f1f72e5810dacf925ca81a8bc64bbe1206dca9f0eb2534a70c9d53",
    "YangMills/RG/BalabanCMP116SourceCenteredPhysicalQuadraticResidualAEInteraction.lean": "00d7116bc43c2cdd9ae0cef1372663f05b116137a854965520d788b4744143cb",
    "YangMills/RG/BalabanCMP116SourceRestrictedConditionedCenteredPhysicalEq226Boundary.lean": "cb4d53a17d95cd021743cacb59ba51ad0edb3d87a7b391a481cf870780afc2fa",
    "YangMills/RG/BalabanCMP116SourceRestrictedConditionedCenteredPhysicalInteractionProducer.lean": "deabaec26a535981d8ff06b887f2dcc43cec70a7f574f01570b8113448511dc7",
    "docs/HRPOLY-CMP102-CMP116-VERTICAL-SLICE.md": "2baf0aef6933a86edc05e05b7e981cf1e58d7208cea995a0998f6d3ea13c961b",
}

QUEUE = [
    ("restricted_visited_transfer_powers", "lake build YangMills.RG.BalabanCMP116RestrictedVisitedTransferPowers", False),
    ("mathlib_pin", "git -C .lake/packages/mathlib rev-parse HEAD", False),
    ("optimal_interaction_alpha", "lake build YangMills.RG.BalabanCMP116Eq226OptimalInteractionAlpha", False),
    ("optimal_interaction_alpha_audit", "lake env lean YangMills/RG/BalabanCMP116Eq226OptimalInteractionAlphaAudit.lean", True),
    ("combined_kernel_support", "lake build YangMills.RG.BalabanCMP116Eq80Lemma1CombinedKernelSupport", False),
    ("combined_kernel_support_audit", "lake env lean YangMills/RG/BalabanCMP116Eq80Lemma1CombinedKernelSupportAudit.lean", True),
    ("combined_hessian_support", "lake build YangMills.RG.BalabanCMP116Eq80Lemma1CombinedHessianSupport", False),
    ("combined_hessian_support_audit", "lake env lean YangMills/RG/BalabanCMP116Eq80Lemma1CombinedHessianSupportAudit.lean", True),
    ("combined_terminal_eq143", "lake build YangMills.RG.BalabanCMP116Eq80Lemma1CombinedTerminalEq143", False),
    ("combined_terminal_eq143_audit", "lake env lean YangMills/RG/BalabanCMP116Eq80Lemma1CombinedTerminalEq143Audit.lean", True),
    ("partial_termsource_constructor", "lake build YangMills.RG.BalabanCMP116Eq226CenteredConditionedCombinedPartialTermSourceConstructor", False),
    ("partial_termsource_constructor_audit", "lake env lean YangMills/RG/BalabanCMP116Eq226CenteredConditionedCombinedPartialTermSourceConstructorAudit.lean", True),
    ("yangmills_core", "lake build YangMillsCore", False),
    ("full_oracle", "lake env lean oracle_check.lean", True),
]

ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
AXIOM_RE = re.compile(r"depends on axioms:\s*\[([^]]*)\]")


def utc_now() -> str:
    return dt.datetime.now(dt.timezone.utc).isoformat()


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as src:
        for chunk in iter(lambda: src.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def write_json(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def command_output(args: list[str], cwd: Path) -> str:
    child = subprocess.run(args, cwd=cwd, text=True, capture_output=True)
    if child.returncode != 0:
        raise RuntimeError(
            f"command failed rc={child.returncode}: {args!r}\n"
            f"stdout:\n{child.stdout}\nstderr:\n{child.stderr}"
        )
    return child.stdout.strip()


def portable_run(command: str, *, cwd: Path, log: Path, metadata: Path) -> tuple[int, float]:
    started_utc = utc_now()
    started = time.perf_counter()
    env = os.environ.copy()
    env.update({"LC_ALL": "C", "LANG": "C", "NO_COLOR": "1"})
    with log.open("w", encoding="utf-8", errors="replace") as out:
        child = subprocess.run(
            ["bash", "-lc", command],
            cwd=cwd,
            stdout=out,
            stderr=subprocess.STDOUT,
            text=True,
            env=env,
        )
    elapsed = time.perf_counter() - started
    write_json(
        metadata,
        {
            "command": command,
            "cwd": str(cwd),
            "started_utc": started_utc,
            "ended_utc": utc_now(),
            "duration_seconds": elapsed,
            "returncode": child.returncode,
            "log_sha256": sha256(log),
        },
    )
    return child.returncode, elapsed


def log_tail(path: Path, lines: int = 80) -> str:
    text = path.read_text(encoding="utf-8", errors="replace")
    return "\n".join(text.splitlines()[-lines:])


def bootstrap_toolchain(evidence: Path) -> dict[str, object]:
    """Install the official pinned Lean release into ephemeral Colab storage."""
    root = Path("/content/hrpoly-toolchain-v4.29.0-rc6")
    archive = Path("/content/lean-4.29.0-rc6-linux.tar.zst")
    if root.exists() or archive.exists():
        raise RuntimeError("toolchain bootstrap paths already exist; refusing a reused runtime")

    bootstrap = evidence / "toolchain"
    bootstrap.mkdir(parents=True, exist_ok=False)
    if shutil.which("curl") is None:
        raise RuntimeError("curl is absent from the Colab image")
    rc, _ = portable_run(
        "curl --fail --location --retry 5 --retry-all-errors --retry-delay 2 "
        "--connect-timeout 30 --output /content/lean-4.29.0-rc6-linux.tar.zst "
        + TOOLCHAIN_ASSET_URL,
        cwd=Path("/content"),
        log=bootstrap / "download.log",
        metadata=bootstrap / "download.json",
    )
    if rc != 0:
        raise RuntimeError(
            f"official toolchain download failed rc={rc}\n{log_tail(bootstrap / 'download.log')}"
        )
    asset_bytes = archive.stat().st_size
    asset_hash = sha256(archive)
    if asset_hash != TOOLCHAIN_ASSET_SHA256:
        raise RuntimeError(
            f"toolchain asset hash mismatch: {asset_hash} != {TOOLCHAIN_ASSET_SHA256}; "
            f"bytes={asset_bytes}"
        )

    if shutil.which("unzstd") is None:
        rc, _ = portable_run(
            "apt-get update -qq && DEBIAN_FRONTEND=noninteractive apt-get install -y -qq zstd",
            cwd=Path("/content"),
            log=bootstrap / "install-zstd.log",
            metadata=bootstrap / "install-zstd.json",
        )
        if rc != 0 or shutil.which("unzstd") is None:
            raise RuntimeError(
                f"zstd installation failed rc={rc}\n{log_tail(bootstrap / 'install-zstd.log')}"
            )

    root.mkdir(parents=True, exist_ok=False)
    rc, _ = portable_run(
        "tar --use-compress-program=unzstd -xf /content/lean-4.29.0-rc6-linux.tar.zst "
        "-C /content/hrpoly-toolchain-v4.29.0-rc6",
        cwd=Path("/content"),
        log=bootstrap / "extract.log",
        metadata=bootstrap / "extract.json",
    )
    if rc != 0:
        raise RuntimeError(f"toolchain extraction failed rc={rc}\n{log_tail(bootstrap / 'extract.log')}")

    lake_candidates = sorted(root.glob("*/bin/lake"))
    if len(lake_candidates) != 1:
        raise RuntimeError(f"expected one extracted bin/lake, found {lake_candidates}")
    bin_dir = lake_candidates[0].parent
    lean = bin_dir / "lean"
    lake = bin_dir / "lake"
    if not lean.is_file() or not lake.is_file():
        raise RuntimeError(f"incomplete toolchain bin directory: {bin_dir}")
    os.environ["PATH"] = f"{bin_dir}{os.pathsep}{os.environ.get('PATH', '')}"

    lean_version = command_output([str(lean), "--version"], Path("/content"))
    lake_version = command_output([str(lake), "--version"], Path("/content"))
    result = {
        "asset_url": TOOLCHAIN_ASSET_URL,
        "asset_bytes": asset_bytes,
        "asset_sha256": asset_hash,
        "expected_asset_sha256": TOOLCHAIN_ASSET_SHA256,
        "bin_dir": str(bin_dir),
        "lean_version": lean_version,
        "lake_version": lake_version,
        "lean_sha256": sha256(lean),
        "lake_sha256": sha256(lake),
    }
    write_json(bootstrap / "toolchain-gate.json", result)
    print("TOOLCHAIN_GATE_OK", json.dumps(result, sort_keys=True), flush=True)
    return result


def preflight(evidence: Path, run_id: str) -> dict[str, object]:
    sentinel = Path("/content/HRPOLY_V7_QUEUE_STARTED")
    states: dict[str, object] = {"absent_before": not sentinel.exists()}
    if not states["absent_before"]:
        raise RuntimeError(f"sentinel already exists: {sentinel}")
    with sentinel.open("x", encoding="utf-8") as out:
        out.write(run_id)
    states["exclusive_creation"] = sentinel.exists()
    states["identity_matches"] = sentinel.read_text(encoding="utf-8") == run_id
    try:
        sentinel.open("x").close()
        states["duplicate_rejected"] = False
    except FileExistsError:
        states["duplicate_rejected"] = True
    if not all(bool(v) for v in states.values()):
        raise RuntimeError(f"sentinel preflight failed: {states}")

    ok_rc, ok_dt = portable_run(
        "true",
        cwd=Path("/content"),
        log=evidence / "preflight_true.log",
        metadata=evidence / "preflight_true.json",
    )
    bad_rc, bad_dt = portable_run(
        "exit 23",
        cwd=Path("/content"),
        log=evidence / "preflight_exit23.log",
        metadata=evidence / "preflight_exit23.json",
    )
    durations_ok = all(math.isfinite(x) and x >= 0 for x in (ok_dt, bad_dt))
    result = {
        "sentinel": states,
        "true_returncode": ok_rc,
        "exit23_returncode": bad_rc,
        "durations_finite_nonnegative": durations_ok,
    }
    if ok_rc != 0 or bad_rc != 23 or not durations_ok:
        raise RuntimeError(f"portable runner preflight failed: {result}")
    write_json(evidence / "preflight.json", result)
    print("PREFLIGHT_OK", json.dumps(result, sort_keys=True), flush=True)
    return result


def verify_driver(driver: Path, driver_b: str, evidence: Path) -> None:
    head = command_output(["git", "rev-parse", "HEAD"], driver)
    if head != driver_b:
        raise RuntimeError(f"driver HEAD mismatch: {head} != {driver_b}")
    ancestor = subprocess.run(
        ["git", "merge-base", "--is-ancestor", SOURCE_A, driver_b], cwd=driver
    ).returncode
    if ancestor != 0:
        raise RuntimeError(f"SOURCE_A is not an ancestor of driver checkpoint {driver_b}")
    changed = set(
        filter(
            None,
            command_output(["git", "diff", "--name-only", SOURCE_A, driver_b], driver).splitlines(),
        )
    )
    if changed != DRIVER_ONLY_PATHS:
        raise RuntimeError(f"A..B touched unexpected paths: {sorted(changed)}")
    write_json(
        evidence / "driver_gate.json",
        {
            "driver_head": head,
            "source_ancestor": SOURCE_A,
            "driver_only_paths": sorted(changed),
        },
    )
    print("DRIVER_GATE_OK", head, SOURCE_A, flush=True)


def clone_source(label: str, repo_url: str, root: Path, evidence: Path) -> None:
    if root.exists():
        raise RuntimeError(f"fresh clone path already exists: {root}")
    log_dir = evidence / label
    log_dir.mkdir(parents=True, exist_ok=False)
    clone_cmd = f"git clone --no-tags {repo_url} {root}"
    rc, _ = portable_run(
        clone_cmd,
        cwd=Path("/content"),
        log=log_dir / "clone.log",
        metadata=log_dir / "clone.json",
    )
    if rc != 0:
        raise RuntimeError(f"{label}: git clone failed rc={rc}")
    checkout_cmd = f"git checkout --detach {SOURCE_A}"
    rc, _ = portable_run(
        checkout_cmd,
        cwd=root,
        log=log_dir / "checkout.log",
        metadata=log_dir / "checkout.json",
    )
    if rc != 0:
        raise RuntimeError(f"{label}: checkout SOURCE_A failed rc={rc}")


def verify_source(label: str, root: Path, evidence: Path) -> dict[str, object]:
    head = command_output(["git", "rev-parse", "HEAD"], root)
    if head != SOURCE_A:
        raise RuntimeError(f"{label}: source HEAD mismatch: {head}")
    base_changed = set(
        filter(None, command_output(["git", "diff", "--name-only", BASE_HEAD, SOURCE_A], root).splitlines())
    )
    if base_changed != set(SOURCE_HASHES):
        raise RuntimeError(
            f"{label}: SOURCE_A changes are not exactly the 27 manifest paths: "
            f"missing={sorted(set(SOURCE_HASHES) - base_changed)} "
            f"extra={sorted(base_changed - set(SOURCE_HASHES))}"
        )
    actual_hashes = {name: sha256(root / name) for name in SOURCE_HASHES}
    mismatches = {
        name: {"expected": SOURCE_HASHES[name], "actual": actual_hashes[name]}
        for name in SOURCE_HASHES
        if actual_hashes[name] != SOURCE_HASHES[name]
    }
    if mismatches:
        raise RuntimeError(f"{label}: source hash mismatch: {mismatches}")
    toolchain = (root / "lean-toolchain").read_text(encoding="utf-8").strip()
    if toolchain != EXPECTED_TOOLCHAIN:
        raise RuntimeError(f"{label}: toolchain mismatch: {toolchain}")
    status = command_output(["git", "status", "--short"], root)
    if status:
        raise RuntimeError(f"{label}: source checkout is dirty: {status}")
    result = {
        "source_head": head,
        "base_head": BASE_HEAD,
        "source_file_count": len(actual_hashes),
        "source_hashes": actual_hashes,
        "toolchain": toolchain,
        "git_status": status,
    }
    write_json(evidence / label / "source_gate.json", result)
    print("SOURCE_GATE_OK", label, head, len(actual_hashes), flush=True)
    return result


def materialize_dependencies(label: str, root: Path, evidence: Path) -> dict[str, object]:
    """Resolve the pinned manifest and fetch caches without permitting pin drift."""
    log_dir = evidence / label / "dependencies"
    log_dir.mkdir(parents=True, exist_ok=False)
    toolchain_file = root / "lean-toolchain"
    manifest_file = root / "lake-manifest.json"
    before = {
        "lean_toolchain_sha256": sha256(toolchain_file),
        "lake_manifest_sha256": sha256(manifest_file),
    }
    rc, elapsed = portable_run(
        "lake exe cache get",
        cwd=root,
        log=log_dir / "cache-get.log",
        metadata=log_dir / "cache-get.json",
    )
    mathlib = root / ".lake" / "packages" / "mathlib"
    update_used = False
    if not mathlib.exists():
        update_used = True
        update_rc, _ = portable_run(
            "lake update",
            cwd=root,
            log=log_dir / "lake-update.log",
            metadata=log_dir / "lake-update.json",
        )
        after_update = {
            "lean_toolchain_sha256": sha256(toolchain_file),
            "lake_manifest_sha256": sha256(manifest_file),
        }
        if update_rc != 0:
            raise RuntimeError(
                f"{label}: lake update failed rc={update_rc}\n{log_tail(log_dir / 'lake-update.log')}"
            )
        if after_update != before:
            subprocess.run(
                ["git", "restore", "--source=HEAD", "--", "lean-toolchain", "lake-manifest.json"],
                cwd=root,
                check=True,
            )
            raise RuntimeError(
                f"{label}: lake update changed pinned inputs; restored and rejected: "
                f"before={before} after={after_update}"
            )
        rc, elapsed = portable_run(
            "lake exe cache get",
            cwd=root,
            log=log_dir / "cache-get-after-update.log",
            metadata=log_dir / "cache-get-after-update.json",
        )
    after = {
        "lean_toolchain_sha256": sha256(toolchain_file),
        "lake_manifest_sha256": sha256(manifest_file),
    }
    if after != before:
        raise RuntimeError(f"{label}: dependency bootstrap changed pinned inputs: {before} -> {after}")
    if not mathlib.exists():
        raise RuntimeError(f"{label}: Mathlib checkout missing after dependency bootstrap")
    mathlib_pin = command_output(["git", "rev-parse", "HEAD"], mathlib)
    if mathlib_pin != EXPECTED_MATHLIB:
        raise RuntimeError(f"{label}: Mathlib pin mismatch after bootstrap: {mathlib_pin}")
    status = command_output(["git", "status", "--short"], root)
    if status:
        raise RuntimeError(f"{label}: dependency bootstrap dirtied source checkout: {status}")
    result = {
        "cache_get_returncode": rc,
        "cache_get_seconds": elapsed,
        "cache_available": rc == 0,
        "compiled_from_source_if_needed": rc != 0,
        "lake_update_used": update_used,
        "mathlib_pin": mathlib_pin,
        "pinned_file_hashes": after,
    }
    write_json(log_dir / "dependency-gate.json", result)
    print("DEPENDENCY_GATE_OK", label, json.dumps(result, sort_keys=True), flush=True)
    if rc != 0:
        print(
            "CACHE_GET_UNAVAILABLE_CONTINUING_WITH_SOURCE_BUILD",
            label,
            log_tail(log_dir / ("cache-get-after-update.log" if update_used else "cache-get.log"), 20),
            flush=True,
        )
    return result


def parse_axioms(log_text: str) -> list[list[str]]:
    results: list[list[str]] = []
    for match in AXIOM_RE.finditer(log_text):
        axioms = sorted(x.strip() for x in match.group(1).split(",") if x.strip())
        if not set(axioms).issubset(ALLOWED_AXIOMS):
            raise RuntimeError(f"disallowed axioms: {axioms}")
        results.append(axioms)
    return results


def run_queue(label: str, root: Path, evidence: Path) -> dict[str, object]:
    if shutil.which("lake") is None:
        raise RuntimeError("lake is absent after verified official toolchain bootstrap")
    entries: list[dict[str, object]] = []
    log_dir = evidence / label / "queue"
    log_dir.mkdir(parents=True, exist_ok=False)
    for index, (name, command, is_audit) in enumerate(QUEUE, start=1):
        print("TARGET_START", label, index, name, command, flush=True)
        log = log_dir / f"{index:02d}-{name}.log"
        metadata = log_dir / f"{index:02d}-{name}.json"
        rc, elapsed = portable_run(command, cwd=root, log=log, metadata=metadata)
        text = log.read_text(encoding="utf-8", errors="replace")
        axioms: list[list[str]] = []
        if is_audit and rc == 0:
            axioms = parse_axioms(text)
            if not axioms:
                raise RuntimeError(f"{label}:{name}: audit emitted no #print axioms result")
        entry = {
            "name": name,
            "command": command,
            "returncode": rc,
            "audit_axioms": axioms,
        }
        entries.append(entry)
        print("TARGET_END", label, index, name, "rc", rc, "seconds", elapsed, flush=True)
        if rc != 0:
            raise RuntimeError(
                f"{label}:{name}: first command failure rc={rc}; log tail:\n{log_tail(log)}"
            )
        if name == "mathlib_pin":
            pin = text.strip().splitlines()[-1] if text.strip() else ""
            if pin != EXPECTED_MATHLIB:
                raise RuntimeError(f"{label}: Mathlib pin mismatch: {pin}")
    semantic = {
        "source_head": SOURCE_A,
        "base_head": BASE_HEAD,
        "toolchain": EXPECTED_TOOLCHAIN,
        "mathlib_pin": EXPECTED_MATHLIB,
        "source_hashes": SOURCE_HASHES,
        "queue": entries,
    }
    write_json(evidence / label / "semantic-result.json", semantic)
    print("QUEUE_GREEN", label, flush=True)
    return semantic


def write_hash_manifest(evidence: Path) -> Path:
    manifest = evidence / "SHA256SUMS"
    lines = []
    for path in sorted(evidence.rglob("*")):
        if path.is_file() and path != manifest:
            lines.append(f"{sha256(path)}  {path.relative_to(evidence).as_posix()}")
    manifest.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return manifest


def archive_evidence(evidence: Path) -> Path:
    archive = Path("/content") / f"{evidence.name}.tar.gz"
    with tarfile.open(archive, "w:gz") as out:
        out.add(evidence, arcname=evidence.name)
    return archive


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--driver-root", type=Path, required=True)
    parser.add_argument("--driver-checkpoint", required=True)
    parser.add_argument("--repo-url", default=REPO_URL)
    args = parser.parse_args()

    run_id = uuid.uuid4().hex
    evidence = Path("/content") / f"hrpoly-v7-evidence-{run_id}"
    evidence.mkdir(parents=True, exist_ok=False)
    session_started = time.perf_counter()
    summary: dict[str, object] = {
        "run_id": run_id,
        "started_utc": utc_now(),
        "repo_url": args.repo_url,
        "driver_checkpoint": args.driver_checkpoint,
        "source_checkpoint": SOURCE_A,
        "runtime": {
            "gpu_device_present": Path("/dev/nvidia0").exists(),
            "meminfo_first_line": Path("/proc/meminfo").read_text(encoding="utf-8").splitlines()[0],
            "python": sys.version,
        },
        "status": "RUNNING",
    }
    write_json(evidence / "summary.json", summary)
    exit_code = 1
    try:
        if summary["runtime"]["gpu_device_present"]:  # type: ignore[index]
            raise RuntimeError("GPU device detected; this run is authorized for CPU only")
        verify_driver(args.driver_root.resolve(), args.driver_checkpoint, evidence)
        preflight(evidence, run_id)
        toolchain = bootstrap_toolchain(evidence)
        summary["toolchain"] = toolchain

        roots = {
            "clone-a": Path("/content/hrpoly-source-a"),
            "clone-b": Path("/content/hrpoly-source-b"),
        }
        semantics: dict[str, object] = {}
        for label, root in roots.items():
            clone_source(label, args.repo_url, root, evidence)
            verify_source(label, root, evidence)
            materialize_dependencies(label, root, evidence)
            semantics[label] = run_queue(label, root, evidence)

        semantic_a = evidence / "clone-a" / "semantic-result.json"
        semantic_b = evidence / "clone-b" / "semantic-result.json"
        hash_a = sha256(semantic_a)
        hash_b = sha256(semantic_b)
        if hash_a != hash_b:
            raise RuntimeError(f"semantic output hashes differ: {hash_a} != {hash_b}")
        summary.update(
            {
                "status": "GREEN",
                "semantic_output_sha256_a": hash_a,
                "semantic_output_sha256_b": hash_b,
                "semantic_outputs_match": True,
            }
        )
        exit_code = 0
    except Exception as exc:  # stop-on-first-error, but retain exact evidence
        summary.update(
            {
                "status": "FAILED",
                "first_error_type": type(exc).__name__,
                "first_error": str(exc),
                "traceback": traceback.format_exc(),
            }
        )
        print("FIRST_ERROR", type(exc).__name__, str(exc), flush=True)
    finally:
        summary["ended_utc"] = utc_now()
        summary["connected_run_seconds"] = time.perf_counter() - session_started
        write_json(evidence / "summary.json", summary)
        write_hash_manifest(evidence)
        archive = archive_evidence(evidence)
        print("FINAL_STATUS", summary["status"], flush=True)
        print("EVIDENCE_ARCHIVE", archive, flush=True)
        print("EVIDENCE_BYTES", archive.stat().st_size, flush=True)
        print("EVIDENCE_SHA256", sha256(archive), flush=True)
        print("CONNECTED_RUN_SECONDS", summary["connected_run_seconds"], flush=True)
    return exit_code


if __name__ == "__main__":
    raise SystemExit(main())
