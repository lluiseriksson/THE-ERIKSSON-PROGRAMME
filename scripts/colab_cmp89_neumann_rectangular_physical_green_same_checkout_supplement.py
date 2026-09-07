#!/usr/bin/env python3
"""Fail-closed same-checkout supplement for the CMP89 physical Green gate.

The original cold runner created the checkout and all build state without a
restored project cache.  A later evidence-path instrumentation incident lost
the focal exit record.  This supplement re-verifies that exact checkout and
reruns both focals and exact axiom audits in the same checkout.  It never
creates or restores another project build directory.
"""

from __future__ import annotations

import datetime as dt
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tarfile
import time
import traceback


RUNNER_REV = "cmp89-neumann-physical-green-same-checkout-supplement-v1"
SOURCE_SHA = "e4834fe7fda3a272391323030c3e8e2f7c13a0c8"
EXPECTED_MATHLIB = "07642720480157414db592fa85b626dafb71355b"
EXPECTED_TOOLCHAIN = "leanprover/lean4:v4.29.0-rc6"
ROOT = Path("/content/hrpoly-cmp89-physical-green-cold-e4834fe7")
TOOLROOT = Path("/content/lean-4.29.0-rc6-linux")
BINDIR = TOOLROOT / "lean-4.29.0-rc6-linux" / "bin"
EVIDENCE = Path(
    "/content/hrpoly-cmp89-physical-green-cold-e4834fe7-same-checkout-supplement"
)
ARCHIVE = Path(str(EVIDENCE) + ".tar.gz")

SOURCE_BLOBS = {
    "YangMills/RG/BalabanCMP89NeumannReflectionRepresentation.lean":
        "50d0f6d919caba851414adb1fc88f12d515715a40f562b8a73e4eb88eecf4b0c",
    "YangMills/RG/BalabanCMP89NeumannReflectionRepresentationAudit.lean":
        "a0ede4a62753ff5b49dfa5033d66d22b3565b8cbcf2b24a433524251269fd216",
    "YangMills/RG/BalabanCMP89NeumannRectangularPhysicalGreenInsertion.lean":
        "693a7d4095f0b423f7095b5341dc918a1c06fdf5195e48f5e88917d6b562a75b",
    "YangMills/RG/BalabanCMP89NeumannRectangularPhysicalGreenInsertionAudit.lean":
        "f6dc340f234db21405d0bf6011e9becb84f4a693f6084057c19c93321e945b91",
    "YangMillsCore.lean":
        "d28473054fd913fb74047d923ea4389d4ddcad92820cc78e2b7ad3f9fe7d1de9",
}

REPRESENTATION_AXIOMS = [
    "YangMills.RG.CMP89NeumannReflectionRepresentationCertificate.side_pos",
    "YangMills.RG.CMP89NeumannReflectionRepresentationCertificate.summable",
    "YangMills.RG.CMP89NeumannReflectionRepresentationCertificate.representation",
    "YangMills.RG.CMP89NeumannReflectionRepresentationCertificate.carrier_nonempty",
    "YangMills.RG.CMP89NeumannReflectionRepresentationCertificate.eq_series",
]

PHYSICAL_AXIOMS = [
    "YangMills.RG.CMP89FullLatticeGreenDecayCertificate",
    "YangMills.RG.summable_cmp89NeumannRectangularBranchFullGreen",
    "YangMills.RG.summable_cmp89NeumannRectangularFullGreen_sum",
    "YangMills.RG.norm_cmp89NeumannReflectionSeries_le_of_fullGreenDecay",
    "YangMills.RG.cmp89Eq248PhysicalFullLatticeGreen",
    "YangMills.RG.cmp89Eq248PhysicalFullLatticeGreenDecayCertificate_draft",
    "YangMills.RG.norm_cmp89Eq248PhysicalNeumannReflectionSeries_le_draft",
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


def run(stage: str, command: list[str], *, cwd: Path = ROOT) -> str:
    print("STAGE=" + stage + " CMD=" + json.dumps(command), flush=True)
    EVIDENCE.mkdir(parents=True, exist_ok=True)
    output_path = EVIDENCE / f"{len(RECORDS):03d}-{stage}.stdout"
    started = time.perf_counter()
    with output_path.open("w", encoding="utf-8", newline="\n") as stream:
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
    output = output_path.read_text(encoding="utf-8")
    jobs = None
    matches = re.findall(r"Build completed successfully \((\d+) jobs\)", output)
    if matches:
        jobs = int(matches[-1])
    RECORDS.append({
        "stage": stage,
        "exit": exit_code,
        "seconds": elapsed,
        "jobs": jobs,
        "output_sha256": sha256(output_path),
    })
    print("\n".join(output.splitlines()[-80:]), flush=True)
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
            + json.dumps({"found": sorted(found), "expected": sorted(expected)})
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


def make_evidence(status: str, opened: str) -> tuple[str, str, str]:
    payload = {
        "runner_rev": RUNNER_REV,
        "source_sha": SOURCE_SHA,
        "same_checkout_cold_origin": True,
        "restored_project_build": False,
        "status": status,
        "opened_utc": opened,
        "closed_utc": utc_now(),
        "source_blobs": SOURCE_BLOBS,
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
    print("STAGE=supplement_open UTC=" + opened, flush=True)
    try:
        for path in (EVIDENCE, ARCHIVE):
            if path.exists():
                raise RuntimeError("FRESH_SUPPLEMENT_PATH_ALREADY_EXISTS=" + str(path))
        EVIDENCE.mkdir(parents=True)
        if not ROOT.is_dir():
            raise RuntimeError("COLD_CHECKOUT_MISSING")
        if not (BINDIR / "lake").is_file():
            raise RuntimeError("VERIFIED_TOOLCHAIN_MISSING")
        os.environ["PATH"] = str(BINDIR) + os.pathsep + os.environ["PATH"]
        head = run("head", ["git", "rev-parse", "HEAD"]).strip()
        if head != SOURCE_SHA:
            raise RuntimeError("HEAD_MISMATCH=" + head)
        if (ROOT / "lean-toolchain").read_text(encoding="utf-8").strip() != EXPECTED_TOOLCHAIN:
            raise RuntimeError("LEAN_TOOLCHAIN_FILE_MISMATCH")
        mathlib = run(
            "mathlib_pin",
            ["git", "-C", ".lake/packages/mathlib", "rev-parse", "HEAD"],
        ).strip()
        if mathlib != EXPECTED_MATHLIB:
            raise RuntimeError("MATHLIB_PIN_MISMATCH=" + mathlib)
        for relative, expected in SOURCE_BLOBS.items():
            actual = sha256(ROOT / relative)
            print(f"SOURCE_BLOB={relative} SHA256={actual}", flush=True)
            if actual != expected:
                raise RuntimeError("SOURCE_BLOB_HASH_MISMATCH=" + relative)

        run(
            "representation_focal",
            ["lake", "build", "YangMills.RG.BalabanCMP89NeumannReflectionRepresentation"],
        )
        representation_audit = run(
            "representation_audit",
            [
                "lake", "env", "lean",
                "YangMills/RG/BalabanCMP89NeumannReflectionRepresentationAudit.lean",
            ],
        )
        parse_axioms_exact(representation_audit, REPRESENTATION_AXIOMS)
        run(
            "physical_green_focal",
            [
                "lake", "build",
                "YangMills.RG.BalabanCMP89NeumannRectangularPhysicalGreenInsertion",
            ],
        )
        physical_audit = run(
            "physical_green_audit",
            [
                "lake", "env", "lean",
                "YangMills/RG/BalabanCMP89NeumannRectangularPhysicalGreenInsertionAudit.lean",
            ],
        )
        parse_axioms_exact(physical_audit, PHYSICAL_AXIOMS)
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
