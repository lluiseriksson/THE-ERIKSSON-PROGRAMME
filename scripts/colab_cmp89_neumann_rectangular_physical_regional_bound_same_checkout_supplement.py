#!/usr/bin/env python3
"""Fail-closed same-checkout supplement for the CMP89 regional bound gate.

The fresh cold runner completed its 8612-job focal and exact audit.  A Colab
editor/cache incident then re-executed the old runner while the editor showed
the download cell and overwrote the archive with an instrumentation FAIL.
This supplement re-verifies that same cold-origin checkout and reruns the
focal plus exact audit incrementally.  No project build is restored.
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


RUNNER_REV = "cmp89-neumann-physical-regional-bound-same-checkout-supplement-v1"
SOURCE_SHA = "466b9de31df1fd65ec86092908746a250edb5b4b"
EXPECTED_MATHLIB = "07642720480157414db592fa85b626dafb71355b"
EXPECTED_TOOLCHAIN = "leanprover/lean4:v4.29.0-rc6"
ROOT = Path("/content/hrpoly-cmp89-regional-bound-cold-466b9de3")
INITIAL = Path("/content/hrpoly-cmp89-regional-bound-cold-466b9de3-evidence")
TOOLROOT = Path("/content/lean-4.29.0-rc6-linux")
BINDIR = TOOLROOT / "lean-4.29.0-rc6-linux" / "bin"
EVIDENCE = Path(
    "/content/hrpoly-cmp89-regional-bound-cold-466b9de3-same-checkout-supplement"
)
ARCHIVE = Path(str(EVIDENCE) + ".tar.gz")

SOURCE_BLOBS = {
    "YangMills/RG/BalabanCMP89NeumannRectangularPhysicalRegionalBound.lean":
        "2da99f5e073ae26a2a131a1650873f47423bc97f6a1f157ffdb6d37a90d7825e",
    "YangMills/RG/BalabanCMP89NeumannRectangularPhysicalRegionalBoundAudit.lean":
        "99cd14ffb61d1984f97e1ae7598a4ac5cd0dc259f1ab49505f7800746427e2fe",
    "YangMillsCore.lean":
        "bdd45bb43b0a01795042149a9934b3782b25054cb5715465b61e8d978e11ea71",
}
TARGET_AXIOMS = [
    "YangMills.RG.norm_cmp89Eq248PhysicalRegionalGreen_le_of_representation_draft",
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


def run(stage: str, command: list[str]) -> str:
    print("STAGE=" + stage + " CMD=" + json.dumps(command), flush=True)
    output_path = EVIDENCE / f"{len(RECORDS):03d}-{stage}.stdout"
    started = time.perf_counter()
    with output_path.open("w", encoding="utf-8", newline="\n") as stream:
        child = subprocess.Popen(
            command,
            cwd=ROOT,
            env=os.environ.copy(),
            text=True,
            stdout=stream,
            stderr=subprocess.STDOUT,
        )
        while True:
            try:
                exit_code = child.wait(timeout=1)
                break
            except subprocess.TimeoutExpired:
                pass
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


def parse_axioms_exact(output: str) -> None:
    compact = re.sub(r"\s+", "", output)
    for forbidden in ("sorryAx", "ofReduceBool"):
        if forbidden in compact:
            raise RuntimeError("FORBIDDEN_AXIOM=" + forbidden)
    blocks = re.findall(r"'([^']+)'dependsonaxioms:\[([^\]]*)\]", compact)
    found = {name: body for name, body in blocks}
    if set(found) != set(TARGET_AXIOMS):
        raise RuntimeError(
            "AXIOM_DECLARATIONS_MISMATCH="
            + json.dumps({"found": sorted(found), "expected": TARGET_AXIOMS})
        )
    for name in TARGET_AXIOMS:
        axioms = {item for item in found[name].split(",") if item}
        if not axioms.issubset(ALLOWED_AXIOMS):
            raise RuntimeError("AXIOM_SET=" + name + ":" + json.dumps(sorted(axioms)))
        print("AXIOM_GATE=" + name + " AXIOMS=" + ",".join(sorted(axioms)), flush=True)


def make_evidence(status: str, opened: str) -> tuple[str, str, str]:
    payload = {
        "runner_rev": RUNNER_REV,
        "source_sha": SOURCE_SHA,
        "same_checkout_cold_origin": True,
        "restored_project_build": False,
        "instrumentation_incident":
            "displayed download cell re-executed old runner and overwrote initial archive",
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
            "mathlib_pin", ["git", "-C", ".lake/packages/mathlib", "rev-parse", "HEAD"]
        ).strip()
        if mathlib != EXPECTED_MATHLIB:
            raise RuntimeError("MATHLIB_PIN_MISMATCH=" + mathlib)
        for relative, expected in SOURCE_BLOBS.items():
            actual = sha256(ROOT / relative)
            print(f"SOURCE_BLOB={relative} SHA256={actual}", flush=True)
            if actual != expected:
                raise RuntimeError("SOURCE_BLOB_HASH_MISMATCH=" + relative)

        # Preserve the original successful cold logs even though its summary
        # files were overwritten by the instrumentation incident.
        if INITIAL.is_dir():
            for source in sorted(INITIAL.glob("*.stdout")):
                if source.name.endswith(("-focal.stdout", "-audit.stdout")):
                    shutil.copy2(source, EVIDENCE / ("initial-cold-" + source.name))

        run(
            "regional_focal",
            ["lake", "build", "YangMills.RG.BalabanCMP89NeumannRectangularPhysicalRegionalBound"],
        )
        audit = run(
            "regional_audit",
            [
                "lake", "env", "lean",
                "YangMills/RG/BalabanCMP89NeumannRectangularPhysicalRegionalBoundAudit.lean",
            ],
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
