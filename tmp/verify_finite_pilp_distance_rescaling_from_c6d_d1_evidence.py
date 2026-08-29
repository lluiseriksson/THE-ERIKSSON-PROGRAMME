#!/usr/bin/env python3
"""Verify distance rescaling from the corrected C6d-D1 cold-root evidence.

The original distance-rescaling gate proved its focal and audit, but its root
ran at an older source and failed only in two later C6d-D1 modules.  This
cross-verifier accepts no partial root: it first requires the complete
corrected D1 evidence verifier to pass, then checks byte identity of the
distance-rescaling pair and requires the corrected cold root to have built the
pair and printed its allowed axiom readout.
"""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import sys
import tarfile


ROOT = Path(__file__).resolve().parents[1]
D1_VERIFIER = ROOT / "tmp" / "verify_c6d_post_green_decay_prefix_evidence.py"
COMMON_BASE = ROOT / "tmp" / "verify_c6d_source_separated_ambient_green_evidence.py"
SOURCE_SHA = "acc5064072a1e5c42eb74735b56b9fc7b465545c"
ORIGINAL_SOURCE_SHA = "ebeea96235ac89a0a9598593855119d4bfe3ea04"
ROOT_STAGE = "03_c6d_post_green_decay_prefix_yang_mills_core_root"
D1_SENTINEL = "C6D_POST_GREEN_DECAY_PREFIX_EVIDENCE_OK"
SUCCESS_SENTINEL = "DISTANCE_RESCALING_FROM_C6D_D1_EVIDENCE_OK"
MODULE = "FinitePiLpTypedKernelDistanceRescaling"
DECLARATION = "finitePiLpTypedExponentialKernelBound_rescale_dist"
PATHS = [
    f"YangMills/RG/{MODULE}.lean",
    f"YangMills/RG/{MODULE}Audit.lean",
]


def load_common_base():
    spec = importlib.util.spec_from_file_location("distance_rescaling_cross_base", COMMON_BASE)
    if spec is None or spec.loader is None:
        raise RuntimeError("DISTANCE_RESCALING_CROSS_BASE_IMPORT_FAILED")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def git(*args: str) -> subprocess.CompletedProcess[bytes]:
    return subprocess.run(
        ["git", "-c", "safe.directory=*", *args],
        cwd=ROOT,
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )


def require_d1_verifier(archive: Path, notebook: Path) -> None:
    child = subprocess.run(
        [sys.executable, str(D1_VERIFIER), str(archive), str(notebook)],
        cwd=ROOT,
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
    )
    if child.returncode != 0:
        raise RuntimeError("C6D_D1_EVIDENCE_FAILED=\n" + child.stdout)
    if child.stdout.count(D1_SENTINEL) != 1:
        raise RuntimeError("C6D_D1_EVIDENCE_SENTINEL_COUNT_INVALID")


def require_blob_identity() -> None:
    for relative in PATHS:
        current = git("show", f"{SOURCE_SHA}:{relative}")
        original = git("show", f"{ORIGINAL_SOURCE_SHA}:{relative}")
        if current.returncode != 0 or original.returncode != 0:
            raise RuntimeError(f"DISTANCE_RESCALING_BLOB_READ_FAILED={relative}")
        if current.stdout != original.stdout:
            raise RuntimeError(f"DISTANCE_RESCALING_BLOB_CHANGED={relative}")
        if current.stdout.count(b"PRE-VALIDATION") != 1:
            raise RuntimeError(f"DISTANCE_RESCALING_PREVALIDATION_COUNT={relative}")


def root_output(archive_path: Path, base) -> tuple[str, dict[str, object]]:
    with tarfile.open(archive_path, "r:gz") as archive:
        members = base.safe_members(archive)
        evidence_members = [m for m in members if m.name.endswith("/evidence.json")]
        if len(evidence_members) != 1:
            raise RuntimeError(f"EVIDENCE_JSON_COUNT={len(evidence_members)}")
        payloads: dict[str, bytes] = {}
        for member in members:
            if member.isfile():
                extracted = archive.extractfile(member)
                if extracted is None:
                    raise RuntimeError(f"UNREADABLE_MEMBER={member.name}")
                payloads[member.name] = extracted.read()
        evidence_name = evidence_members[0].name
        payload = json.loads(payloads[evidence_name])
    if payload.get("source_sha") != SOURCE_SHA:
        raise RuntimeError(f"SOURCE_SHA={payload.get('source_sha')!r}")
    records = payload.get("records")
    if not isinstance(records, list):
        raise RuntimeError("RECORDS_NOT_LIST")
    prefix = evidence_name.rsplit("/", 1)[0]
    for index, record in enumerate(records):
        if isinstance(record, dict) and record.get("stage") == ROOT_STAGE:
            if record.get("exit") != 0:
                raise RuntimeError(f"ROOT_EXIT={record.get('exit')!r}")
            member = f"{prefix}/{index:03d}-{ROOT_STAGE}.stdout"
            raw = payloads.get(member)
            if raw is None:
                raise RuntimeError(f"ROOT_LOG_MISSING={member}")
            normalized = raw.decode("utf-8").replace("\r\n", "\n").replace("\r", "\n")
            measured = hashlib.sha256(normalized.encode()).hexdigest()
            if measured != record.get("output_sha256"):
                raise RuntimeError("ROOT_LOG_HASH_MISMATCH")
            return normalized, record
    raise RuntimeError("ROOT_STAGE_MISSING")


def require_pair_in_root(text: str) -> None:
    for module in (MODULE, MODULE + "Audit"):
        if not re.search(rf"(?:Built|Replayed) YangMills\.RG\.{re.escape(module)}(?:\s|$)", text):
            raise RuntimeError(f"ROOT_DISTANCE_RESCALING_MODULE_MISSING={module}")
    compact = re.sub(r"\s+", "", text)
    pattern = (
        re.escape("'YangMills.RG." + DECLARATION + "'dependsonaxioms:[")
        + r"([^\]]*)\]"
    )
    matches = re.findall(pattern, compact)
    if len(matches) != 1:
        raise RuntimeError(
            f"ROOT_AXIOM_READOUT_COUNT_{DECLARATION}={len(matches)} EXPECTED=1"
        )
    names = {name for name in matches[0].split(",") if name}
    if not names.issubset({"propext", "Classical.choice", "Quot.sound"}):
        raise RuntimeError(f"ROOT_FORBIDDEN_AXIOMS_{DECLARATION}={sorted(names)!r}")
    for forbidden in ("sorryAx", "ofReduceBool"):
        if forbidden in text:
            raise RuntimeError(f"ROOT_FORBIDDEN_AXIOM_TOKEN={forbidden}")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("archive", type=Path)
    parser.add_argument("notebook", type=Path)
    args = parser.parse_args()
    archive = args.archive.resolve()
    notebook = args.notebook.resolve()
    base = load_common_base()
    require_d1_verifier(archive, notebook)
    require_blob_identity()
    text, record = root_output(archive, base)
    require_pair_in_root(text)
    print(SUCCESS_SENTINEL)
    print(f"SOURCE_SHA={SOURCE_SHA}")
    print(f"ORIGINAL_SOURCE_SHA={ORIGINAL_SOURCE_SHA}")
    print(f"ROOT_SECONDS={float(record['seconds']):.3f}")
    print(f"ARCHIVE_SHA256={base.sha256(archive)}")
    print(f"NOTEBOOK_SHA256={base.sha256(notebook)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
