#!/usr/bin/env python3
"""Verify the diameter pair from the Green-v4 cold root evidence.

The Green-v4 gate runs in one fresh checkout at ``SOURCE_SHA`` and finishes
with a full ``YangMillsCore`` root.  This verifier first requires the complete
Green-v4 evidence verifier to pass, then checks that the root actually built
the terminal-block diameter pair and printed every expected axiom readout.
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
BASE_PATH = ROOT / "tmp" / "verify_c6d_source_separated_ambient_green_evidence.py"
SOURCE_SHA = "7e90203e8bfd1deb58d998fb5cdad0baab925af5"
RUNNER_REV = "c6d-source-separated-ambient-green-v4"
MODULES = ["BalabanCMP99SourceActiveRegionTerminalBlockDiameter"]
SUCCESS_SENTINEL = "C6D_TERMINAL_BLOCK_DIAMETER_FROM_GREEN_V4_EVIDENCE_OK"
GREEN_SENTINEL = "C6D_SOURCE_SEPARATED_AMBIENT_GREEN_EVIDENCE_OK"
ROOT_STAGE = "04_c6d_source_green_yang_mills_core_root"
PATHS = [
    f"YangMills/RG/{MODULES[0]}.lean",
    f"YangMills/RG/{MODULES[0]}Audit.lean",
]
DECLARATIONS = [
    "CMP99SourceActiveRegionChain.div_pow_eq_of_sameTerminalBlock",
    "CMP99SourceActiveRegionChain.sameTerminalBlock_finBoxDist_le",
    "CMP99SourceActiveRegionChain.generatedCountingMass_finiteRange_terminalBlock",
    "CMP99SourceActiveRegionChain.QprimeMass_finiteRange_terminalBlock",
]
FAILED_DIAMETER_SOURCE = "a2715bf8cdae841dfc313ea9f34a23fe1d2bdd35"


def load_base():
    spec = importlib.util.spec_from_file_location("green_v4_evidence_base", BASE_PATH)
    if spec is None or spec.loader is None:
        raise RuntimeError("GREEN_V4_EVIDENCE_BASE_IMPORT_FAILED")
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


def require_green_verifier(archive: Path, notebook: Path) -> None:
    child = subprocess.run(
        [sys.executable, str(BASE_PATH), str(archive), str(notebook)],
        cwd=ROOT,
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
    )
    if child.returncode != 0:
        raise RuntimeError("GREEN_V4_EVIDENCE_FAILED=\n" + child.stdout)
    if child.stdout.count(GREEN_SENTINEL) != 1:
        raise RuntimeError("GREEN_V4_EVIDENCE_SENTINEL_COUNT_INVALID")


def require_blob_identity() -> None:
    for relative in PATHS:
        green = git("show", f"{SOURCE_SHA}:{relative}")
        earlier = git("show", f"{FAILED_DIAMETER_SOURCE}:{relative}")
        if green.returncode != 0 or earlier.returncode != 0:
            raise RuntimeError(f"DIAMETER_BLOB_READ_FAILED={relative}")
        if green.stdout != earlier.stdout:
            raise RuntimeError(f"DIAMETER_BLOB_CHANGED={relative}")
        if green.stdout.count(b"PRE-VALIDATION") != 1:
            raise RuntimeError(f"DIAMETER_PREVALIDATION_COUNT={relative}")


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


def require_diameter_in_root(text: str) -> None:
    for module in (MODULES[0], MODULES[0] + "Audit"):
        if not re.search(rf"(?:Built|Replayed) YangMills\.RG\.{re.escape(module)}(?:\s|$)", text):
            raise RuntimeError(f"ROOT_DIAMETER_MODULE_MISSING={module}")
    compact = re.sub(r"\s+", "", text)
    for declaration in DECLARATIONS:
        pattern = (
            re.escape("'YangMills.RG." + declaration + "'dependsonaxioms:[")
            + r"([^\]]*)\]"
        )
        matches = re.findall(pattern, compact)
        if len(matches) != 1:
            raise RuntimeError(
                f"ROOT_AXIOM_READOUT_COUNT_{declaration}={len(matches)} EXPECTED=1"
            )
        names = {name for name in matches[0].split(",") if name}
        if not names.issubset({"propext", "Classical.choice", "Quot.sound"}):
            raise RuntimeError(
                f"ROOT_FORBIDDEN_AXIOMS_{declaration}={sorted(names)!r}"
            )
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
    base = load_base()
    require_green_verifier(archive, notebook)
    require_blob_identity()
    text, record = root_output(archive, base)
    require_diameter_in_root(text)
    print(SUCCESS_SENTINEL)
    print(f"SOURCE_SHA={SOURCE_SHA}")
    print(f"RUNNER_REV={RUNNER_REV}")
    print(f"ROOT_SECONDS={float(record['seconds']):.3f}")
    print(f"ARCHIVE_SHA256={base.sha256(archive)}")
    print(f"NOTEBOOK_SHA256={base.sha256(notebook)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
