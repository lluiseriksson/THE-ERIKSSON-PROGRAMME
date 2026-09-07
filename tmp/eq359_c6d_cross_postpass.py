#!/usr/bin/env python3
"""Reuse the cold Eq359 root to close the byte-identical C6d boundary.

This post-pass is deliberately narrower than a second cold build.  It first
requires the completed Eq359 evidence record and proves that all thirty-four
C6d source/audit blobs are byte-identical at the historical C6d checkpoint
and at the exact Eq359 source.  It then runs the seventeen audit files in the
already-built checkout and checks all ninety-two ``#print axioms`` readouts.

It does not edit source, retire PRE-VALIDATION, move 20/41, or instantiate a
TermSource.  A local verifier must still combine this archive with the Eq359
cold archive before the existing fail-closed C6d sealer may be used.
"""

from __future__ import annotations

from collections import defaultdict
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tarfile
import time


EQ359_SOURCE_SHA = "cd6ff65638f0e09e2533733df2d7176c10714a3a"
C6D_SOURCE_SHA = "3738ddb64155a2d85f6d3609d05d5b71114ca498"
RUNNER_REV = "c6d-eq359-cross-postpass-v1"
ROOT = Path("/content/hrpoly-eq359-real-slice")
EQ359_EVIDENCE = Path("/content/hrpoly-eq359-real-slice-evidence/evidence.json")
EVIDENCE = Path("/content/hrpoly-c6d-eq359-cross-evidence")
ARCHIVE = Path("/content/hrpoly-c6d-eq359-cross-evidence.tar.gz")
MANIFEST = "tmp/C6D-TRANSITIVE-PREVALIDATION-PATHS.txt"

ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
FORBIDDEN = {"sorryAx", "ofReduceBool"}
PRE_MARKER = (
    "PRE-VALIDATION: source is present in scratch only; no `.olean` has been\n"
    "materialized and no compiler or axiom-oracle verdict exists for this module."
)
PRINT_RE = re.compile(r"^#print\s+axioms\s+(.+?)\s*$", re.MULTILINE)
OUTPUT_RE = re.compile(
    r"'([^']+)'\s+depends\s+on\s+axioms:\s*\[([^\]]*)\]", re.MULTILINE
)
NO_AXIOM_RE = re.compile(
    r"'([^']+)'\s+does\s+not\s+depend\s+on\s+any\s+axioms", re.MULTILINE
)


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def git(*args: str) -> subprocess.CompletedProcess[bytes]:
    return subprocess.run(
        ["git", "-c", "safe.directory=*", *args],
        cwd=ROOT,
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )


def git_blob(commit: str, relative: str) -> bytes:
    child = git("show", f"{commit}:{relative}")
    if child.returncode != 0:
        raise RuntimeError(
            "C6D_CROSS_GIT_BLOB_FAILED="
            + relative
            + "/"
            + child.stderr.decode(errors="replace")
        )
    return child.stdout


def parse_axioms(body: str) -> frozenset[str]:
    return frozenset(name for name in re.split(r"\s*,\s*", body.strip()) if name)


def require_eq359_cold_root() -> tuple[dict, str]:
    if not EQ359_EVIDENCE.is_file():
        raise RuntimeError("C6D_CROSS_EQ359_EVIDENCE_MISSING")
    raw = EQ359_EVIDENCE.read_bytes()
    evidence = json.loads(raw.decode("utf-8"))
    if evidence.get("status") != "PASS":
        raise RuntimeError("C6D_CROSS_EQ359_STATUS_NOT_PASS")
    if evidence.get("source_sha") != EQ359_SOURCE_SHA:
        raise RuntimeError("C6D_CROSS_EQ359_SOURCE_MISMATCH")
    roots = [
        record
        for record in evidence.get("records", [])
        if record.get("stage") == "eq359_real_slice_root"
    ]
    if len(roots) != 1 or roots[0].get("exit") != 0:
        raise RuntimeError("C6D_CROSS_EQ359_ROOT_NOT_GREEN")
    return evidence, sha256(raw)


def boundary() -> tuple[list[str], dict[str, str], dict[str, list[str]]]:
    manifest_base = git_blob(C6D_SOURCE_SHA, MANIFEST)
    manifest_eq359 = git_blob(EQ359_SOURCE_SHA, MANIFEST)
    if manifest_base != manifest_eq359:
        raise RuntimeError("C6D_CROSS_MANIFEST_BLOB_DRIFT")
    paths = [
        line.strip()
        for line in manifest_eq359.decode("utf-8").splitlines()
        if line.strip() and not line.lstrip().startswith("#")
    ]
    if len(paths) != 34 or len(set(paths)) != 34:
        raise RuntimeError(f"C6D_CROSS_PATH_COUNT={len(paths)} WANT=34")

    hashes: dict[str, str] = {}
    declarations: dict[str, list[str]] = {}
    for relative in paths:
        base = git_blob(C6D_SOURCE_SHA, relative)
        current = git_blob(EQ359_SOURCE_SHA, relative)
        if base != current:
            raise RuntimeError("C6D_CROSS_BOUNDARY_BLOB_DRIFT=" + relative)
        worktree = (ROOT / relative).read_bytes()
        if worktree != current:
            raise RuntimeError("C6D_CROSS_WORKTREE_BLOB_DRIFT=" + relative)
        text = current.decode("utf-8")
        if text.count(PRE_MARKER) != 1:
            raise RuntimeError("C6D_CROSS_PRE_MARKER_COUNT=" + relative)
        hashes[relative] = sha256(current)
        if relative.endswith("Audit.lean"):
            names = PRINT_RE.findall(text)
            if not names:
                raise RuntimeError("C6D_CROSS_AUDIT_EMPTY=" + relative)
            declarations[relative] = names

    expected = [name for names in declarations.values() for name in names]
    if len(declarations) != 17:
        raise RuntimeError(f"C6D_CROSS_AUDIT_COUNT={len(declarations)} WANT=17")
    if len(expected) != 92 or len(set(expected)) != 92:
        raise RuntimeError(
            f"C6D_CROSS_DECLARATION_COUNT={len(expected)} WANT=92_UNIQUE"
        )
    return paths, hashes, declarations


def run_audits(declarations: dict[str, list[str]]) -> list[dict]:
    EVIDENCE.mkdir(parents=True, exist_ok=True)
    records: list[dict] = []
    observed: dict[str, list[frozenset[str]]] = defaultdict(list)

    for index, (relative, expected) in enumerate(sorted(declarations.items()), start=1):
        module = Path(relative).stem
        stage = f"c6d_cross_{index:02d}_{module.lower()}"
        output_path = Path(".lake/build/lib/lean/YangMills/RG") / f"{module}.olean"
        command = ["lake", "env", "lean", relative, "-o", str(output_path)]
        print("STAGE=" + stage + " CMD=" + json.dumps(command), flush=True)
        started = time.perf_counter()
        child = subprocess.run(
            command,
            cwd=ROOT,
            env=os.environ.copy(),
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
        )
        elapsed = time.perf_counter() - started
        output = child.stdout
        print(output, flush=True)
        print(
            f"STAGE={stage} EXIT={child.returncode} SECONDS={elapsed:.3f}",
            flush=True,
        )
        output_bytes = output.encode("utf-8")
        (EVIDENCE / f"{stage}.stdout").write_bytes(output_bytes)
        records.append(
            {
                "stage": stage,
                "path": relative,
                "exit": child.returncode,
                "seconds": elapsed,
                "output_sha256": sha256(output_bytes),
            }
        )
        if child.returncode != 0:
            raise RuntimeError("C6D_CROSS_FIRST_ERROR=" + stage)
        compact = re.sub(r"\s+", "", output)
        for forbidden in FORBIDDEN:
            if forbidden in compact:
                raise RuntimeError("C6D_CROSS_FORBIDDEN_AXIOM=" + forbidden)
        stage_observed: dict[str, list[frozenset[str]]] = defaultdict(list)
        for name, body in OUTPUT_RE.findall(output):
            stage_observed[name].append(parse_axioms(body))
        for name in NO_AXIOM_RE.findall(output):
            stage_observed[name].append(frozenset())
        if set(stage_observed) != set(expected):
            raise RuntimeError(
                "C6D_CROSS_STAGE_READOUT_SCOPE="
                + json.dumps(
                    {
                        "stage": stage,
                        "expected": sorted(expected),
                        "observed": sorted(stage_observed),
                    },
                    sort_keys=True,
                )
            )
        for name in expected:
            blocks = stage_observed.get(name, [])
            if len(blocks) != 1:
                raise RuntimeError(
                    f"C6D_CROSS_READOUT_COUNT={name}:{len(blocks)} WANT=1"
                )
            if not blocks[0].issubset(ALLOWED):
                raise RuntimeError(
                    "C6D_CROSS_NONSTANDARD_AXIOMS="
                    + name
                    + ":"
                    + json.dumps(sorted(blocks[0]))
                )
            observed[name].extend(blocks)

    expected_all = [name for names in declarations.values() for name in names]
    if set(observed) != set(expected_all):
        raise RuntimeError("C6D_CROSS_OBSERVED_SCOPE_MISMATCH")
    return records


def package(evidence: dict) -> str:
    evidence_bytes = (json.dumps(evidence, indent=2, sort_keys=True) + "\n").encode()
    (EVIDENCE / "evidence.json").write_bytes(evidence_bytes)
    if ARCHIVE.exists():
        ARCHIVE.unlink()
    with tarfile.open(ARCHIVE, "w:gz") as archive:
        for path in sorted(EVIDENCE.iterdir(), key=lambda item: item.name):
            archive.add(path, arcname=f"evidence/{path.name}")
    return sha256(ARCHIVE.read_bytes())


def main() -> int:
    print("RUNNER_REV=" + RUNNER_REV, flush=True)
    head = git("rev-parse", "HEAD")
    if head.returncode != 0 or head.stdout.decode().strip() != EQ359_SOURCE_SHA:
        raise RuntimeError("C6D_CROSS_HEAD_MISMATCH")
    eq359, eq359_hash = require_eq359_cold_root()
    paths, hashes, declarations = boundary()
    if EVIDENCE.exists():
        shutil.rmtree(EVIDENCE)
    records = run_audits(declarations)
    evidence = {
        "status": "PASS",
        "runner_rev": RUNNER_REV,
        "eq359_source_sha": EQ359_SOURCE_SHA,
        "c6d_source_sha": C6D_SOURCE_SHA,
        "eq359_evidence_sha256": eq359_hash,
        "eq359_root_record": next(
            record
            for record in eq359["records"]
            if record["stage"] == "eq359_real_slice_root"
        ),
        "boundary_paths": paths,
        "boundary_blob_sha256": hashes,
        "declarations_by_audit": declarations,
        "expected_declarations": 92,
        "allowed_axioms": sorted(ALLOWED),
        "records": records,
    }
    archive_hash = package(evidence)
    print("C6D_CROSS_ARCHIVE=" + str(ARCHIVE), flush=True)
    print("C6D_CROSS_ARCHIVE_SHA256=" + archive_hash, flush=True)
    print("C6D_CROSS_POSTPASS_FINAL_STATUS=PASS", flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
