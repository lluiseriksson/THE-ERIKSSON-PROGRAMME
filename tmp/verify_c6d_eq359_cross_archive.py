#!/usr/bin/env python3
"""Verify C6d evidence obtained from the byte-identical Eq359 cold root.

The verifier composes two independent artifacts:

* the ordinary Eq359 cold archive, whose existing verifier proves the exact
  fresh checkout and successful ``YangMillsCore`` root; and
* the warm cross-postpass archive, which proves all ninety-two C6d axiom
  readouts on the retained checkout.

It additionally checks from canonical Git blobs that all thirty-four C6d
source/audit files are byte-identical at both source checkpoints.  It neither
runs Lean nor edits the repository.
"""

from __future__ import annotations

from collections import defaultdict
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import tarfile
import tempfile


ROOT = Path(__file__).resolve().parents[1]
EQ359_VERIFIER = ROOT / "tmp" / "verify_eq359_real_slice_archive.py"
EQ359_SOURCE_SHA = "cd6ff65638f0e09e2533733df2d7176c10714a3a"
EQ359_RUNNER_REV = "eq359-real-slice-promoted-cold-v4"
C6D_SOURCE_SHA = "3738ddb64155a2d85f6d3609d05d5b71114ca498"
CROSS_RUNNER_REV = "c6d-eq359-cross-postpass-v1"
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


def git_blob(repo: Path, commit: str, relative: str) -> bytes:
    child = subprocess.run(
        ["git", "-c", "safe.directory=*", "show", f"{commit}:{relative}"],
        cwd=repo,
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    if child.returncode != 0:
        raise RuntimeError(
            "C6D_CROSS_VERIFY_GIT_BLOB_FAILED="
            + relative
            + "/"
            + child.stderr.decode(errors="replace")
        )
    return child.stdout


def safe_members(path: Path) -> tuple[str, dict[str, tarfile.TarInfo]]:
    with tarfile.open(path, "r:gz") as archive:
        members = [member for member in archive.getmembers() if member.isfile()]
    names = [member.name for member in members]
    if any(name.startswith("/") or ".." in Path(name).parts for name in names):
        raise RuntimeError("C6D_CROSS_VERIFY_UNSAFE_ARCHIVE_MEMBER")
    roots = {Path(name).parts[0] for name in names}
    if len(roots) != 1:
        raise RuntimeError("C6D_CROSS_VERIFY_ARCHIVE_ROOT_SCOPE")
    return next(iter(roots)), {member.name: member for member in members}


def read_member(path: Path, member: tarfile.TarInfo) -> bytes:
    with tarfile.open(path, "r:gz") as archive:
        stream = archive.extractfile(member)
        if stream is None:
            raise RuntimeError("C6D_CROSS_VERIFY_ARCHIVE_READ_FAILED")
        return stream.read()


def parse_axioms(body: str) -> frozenset[str]:
    return frozenset(name for name in re.split(r"\s*,\s*", body.strip()) if name)


def verify_eq359(repo: Path, archive: Path) -> tuple[dict, str, str]:
    with tempfile.TemporaryDirectory(prefix="eq359-c6d-cross-") as temp:
        output = Path(temp) / "eq359.json"
        child = subprocess.run(
            [
                sys.executable,
                str(EQ359_VERIFIER),
                "--repo",
                str(repo),
                "--archive",
                str(archive),
                "--source-sha",
                EQ359_SOURCE_SHA,
                "--runner-rev",
                EQ359_RUNNER_REV,
                "--json-out",
                str(output),
            ],
            cwd=repo,
            check=False,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
        )
        if child.returncode != 0:
            raise RuntimeError("C6D_CROSS_EQ359_VERIFIER_FAILED=" + child.stdout)
        result = json.loads(output.read_text(encoding="utf-8"))
    if result.get("status") != "EQ359_REAL_SLICE_EVIDENCE_OK":
        raise RuntimeError("C6D_CROSS_EQ359_VERIFIER_STATUS")

    root, files = safe_members(archive)
    evidence_name = f"{root}/evidence.json"
    if evidence_name not in files:
        raise RuntimeError("C6D_CROSS_EQ359_EVIDENCE_MEMBER_MISSING")
    evidence_raw = read_member(archive, files[evidence_name])
    evidence = json.loads(evidence_raw.decode("utf-8"))
    roots = [
        record
        for record in evidence.get("records", [])
        if record.get("stage") == "eq359_real_slice_root"
    ]
    if len(roots) != 1 or roots[0].get("exit") != 0:
        raise RuntimeError("C6D_CROSS_EQ359_ROOT_RECORD")
    return roots[0], sha256(evidence_raw), sha256(archive.read_bytes())


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo", type=Path, default=ROOT)
    parser.add_argument("--eq359-archive", type=Path, required=True)
    parser.add_argument("--cross-archive", type=Path, required=True)
    parser.add_argument("--json-out", type=Path)
    args = parser.parse_args()
    repo = args.repo.resolve()
    eq359_archive = args.eq359_archive.resolve()
    cross_archive = args.cross_archive.resolve()
    if not eq359_archive.is_file() or not cross_archive.is_file():
        raise RuntimeError("C6D_CROSS_VERIFY_ARCHIVE_MISSING")

    root_record, eq359_evidence_hash, eq359_archive_hash = verify_eq359(
        repo, eq359_archive
    )
    root, files = safe_members(cross_archive)
    evidence_name = f"{root}/evidence.json"
    if evidence_name not in files:
        raise RuntimeError("C6D_CROSS_VERIFY_EVIDENCE_MISSING")
    evidence_raw = read_member(cross_archive, files[evidence_name])
    evidence = json.loads(evidence_raw.decode("utf-8"))
    required = {
        "status": "PASS",
        "runner_rev": CROSS_RUNNER_REV,
        "eq359_source_sha": EQ359_SOURCE_SHA,
        "c6d_source_sha": C6D_SOURCE_SHA,
        "expected_declarations": 92,
        "eq359_evidence_sha256": eq359_evidence_hash,
    }
    for key, wanted in required.items():
        if evidence.get(key) != wanted:
            raise RuntimeError("C6D_CROSS_VERIFY_FIELD_MISMATCH=" + key)
    if evidence.get("eq359_root_record") != root_record:
        raise RuntimeError("C6D_CROSS_VERIFY_ROOT_RECORD_MISMATCH")
    if set(evidence.get("allowed_axioms", [])) != ALLOWED:
        raise RuntimeError("C6D_CROSS_VERIFY_ALLOWED_AXIOMS")

    base_manifest = git_blob(repo, C6D_SOURCE_SHA, MANIFEST)
    eq359_manifest = git_blob(repo, EQ359_SOURCE_SHA, MANIFEST)
    if base_manifest != eq359_manifest:
        raise RuntimeError("C6D_CROSS_VERIFY_MANIFEST_DRIFT")
    paths = [
        line.strip()
        for line in base_manifest.decode("utf-8").splitlines()
        if line.strip() and not line.lstrip().startswith("#")
    ]
    if len(paths) != 34 or len(set(paths)) != 34:
        raise RuntimeError("C6D_CROSS_VERIFY_PATH_SCOPE")
    if evidence.get("boundary_paths") != paths:
        raise RuntimeError("C6D_CROSS_VERIFY_BOUNDARY_ORDER")

    boundary_hashes: dict[str, str] = {}
    declarations: dict[str, list[str]] = {}
    for relative in paths:
        base = git_blob(repo, C6D_SOURCE_SHA, relative)
        current = git_blob(repo, EQ359_SOURCE_SHA, relative)
        if base != current:
            raise RuntimeError("C6D_CROSS_VERIFY_BOUNDARY_DRIFT=" + relative)
        text = base.decode("utf-8")
        if text.count(PRE_MARKER) != 1:
            raise RuntimeError("C6D_CROSS_VERIFY_PRE_MARKER=" + relative)
        boundary_hashes[relative] = sha256(base)
        if relative.endswith("Audit.lean"):
            declarations[relative] = PRINT_RE.findall(text)
    if evidence.get("boundary_blob_sha256") != boundary_hashes:
        raise RuntimeError("C6D_CROSS_VERIFY_BOUNDARY_HASHES")
    if evidence.get("declarations_by_audit") != declarations:
        raise RuntimeError("C6D_CROSS_VERIFY_DECLARATION_MAP")
    expected = [name for names in declarations.values() for name in names]
    if len(declarations) != 17 or len(expected) != 92 or len(set(expected)) != 92:
        raise RuntimeError("C6D_CROSS_VERIFY_DECLARATION_SCOPE")

    records = evidence.get("records")
    if not isinstance(records, list) or len(records) != 17:
        raise RuntimeError("C6D_CROSS_VERIFY_RECORD_SCOPE")
    outputs: list[str] = []
    expected_members = {evidence_name}
    observed: dict[str, list[frozenset[str]]] = defaultdict(list)
    for record in records:
        stage = record.get("stage")
        relative = record.get("path")
        if not isinstance(stage, str) or relative not in declarations:
            raise RuntimeError("C6D_CROSS_VERIFY_RECORD_INVALID")
        if record.get("exit") != 0:
            raise RuntimeError("C6D_CROSS_VERIFY_STAGE_EXIT=" + stage)
        member_name = f"{root}/{stage}.stdout"
        expected_members.add(member_name)
        if member_name not in files:
            raise RuntimeError("C6D_CROSS_VERIFY_STDOUT_MISSING=" + stage)
        output_raw = read_member(cross_archive, files[member_name])
        if sha256(output_raw) != record.get("output_sha256"):
            raise RuntimeError("C6D_CROSS_VERIFY_STDOUT_HASH=" + stage)
        output = output_raw.decode("utf-8")
        outputs.append(output)
        compact = re.sub(r"\s+", "", output)
        for forbidden in FORBIDDEN:
            if forbidden in compact:
                raise RuntimeError("C6D_CROSS_VERIFY_FORBIDDEN=" + forbidden)
        stage_observed: dict[str, list[frozenset[str]]] = defaultdict(list)
        for name, body in OUTPUT_RE.findall(output):
            stage_observed[name].append(parse_axioms(body))
        for name in NO_AXIOM_RE.findall(output):
            stage_observed[name].append(frozenset())
        if set(stage_observed) != set(declarations[relative]):
            raise RuntimeError("C6D_CROSS_VERIFY_STAGE_SCOPE=" + stage)
        for name, blocks in stage_observed.items():
            if len(blocks) != 1 or not blocks[0].issubset(ALLOWED):
                raise RuntimeError("C6D_CROSS_VERIFY_AXIOMS=" + name)
            observed[name].extend(blocks)
    if set(files) != expected_members:
        raise RuntimeError("C6D_CROSS_VERIFY_MEMBER_SCOPE")
    if set(observed) != set(expected) or any(len(observed[name]) != 1 for name in expected):
        raise RuntimeError("C6D_CROSS_VERIFY_OBSERVED_SCOPE")

    result = {
        "status": "C6D_EQ359_CROSS_EVIDENCE_OK",
        "c6d_source_sha": C6D_SOURCE_SHA,
        "eq359_source_sha": EQ359_SOURCE_SHA,
        "cross_runner_revision": CROSS_RUNNER_REV,
        "boundary_paths": paths,
        "boundary_blob_sha256": boundary_hashes,
        "expected_declarations": 92,
        "allowed_axioms": sorted(ALLOWED),
        "eq359_root_record": root_record,
        "eq359_archive_sha256": eq359_archive_hash,
        "cross_archive_sha256": sha256(cross_archive.read_bytes()),
        "cross_evidence_sha256": sha256(evidence_raw),
        "transport": "eq359-cold-root-plus-retained-runtime-c6d-axioms",
    }
    rendered = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.json_out is not None:
        args.json_out.write_text(rendered, encoding="utf-8", newline="\n")
    print(rendered, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
