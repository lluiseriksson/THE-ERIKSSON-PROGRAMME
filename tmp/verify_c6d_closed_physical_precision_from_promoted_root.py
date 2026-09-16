#!/usr/bin/env python3
"""Verify the closed physical Eq. (3.60) pair from the promoted-prefix root.

The promoted-prefix archive already proves a cold checkout at one immutable
source SHA and a successful ``YangMillsCore`` build.  Since the root imports
the closed physical precision audit, its stdout also contains that audit's
axiom declarations.  This verifier makes that transitive evidence explicit;
it neither reinterprets a warm diagnostic nor widens the promoted focal gate.
"""

from __future__ import annotations

import argparse
from collections import defaultdict
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import tarfile
import tempfile


ROOT = Path(__file__).resolve().parents[1]
PROMOTED_VERIFIER = ROOT / "tmp" / "verify_c6d_promoted_precision_prefix_archive.py"
SOURCE_PATH = "YangMills/RG/BalabanCMP99Eq360ComplexClosedPhysicalPrecision.lean"
AUDIT_PATH = "YangMills/RG/BalabanCMP99Eq360ComplexClosedPhysicalPrecisionAudit.lean"
CORE_PATH = "YangMillsCore.lean"
ROOT_STAGE = "c6d_promoted_precision_prefix_root"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
FORBIDDEN = {"sorryAx", "ofReduceBool"}
PRINT_RE = re.compile(r"^#print\s+axioms\s+(.+?)\s*$", re.MULTILINE)
OUTPUT_RE = re.compile(
    r"'([^']+)'\s+depends\s+on\s+axioms:\s*\[([^\]]*)\]",
    re.MULTILINE,
)
NO_AXIOM_RE = re.compile(
    r"'([^']+)'\s+does\s+not\s+depend\s+on\s+any\s+axioms",
    re.MULTILINE,
)


def git_blob(repo: Path, source_sha: str, relative: str) -> bytes:
    child = subprocess.run(
        ["git", "-c", "safe.directory=*", "cat-file", "blob", f"{source_sha}:{relative}"],
        cwd=repo,
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    if child.returncode != 0:
        raise RuntimeError(
            f"C6D_CLOSED_PHYSICAL_GIT_BLOB_FAILED={relative}:"
            + child.stderr.decode(errors="replace")
        )
    return child.stdout


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def parse_axioms(body: str) -> frozenset[str]:
    return frozenset(name for name in re.split(r"\s*,\s*", body.strip()) if name)


def verify_promoted(
    repo: Path, archive: Path, source_sha: str, runner_rev: str
) -> dict:
    with tempfile.TemporaryDirectory(prefix="c6d-closed-physical-root-") as temp:
        output = Path(temp) / "promoted.json"
        child = subprocess.run(
            [
                sys.executable,
                str(PROMOTED_VERIFIER),
                "--repo",
                str(repo),
                "--archive",
                str(archive),
                "--source-sha",
                source_sha,
                "--runner-rev",
                runner_rev,
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
            raise RuntimeError("C6D_CLOSED_PHYSICAL_PROMOTED_VERIFY_FAILED=" + child.stdout)
        return json.loads(output.read_text(encoding="utf-8"))


def root_stdout(archive: Path) -> str:
    suffix = "/" + ROOT_STAGE + ".stdout"
    with tarfile.open(archive, "r:gz") as tar:
        matches = [member for member in tar.getmembers() if member.name.endswith(suffix)]
        if len(matches) != 1 or not matches[0].isfile():
            raise RuntimeError("C6D_CLOSED_PHYSICAL_ROOT_STDOUT_SCOPE")
        stream = tar.extractfile(matches[0])
        if stream is None:
            raise RuntimeError("C6D_CLOSED_PHYSICAL_ROOT_STDOUT_MISSING")
        return stream.read().decode("utf-8")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo", type=Path, default=ROOT)
    parser.add_argument("--archive", type=Path, required=True)
    parser.add_argument("--source-sha", required=True)
    parser.add_argument("--runner-rev", required=True)
    parser.add_argument("--json-out", type=Path)
    args = parser.parse_args()

    repo = args.repo.resolve()
    archive = args.archive.resolve()
    if re.fullmatch(r"[0-9a-f]{40}", args.source_sha) is None:
        raise RuntimeError("C6D_CLOSED_PHYSICAL_SOURCE_SHA_INVALID")
    promoted = verify_promoted(repo, archive, args.source_sha, args.runner_rev)
    if promoted.get("status") != "C6D_NEXT_REAL_SLICE_EVIDENCE_OK":
        raise RuntimeError("C6D_CLOSED_PHYSICAL_PROMOTED_STATUS")

    source_blob = git_blob(repo, args.source_sha, SOURCE_PATH)
    audit_blob = git_blob(repo, args.source_sha, AUDIT_PATH)
    core_blob = git_blob(repo, args.source_sha, CORE_PATH)
    expected_import = (
        b"import YangMills.RG.BalabanCMP99Eq360ComplexClosedPhysicalPrecisionAudit\n"
    )
    if core_blob.count(expected_import) != 1:
        raise RuntimeError("C6D_CLOSED_PHYSICAL_CORE_IMPORT")
    declarations = PRINT_RE.findall(audit_blob.decode("utf-8"))
    if len(declarations) != 14 or len(set(declarations)) != 14:
        raise RuntimeError("C6D_CLOSED_PHYSICAL_DECLARATION_SCOPE")

    output = root_stdout(archive)
    compact = re.sub(r"\s+", "", output)
    for forbidden in FORBIDDEN:
        if forbidden in compact:
            raise RuntimeError(f"C6D_CLOSED_PHYSICAL_FORBIDDEN_AXIOM={forbidden}")
    observed: dict[str, list[frozenset[str]]] = defaultdict(list)
    for declaration, body in OUTPUT_RE.findall(output):
        observed[declaration].append(parse_axioms(body))
    for declaration in NO_AXIOM_RE.findall(output):
        observed[declaration].append(frozenset())
    for declaration in declarations:
        blocks = observed.get(declaration, [])
        if len(blocks) != 1:
            raise RuntimeError(
                f"C6D_CLOSED_PHYSICAL_AXIOM_OUTPUT_COUNT={declaration}:{len(blocks)}"
            )
        if not blocks[0].issubset(ALLOWED):
            raise RuntimeError(
                f"C6D_CLOSED_PHYSICAL_NONSTANDARD_AXIOM={declaration}:"
                + ",".join(sorted(blocks[0]))
            )

    result = {
        "status": "C6D_CLOSED_PHYSICAL_FROM_PROMOTED_ROOT_OK",
        "source_sha": args.source_sha,
        "runner_revision": args.runner_rev,
        "expected_declarations": declarations,
        "allowed_axioms": sorted(ALLOWED),
        "boundary_blob_sha256": {
            SOURCE_PATH: sha256(source_blob),
            AUDIT_PATH: sha256(audit_blob),
        },
        "promoted_evidence_input_sha256": promoted["evidence_input_sha256"],
        "transport": "promoted-prefix-cold-root-stdout",
    }
    rendered = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.json_out is not None:
        args.json_out.write_text(rendered, encoding="utf-8", newline="\n")
    print(rendered, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
