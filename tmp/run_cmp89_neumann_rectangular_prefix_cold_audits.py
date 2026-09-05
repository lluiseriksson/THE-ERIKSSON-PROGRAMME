#!/usr/bin/env python3
"""Run the four omitted CMP89 rectangular-prefix audits fail closed.

The representative cold runner compiles these sources transitively but audits
only the final representative.  This companion is intended for that same
fresh checkout after the focal runner has passed.  It never edits the clone.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import tarfile
import time


ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
BLACKLIST = ("sorryAx", "ofReduceBool", "Lean.ofReduceBool")
AUDITS = (
    ("BalabanCMP89NeumannReflectionBranchSumAudit.lean", 2),
    ("BalabanCMP89NeumannReflectionOrbitAlgebraAudit.lean", 9),
    ("BalabanCMP89NeumannReflectionScaleDictionaryAudit.lean", 9),
    ("BalabanCMP89NeumannReflectionResidueDictionaryAudit.lean", 8),
)


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def parse_axioms(output: str, expected: int) -> list[list[str]]:
    if any(token in output for token in BLACKLIST):
        raise RuntimeError("AXIOM_BLACKLIST_HIT")
    compact = re.sub(r"\s+", "", output)
    blocks = re.findall(r"dependsonaxioms:\[([^\]]*)\]", compact)
    pure = len(re.findall(r"doesnotdependonanyaxioms", compact))
    if len(blocks) + pure != expected:
        raise RuntimeError(
            f"AXIOM_READOUT_COUNT expected={expected} "
            f"actual={len(blocks) + pure}"
        )
    parsed: list[list[str]] = []
    for block in blocks:
        names = [name for name in block.split(",") if name]
        extras = set(names) - ALLOWED
        if extras:
            raise RuntimeError("AXIOM_OUTSIDE_ALLOWED=" + ",".join(sorted(extras)))
        parsed.append(names)
    parsed.extend([] for _ in range(pure))
    return parsed


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", type=Path, required=True)
    parser.add_argument("--evidence", type=Path, required=True)
    parser.add_argument("--source-sha", required=True)
    args = parser.parse_args()

    root = args.root.resolve()
    evidence = args.evidence.resolve()
    evidence.mkdir(parents=True, exist_ok=True)
    measured_sha = subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=root, text=True
    ).strip()
    if measured_sha != args.source_sha:
        raise RuntimeError(
            f"SOURCE_SHA_MISMATCH expected={args.source_sha} actual={measured_sha}"
        )

    records = []
    for index, (name, expected) in enumerate(AUDITS, start=1):
        relative = Path("YangMills/RG") / name
        output_path = evidence / f"{index:02d}-{name}.stdout"
        started = time.perf_counter()
        child = subprocess.run(
            ["lake", "env", "lean", relative.as_posix()],
            cwd=root,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
        )
        elapsed = time.perf_counter() - started
        output_path.write_text(child.stdout, encoding="utf-8", newline="\n")
        print(child.stdout, flush=True)
        print(
            f"STAGE={name} EXIT={child.returncode} SECONDS={elapsed:.3f}",
            flush=True,
        )
        if child.returncode != 0:
            raise RuntimeError("FIRST_ERROR=" + name)
        parsed = parse_axioms(child.stdout, expected)
        records.append(
            {
                "stage": name,
                "exit": child.returncode,
                "seconds": elapsed,
                "expected_readouts": expected,
                "axioms": parsed,
                "stdout_sha256": sha256(output_path),
            }
        )

    payload = {
        "status": "PASS",
        "source_sha": measured_sha,
        "allowed_axioms": sorted(ALLOWED),
        "records": records,
    }
    evidence_json = evidence / "evidence.json"
    evidence_json.write_text(
        json.dumps(payload, sort_keys=True, indent=2) + "\n",
        encoding="utf-8",
        newline="\n",
    )
    archive = evidence.with_suffix(".tar.gz")
    if archive.exists():
        archive.unlink()
    with tarfile.open(archive, "w:gz") as stream:
        stream.add(evidence, arcname=evidence.name)
    print("EVIDENCE_JSON_SHA256=" + sha256(evidence_json), flush=True)
    print("EVIDENCE_ARCHIVE=" + str(archive), flush=True)
    print("EVIDENCE_ARCHIVE_SHA256=" + sha256(archive), flush=True)
    print("CMP89_NEUMANN_RECTANGULAR_PREFIX_EXTRA_AUDITS_OK", flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
