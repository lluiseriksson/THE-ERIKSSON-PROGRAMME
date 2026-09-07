#!/usr/bin/env python3
"""Warm, non-sealing Colab debug for the C6d physical dictionary scratch."""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import time


DRAFTS = (
    "tmp/FinitePiLpTypedKernelReindexRectangularAlgebra.draft.lean",
    "tmp/FinitePiLpTypedKernelReindexRectangularAlgebraAudit.draft.lean",
    "tmp/BalabanCMP99Eq360C6dSourceSeparatedPhysicalBackground.draft.lean",
    "tmp/BalabanCMP99Eq360C6dSourceSeparatedPhysicalBackgroundAudit.draft.lean",
    "tmp/BalabanCMP99Eq360C6dSourceSeparatedPhysicalLaplacianDictionary.draft.lean",
    "tmp/BalabanCMP99Eq360C6dSourceSeparatedPhysicalLaplacianDictionaryAudit.draft.lean",
    "tmp/BalabanCMP99Eq360C6dSourceSeparatedPhysicalPrecisionDictionary.draft.lean",
    "tmp/BalabanCMP99Eq360C6dSourceSeparatedPhysicalPrecisionDictionaryAudit.draft.lean",
)
EXPECTED_AXIOM_HEADERS = (3, 3, 3, 1)
PRINT = re.compile(r"(?m)^#print axioms (?:YangMills\.RG\.)?([^\s]+)\s*$")


def run(command: list[str], cwd: Path) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        command,
        cwd=cwd,
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
    )


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo", type=Path, required=True)
    parser.add_argument("--source-sha", required=True)
    parser.add_argument(
        "--evidence",
        type=Path,
        default=Path("/content/c6d-physical-precision-dictionary-warm-debug"),
    )
    args = parser.parse_args()
    repo = args.repo.resolve()
    evidence = args.evidence.resolve()
    if re.fullmatch(r"[0-9a-f]{40}", args.source_sha) is None:
        raise RuntimeError("C6D_PHYSICAL_DICTIONARY_DEBUG_SOURCE_SHA_INVALID")
    if not (repo / ".git").exists():
        raise RuntimeError(f"C6D_PHYSICAL_DICTIONARY_DEBUG_REPO_INVALID={repo}")

    fetch = run(["git", "fetch", "origin", args.source_sha], repo)
    print(fetch.stdout, end="", flush=True)
    if fetch.returncode != 0:
        raise RuntimeError("C6D_PHYSICAL_DICTIONARY_DEBUG_FETCH_FAILED")
    checkout = run(["git", "checkout", "--detach", args.source_sha], repo)
    print(checkout.stdout, end="", flush=True)
    if checkout.returncode != 0:
        raise RuntimeError("C6D_PHYSICAL_DICTIONARY_DEBUG_CHECKOUT_FAILED")
    head = run(["git", "rev-parse", "HEAD"], repo)
    if head.returncode != 0 or head.stdout.strip() != args.source_sha:
        raise RuntimeError(
            f"C6D_PHYSICAL_DICTIONARY_DEBUG_HEAD={head.stdout.strip()} "
            f"EXPECTED={args.source_sha}"
        )

    promote_path = repo / "tmp" / "promote_c6d_physical_precision_dictionary.py"
    spec = importlib.util.spec_from_file_location("c6d_physical_dictionary_promotion", promote_path)
    if spec is None or spec.loader is None:
        raise RuntimeError("C6D_PHYSICAL_DICTIONARY_DEBUG_PROMOTION_IMPORT_FAILED")
    promotion = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(promotion)
    files: list[str] = []
    for draft in DRAFTS:
        target = promotion.destination(draft)
        target_path = repo / target
        tracked = run(["git", "cat-file", "-e", f"HEAD:{target}"], repo)
        if tracked.returncode == 0:
            raise RuntimeError(f"C6D_PHYSICAL_DICTIONARY_DEBUG_TARGET_TRACKED={target}")
        target_path.parent.mkdir(parents=True, exist_ok=True)
        target_path.write_bytes(promotion.promote_text((repo / draft).read_bytes()))
        files.append(target)

    evidence.mkdir(parents=True, exist_ok=True)
    records: list[dict[str, object]] = []
    for index, relative in enumerate(files):
        path = repo / relative
        if not path.is_file():
            raise RuntimeError(f"C6D_PHYSICAL_DICTIONARY_DEBUG_FILE_MISSING={relative}")
        if index % 2 == 1:
            expected = EXPECTED_AXIOM_HEADERS[index // 2]
            actual = len(PRINT.findall(path.read_text(encoding="utf-8")))
            if actual != expected:
                raise RuntimeError(
                    f"C6D_PHYSICAL_DICTIONARY_DEBUG_AXIOM_HEADERS={relative}/"
                    f"{actual} EXPECTED={expected}"
                )
        stage = f"{index + 1:02d}_{path.stem.lower()}"
        if index % 2 == 0:
            module = "YangMills.RG." + path.stem
            command = ["lake", "build", module]
        else:
            command = ["lake", "env", "lean", relative]
        print(f"STAGE={stage} CMD={command!r}", flush=True)
        started = time.perf_counter()
        child = run(command, repo)
        seconds = time.perf_counter() - started
        output_path = evidence / f"{index:03d}-{stage}.stdout"
        output_path.write_text(child.stdout, encoding="utf-8", newline="\n")
        print(child.stdout, end="", flush=True)
        record = {
            "stage": stage,
            "file": relative,
            "exit": child.returncode,
            "seconds": seconds,
            "output_sha256": sha256(output_path),
        }
        records.append(record)
        print(f"STAGE={stage} EXIT={child.returncode} SECONDS={seconds:.3f}", flush=True)
        if child.returncode != 0:
            (evidence / "debug.json").write_text(
                json.dumps(
                    {"status": "FAIL", "source_sha": args.source_sha, "records": records},
                    indent=2,
                    sort_keys=True,
                ) + "\n",
                encoding="utf-8",
                newline="\n",
            )
            print(f"FIRST_ERROR={stage}", flush=True)
            print("FINAL_STATUS=FAIL", flush=True)
            return child.returncode

    (evidence / "debug.json").write_text(
        json.dumps(
            {"status": "PASS", "source_sha": args.source_sha, "records": records},
            indent=2,
            sort_keys=True,
        ) + "\n",
        encoding="utf-8",
        newline="\n",
    )
    print(f"C6D_PHYSICAL_DICTIONARY_WARM_DEBUG_OK files={len(files)}", flush=True)
    print("FINAL_STATUS=PASS", flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
