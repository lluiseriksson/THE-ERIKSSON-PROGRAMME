#!/usr/bin/env python3
"""Run the three bounded C6d warm diagnostics after the cold gate.

The retained checkout is never moved. Each diagnostic runner is read from an
exact Git commit, checked against its recorded SHA-256, materialized outside
the checkout and executed once. The sequence stops at the first nonzero exit.
Warm success is diagnostic only and cannot retire PRE-VALIDATION notices.
"""

from __future__ import annotations

import argparse
import hashlib
from pathlib import Path
import subprocess
import sys
import time


RUNNERS = (
    (
        "54af203d0ab38f8481d3386800c21e37adaf4702",
        "tmp/debug_c6d_source_terminal_coercivity_retained_runtime.py",
        "03AE6A1D2F7678AFA572AEF75D41B997AE55CDC76724865CCD708A42AF94ADD5",
        "source_terminal_coercivity",
    ),
    (
        "a88a2e7aa5f636da4060b7b50724f69c92a8b53c",
        "tmp/debug_poincare_positive_radius_retained_runtime.py",
        "B354FCD0620491EE2139FFB7EBBB8AB4072237A846E43AC9B2F78D0E32098F92",
        "poincare_positive_radius",
    ),
    (
        "c093920bb12c925bf77be80479f082ec2e493955",
        "tmp/debug_c6d_source_terminal_coercivity_reachability_retained_runtime.py",
        "F9AB738775178A1ECD4DB53C363A541F6B4F5FF547CCD504813FF13C0FE43D1C",
        "source_terminal_coercivity_reachability",
    ),
)


def run(
    cwd: Path, *cmd: str, capture: bool = True
) -> subprocess.CompletedProcess[bytes]:
    return subprocess.run(
        list(cmd),
        cwd=cwd,
        check=False,
        stdout=subprocess.PIPE if capture else None,
        stderr=subprocess.STDOUT if capture else None,
    )


def git(repo: Path, *args: str) -> bytes:
    child = run(repo, "git", "-c", "safe.directory=*", *args)
    if child.returncode != 0:
        raise RuntimeError(
            "C6D_POST_COLD_GIT_FAIL=" + " ".join(args) + ":"
            + child.stdout.decode(errors="replace")
        )
    return child.stdout


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo", type=Path, required=True)
    parser.add_argument(
        "--scratch-dir", type=Path, default=Path("/content/c6d-post-cold-runners")
    )
    args = parser.parse_args()
    repo = args.repo.resolve()
    scratch = args.scratch_dir.resolve()
    scratch.mkdir(parents=True, exist_ok=True)

    original_head = git(repo, "rev-parse", "HEAD").decode().strip()
    print(f"POST_COLD_ORIGINAL_HEAD={original_head}", flush=True)

    for index, (source_sha, relative, expected_sha256, label) in enumerate(
        RUNNERS, start=1
    ):
        git(repo, "fetch", "--no-tags", "origin", source_sha)
        resolved = git(repo, "rev-parse", f"{source_sha}^{{commit}}").decode().strip()
        if resolved != source_sha:
            raise RuntimeError(f"C6D_POST_COLD_SOURCE_MISMATCH={label}")
        data = git(repo, "cat-file", "blob", f"{source_sha}:{relative}")
        actual_sha256 = hashlib.sha256(data).hexdigest().upper()
        if actual_sha256 != expected_sha256:
            raise RuntimeError(
                f"C6D_POST_COLD_RUNNER_HASH_MISMATCH={label}:"
                f"{actual_sha256}:WANT={expected_sha256}"
            )
        target = scratch / f"{index:02d}-{Path(relative).name}"
        target.write_bytes(data)
        print(
            f"POST_COLD_RUNNER={label} SOURCE_SHA={source_sha} "
            f"SHA256={actual_sha256}",
            flush=True,
        )
        started = time.perf_counter()
        child = run(
            repo,
            sys.executable,
            str(target),
            "--repo",
            str(repo),
            "--source-sha",
            source_sha,
        )
        output = child.stdout.decode(errors="replace")
        print(output, end="", flush=True)
        print(
            f"POST_COLD_STAGE={label} EXIT={child.returncode} "
            f"SECONDS={time.perf_counter() - started:.3f}",
            flush=True,
        )
        if child.returncode != 0:
            print(f"POST_COLD_FIRST_ERROR={label}", flush=True)
            print("POST_COLD_FINAL_STATUS=FAIL", flush=True)
            return child.returncode

    final_head = git(repo, "rev-parse", "HEAD").decode().strip()
    if final_head != original_head:
        raise RuntimeError(
            f"C6D_POST_COLD_HEAD_MOVED={original_head}:NOW={final_head}"
        )
    print("POST_COLD_FINAL_STATUS=PASS", flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
