#!/usr/bin/env python3
"""Generate the one-cell launcher for a pinned Eq. (3.37) Ubar-radius runner."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess


ROOT = Path(__file__).resolve().parents[1]
RUNNER_PATH = "scripts/colab_eq337_complex_ubar_radius_validation.py"
REPO_RAW = (
    "https://raw.githubusercontent.com/lluiseriksson/"
    "THE-ERIKSSON-PROGRAMME"
)


def git(*args: str, binary: bool = False) -> bytes | str:
    child = subprocess.run(
        ["git", "-c", "safe.directory=*", *args],
        cwd=ROOT,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    if child.returncode != 0:
        raise SystemExit(
            "GIT_FAIL " + " ".join(args) + "\n"
            + child.stderr.decode("utf-8", errors="replace")
        )
    return child.stdout if binary else child.stdout.decode("utf-8").strip()


def blob(checkpoint: str, path: str) -> bytes:
    return git("cat-file", "blob", f"{checkpoint}:{path}", binary=True)  # type: ignore[return-value]


def require_commit(sha: str, label: str) -> None:
    if re.fullmatch(r"[0-9a-f]{40}", sha) is None:
        raise SystemExit(f"{label}_SHA_FORMAT_INVALID")
    resolved = git("rev-parse", f"{sha}^{{commit}}")
    if resolved != sha:
        raise SystemExit(f"{label}_SHA_MISMATCH={resolved}")


def generate(source_sha: str, runner_checkpoint: str, runner_rev: str) -> str:
    require_commit(source_sha, "SOURCE")
    require_commit(runner_checkpoint, "RUNNER")
    runner = blob(runner_checkpoint, RUNNER_PATH)
    runner_text = runner.decode("utf-8")
    source_pin = re.search(r'^SOURCE_SHA\s*=\s*["\']([0-9a-f]{40})["\']\s*$', runner_text, re.MULTILINE)
    if source_pin is None or source_pin.group(1) != source_sha:
        raise SystemExit("EQ337_UBAR_RUNNER_SOURCE_PIN_MISMATCH")
    revision_pin = re.search(
        r'^runner\.RUNNER_REV\s*=\s*["\']([^"\']+)["\']\s*$',
        runner_text,
        re.MULTILINE,
    )
    if revision_pin is None or revision_pin.group(1) != runner_rev:
        raise SystemExit("EQ337_UBAR_RUNNER_REV_MISMATCH")
    runner_hash = hashlib.sha256(runner).hexdigest()
    runner_url = f"{REPO_RAW}/{runner_checkpoint}/{RUNNER_PATH}"
    cell = f'''import hashlib, urllib.request
from google.colab import runtime
RUNNER_URL = {json.dumps(runner_url)}
RUNNER_SHA256 = {json.dumps(runner_hash)}
with urllib.request.urlopen(RUNNER_URL) as response:
    runner_source = response.read()
measured = hashlib.sha256(runner_source).hexdigest()
print("RUNNER_TRANSPORT_SHA256=" + measured, flush=True)
if measured != RUNNER_SHA256:
    raise RuntimeError("RUNNER_TRANSPORT_HASH_MISMATCH")
release_runtime = runtime.unassign
runtime.unassign = lambda: print("RUNTIME_UNASSIGN_DEFERRED=1", flush=True)
launcher_exit = 0
try:
    exec(compile(runner_source, RUNNER_URL, "exec"), {{"__name__": "__main__"}})
except SystemExit as exc:
    launcher_exit = int(exc.code or 0)
except BaseException as exc:
    launcher_exit = 1
    print("LAUNCHER_EXCEPTION=" + repr(exc), flush=True)
finally:
    print(f"LAUNCHER_EXIT={{launcher_exit}}", flush=True)
    if launcher_exit == 0:
        release_runtime()
    else:
        print("RUNTIME_RETAINED_FOR_DEBUG=1", flush=True)
if launcher_exit != 0:
    raise RuntimeError(f"RUNNER_EXIT={{launcher_exit}}")
'''
    notebook = {
        "cells": [
            {
                "cell_type": "code",
                "execution_count": None,
                "metadata": {},
                "outputs": [],
                "source": cell.splitlines(keepends=True),
            }
        ],
        "metadata": {
            "colab": {"provenance": []},
            "kernelspec": {"display_name": "Python 3", "name": "python3"},
            "language_info": {"name": "python"},
        },
        "nbformat": 4,
        "nbformat_minor": 0,
    }
    return json.dumps(notebook, indent=2, ensure_ascii=False) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--source-sha", required=True)
    parser.add_argument("--runner-checkpoint", required=True)
    parser.add_argument("--runner-rev", required=True)
    parser.add_argument(
        "--output",
        type=Path,
        default=ROOT / "scripts" / "colab_eq337_complex_ubar_radius_validation.ipynb",
    )
    args = parser.parse_args()
    content = generate(args.source_sha, args.runner_checkpoint, args.runner_rev)
    notebook = json.loads(content)
    compile("".join(notebook["cells"][0]["source"]), str(args.output), "exec")
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(content, encoding="utf-8", newline="\n")
    print(
        "EQ337_COMPLEX_UBAR_NOTEBOOK_GENERATED "
        f"source_sha={args.source_sha} runner_checkpoint={args.runner_checkpoint} "
        f"runner_rev={args.runner_rev} "
        f"sha256={hashlib.sha256(content.encode()).hexdigest().upper()} "
        f"output={args.output}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
