#!/usr/bin/env python3
"""Generate a pinned, repro-only C6d Step3 diagnostic Colab notebook."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
import subprocess


ROOT = Path(__file__).resolve().parents[1]
SOURCE_SHA = "557a472e96509d3473b925cb07114292fc28587c"
RUNNER_CHECKPOINT = "0eefbd484993e06293d20032668a61409e72a13d"
RUNNER_PATH = "scripts/colab_c6d_step3_localized_precision_validation.py"
RUNNER_REV = "c6d-step3-localized-precision-v4"
DIAGNOSTIC_REV = "c6d-step3-clm-repro-diagnostic-v2"
OUTPUT = ROOT / "scripts" / "colab_c6d_step3_clm_repro_diagnostic.ipynb"


def git_blob() -> bytes:
    child = subprocess.run(
        [
            "git", "-c", "safe.directory=*", "cat-file", "blob",
            f"{RUNNER_CHECKPOINT}:{RUNNER_PATH}",
        ],
        cwd=ROOT,
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    if child.returncode != 0:
        raise RuntimeError(child.stderr.decode(errors="replace"))
    return child.stdout


def main() -> int:
    runner = git_blob()
    runner_text = runner.decode("utf-8")
    if f"runner.SOURCE_SHA = {SOURCE_SHA!r}" not in runner_text:
        raise RuntimeError("C6D_DIAGNOSTIC_SOURCE_PIN_MISMATCH")
    if f'runner.RUNNER_REV = "{RUNNER_REV}"' not in runner_text:
        raise RuntimeError("C6D_DIAGNOSTIC_RUNNER_REV_MISMATCH")
    runner_hash = hashlib.sha256(runner).hexdigest()
    runner_url = (
        "https://raw.githubusercontent.com/lluiseriksson/"
        "THE-ERIKSSON-PROGRAMME/"
        f"{RUNNER_CHECKPOINT}/{RUNNER_PATH}"
    )
    cell = f'''import hashlib, importlib.util, pathlib, urllib.request
from google.colab import files, runtime

RUNNER_URL = {runner_url!r}
RUNNER_SHA256 = {runner_hash!r}
RUNNER_FILE = pathlib.Path("/content/c6d_step3_v3_runner.py")
with urllib.request.urlopen(RUNNER_URL) as response:
    runner_source = response.read()
measured = hashlib.sha256(runner_source).hexdigest()
print("RUNNER_TRANSPORT_SHA256=" + measured, flush=True)
if measured != RUNNER_SHA256:
    raise RuntimeError("RUNNER_TRANSPORT_HASH_MISMATCH")
RUNNER_FILE.write_bytes(runner_source)
spec = importlib.util.spec_from_file_location("c6d_step3_v3_runner", RUNNER_FILE)
if spec is None or spec.loader is None:
    raise RuntimeError("C6D_DIAGNOSTIC_RUNNER_IMPORT_FAILED")
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)
if module.runner.SOURCE_SHA != {SOURCE_SHA!r}:
    raise RuntimeError("C6D_DIAGNOSTIC_SOURCE_SHA_MISMATCH")
if module.runner.RUNNER_REV != {RUNNER_REV!r}:
    raise RuntimeError("C6D_DIAGNOSTIC_RUNNER_REV_MISMATCH")
if len(module.runner.QUEUE) != 9:
    raise RuntimeError("C6D_DIAGNOSTIC_ORIGINAL_QUEUE_MISMATCH")
if module.runner.QUEUE[0][0] != "00_c6d_step3_clm_extensionality_repro":
    raise RuntimeError("C6D_DIAGNOSTIC_FIRST_STAGE_MISMATCH")
module.runner.RUNNER_REV = {DIAGNOSTIC_REV!r}
module.runner.ROOT = pathlib.Path("/content/hrpoly-c6d-step3-clm-diagnostic")
module.runner.EVIDENCE = pathlib.Path("/content/hrpoly-c6d-step3-clm-diagnostic-evidence")
module.runner.ARCHIVE = pathlib.Path("/content/hrpoly-c6d-step3-clm-diagnostic-evidence.tar.gz")
module.runner.PATH_MANIFEST = pathlib.Path("/content/hrpoly-c6d-step3-clm-diagnostic-paths.txt")
module.runner.QUEUE = module.runner.QUEUE[:1]
runtime.unassign = lambda: print("RUNTIME_UNASSIGN_DEFERRED=1", flush=True)
diagnostic_exit = module.runner.main()
files.download(str(module.runner.ARCHIVE))
print("DIAGNOSTIC_EXIT=" + str(diagnostic_exit), flush=True)
print("RUNTIME_RETAINED_FOR_EVIDENCE=1", flush=True)
if diagnostic_exit != 0:
    raise RuntimeError("C6D_DIAGNOSTIC_FAILED_AS_EXPECTED")
'''
    compile(cell, "c6d_step3_clm_diagnostic_cell.py", "exec")
    notebook = {
        "cells": [
            {
                "cell_type": "code",
                "execution_count": None,
                "metadata": {"id": "c6d_step3_clm_repro_diagnostic"},
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
    payload = json.dumps(notebook, indent=2) + "\n"
    OUTPUT.write_text(payload, encoding="utf-8", newline="\n")
    print(
        "C6D_STEP3_CLM_DIAGNOSTIC_NOTEBOOK_GENERATED "
        f"source_sha={SOURCE_SHA} runner_checkpoint={RUNNER_CHECKPOINT} "
        f"runner_sha256={runner_hash.upper()} "
        f"notebook_sha256={hashlib.sha256(payload.encode()).hexdigest().upper()}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
