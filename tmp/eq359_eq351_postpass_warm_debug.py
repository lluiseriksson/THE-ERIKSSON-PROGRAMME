#!/usr/bin/env python3
"""Run the two bounded Eq351 warm diagnostics after the Eq359 cold PASS.

This orchestrator downloads two immutable child runners by raw GitHub commit,
verifies their SHA-256 digests before execution, and runs them once in order:
the positive-adjoint expansion first, then the canonical negative-bond
factorization.  It never reruns the Eq359 cell and never releases the retained
runtime.  Both child results remain diagnostic PRE-VALIDATION evidence.
"""

from __future__ import annotations

import hashlib
from pathlib import Path
import subprocess
import sys
import time
import urllib.request


CHILDREN = (
    {
        "name": "positive_adjoint",
        "url": (
            "https://raw.githubusercontent.com/lluiseriksson/"
            "THE-ERIKSSON-PROGRAMME/"
            "587a02133b71433e2ebc2fb722389d17a1992cc7/"
            "tmp/eq359_eq351_positive_adjoint_warm_debug.py"
        ),
        "sha256": "3F6F11F3A433B5BA7F102123839CE53FE502440370B1DC6B3468AF0B609143C0",
        "sentinel": "WARM_POSITIVE_ADJOINT_FINAL_STATUS=PASS",
    },
    {
        "name": "negative_bond",
        "url": (
            "https://raw.githubusercontent.com/lluiseriksson/"
            "THE-ERIKSSON-PROGRAMME/"
            "cfcd0d01978ade4ea4ef077d8caa1412b284265a/"
            "tmp/eq359_eq351_negative_bond_warm_debug.py"
        ),
        "sha256": "D10E102C763E51C49E55B3EC96267B601B22F5DF4C47FC7757183D5FC8C5A118",
        "sentinel": "WARM_NEGATIVE_BOND_FINAL_STATUS=PASS",
    },
)


def fetch_child(child: dict[str, str]) -> Path:
    with urllib.request.urlopen(child["url"]) as response:
        payload = response.read()
    measured = hashlib.sha256(payload).hexdigest().upper()
    print(
        f"POSTPASS_TRANSPORT={child['name']} SHA256={measured} BYTES={len(payload)}",
        flush=True,
    )
    if measured != child["sha256"]:
        raise RuntimeError("POSTPASS_HASH_MISMATCH=" + child["name"])
    path = Path("/content") / f"eq351-{child['name']}-warm-debug.py"
    path.write_bytes(payload)
    return path


def run_child(child: dict[str, str], path: Path) -> None:
    started = time.perf_counter()
    process = subprocess.run(
        [sys.executable, str(path)],
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
    )
    elapsed = time.perf_counter() - started
    print(process.stdout, flush=True)
    print(
        f"POSTPASS_CHILD={child['name']} EXIT={process.returncode} "
        f"SECONDS={elapsed:.3f}",
        flush=True,
    )
    if process.returncode != 0:
        raise RuntimeError("POSTPASS_CHILD_FAILED=" + child["name"])
    if child["sentinel"] not in process.stdout:
        raise RuntimeError("POSTPASS_SENTINEL_MISSING=" + child["name"])


def main() -> int:
    for child in CHILDREN:
        path = fetch_child(child)
        run_child(child, path)
    print("WARM_EQ351_POSTPASS_FINAL_STATUS=PASS", flush=True)
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except BaseException as exc:
        print("WARM_EQ351_POSTPASS_FINAL_STATUS=FAIL", flush=True)
        print("WARM_EQ351_POSTPASS_ERROR=" + repr(exc), flush=True)
        raise
