#!/usr/bin/env python3
"""Executable sign-convention witness for CONT-C1 PR 34.

This judge does not decide the KP inequality. It verifies that the audited
head simultaneously contains the positive C1 beta2D convention and the
negative-sign Gibbs tilt with the positive real-trace observable, then emits
a one-plaquette unit-energy witness.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import subprocess
from pathlib import Path


PRODUCER_FILE = Path("YangMills/Continuum/TightnessScaleNoGo.lean")
GIBBS_FILE = Path("YangMills/L1_GibbsMeasure/GibbsMeasure.lean")
OBSERVABLE_FILE = Path("YangMills/ClayCore/SchurPhysicalBridge.lean")


def git(checkout: Path, *args: str) -> str:
    result = subprocess.run(
        ["git", "-C", str(checkout), *args],
        check=False,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    if result.returncode != 0:
        raise RuntimeError(result.stderr.strip())
    return result.stdout.strip()


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require_fragment(text: str, fragment: str, label: str) -> None:
    if fragment not in text:
        raise RuntimeError(f"{label}: required fragment absent: {fragment!r}")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--checkout", required=True, type=Path)
    parser.add_argument("--expected-sha", required=True)
    args = parser.parse_args()

    checkout = args.checkout.resolve()
    head = git(checkout, "rev-parse", "HEAD")
    if head != args.expected_sha:
        raise RuntimeError(f"HEAD mismatch: expected {args.expected_sha}, got {head}")
    if git(checkout, "status", "--porcelain=v2", "--untracked-files=no"):
        raise RuntimeError("tracked checkout is not clean")

    producer_path = checkout / PRODUCER_FILE
    gibbs_path = checkout / GIBBS_FILE
    observable_path = checkout / OBSERVABLE_FILE
    producer = producer_path.read_text(encoding="utf-8")
    gibbs = gibbs_path.read_text(encoding="utf-8")
    observable = observable_path.read_text(encoding="utf-8")

    require_fragment(
        producer,
        "1 / (S.g2 * S.a ^ 2)",
        str(PRODUCER_FILE),
    )
    require_fragment(
        gibbs,
        "fun U => -β * wilsonAction plaquetteEnergy U",
        str(GIBBS_FILE),
    )
    require_fragment(
        observable,
        "fun U => U.val.trace.re",
        str(OBSERVABLE_FILE),
    )

    beta = 1.0
    positive_wilson_weight = math.exp(beta)
    checked_gibbs_weight = math.exp(-beta)
    assert positive_wilson_weight != checked_gibbs_weight

    print(
        json.dumps(
            {
                "audit_status": "PASS",
                "claim_verdict": "FAIL",
                "producer_sha": head,
                "classification": (
                    "finite sign-convention witness; not a physics theorem"
                ),
                "inputs": {
                    "plaquettes": 1,
                    "plaquette_energy": 1,
                    "beta": beta,
                },
                "witness": {
                    "c1_positive_weight": positive_wilson_weight,
                    "checked_gibbs_weight": checked_gibbs_weight,
                    "equal": False,
                },
                "files": {
                    str(PRODUCER_FILE): sha256(producer_path),
                    str(GIBBS_FILE): sha256(gibbs_path),
                    str(OBSERVABLE_FILE): sha256(observable_path),
                },
                "scope": (
                    "The witness rejects the unbridged physical sign convention; "
                    "it does not reject the absolute-value KP cap."
                ),
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
