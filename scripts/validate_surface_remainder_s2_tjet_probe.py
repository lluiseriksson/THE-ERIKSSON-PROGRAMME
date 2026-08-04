"""Validate the shape and candidate-only scope of an S2 t-jet transcript."""

from __future__ import annotations

import re
import sys
import hashlib
from pathlib import Path


REQUIRED = (
    "PROVENANCE script=",
    "PROVENANCE script_sha256=",
    "PROVENANCE git_head=",
    "PROVENANCE python=",
    "PROVENANCE python_flint=",
    "PROVENANCE arb_prec_bits=",
    "CONFIG beta=",
    "effective_cells=",
    "Y_t0=",
    "Y_t1=",
    "Y_t2=",
    "theta3=",
    "half_abs_upper=",
    "CANDIDATE_LOCAL_PASS: exact t-jet enclosure at one point; no S2/K2/G2/S1'''/S2''' promotion",
)


def main() -> int:
    if len(sys.argv) != 2:
        print("usage: validate_surface_remainder_s2_tjet_probe.py TRANSCRIPT")
        return 2
    path = Path(sys.argv[1])
    text = path.read_text(encoding="utf-8")
    missing = [needle for needle in REQUIRED if needle not in text]
    if missing:
        print("MISSING:", "; ".join(missing))
        return 1
    match = re.search(r"effective_cells=(\d+)", text)
    if not match or int(match.group(1)) < 1:
        print("invalid effective cell count")
        return 1
    if "DESIGN" in text or "OPEN" in text:
        print("unexpected terminal wording")
        return 1
    script_match = re.search(r"PROVENANCE script=(\S+)", text)
    hash_match = re.search(r"PROVENANCE script_sha256=([0-9a-f]{64})", text)
    if not script_match or not hash_match:
        print("missing script provenance")
        return 1
    script_path = (path.parent / script_match.group(1)).resolve()
    if not script_path.exists():
        print(f"script not found: {script_path}")
        return 1
    actual_hash = hashlib.sha256(script_path.read_bytes()).hexdigest()
    if actual_hash != hash_match.group(1):
        print("script hash mismatch")
        return 1
    print("S2 T-JET CANDIDATE TRANSCRIPT SHAPE PASS")
    print("CANDIDATE ONLY; NO S2/K2/G2/S1'''/S2''' PROMOTION")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
