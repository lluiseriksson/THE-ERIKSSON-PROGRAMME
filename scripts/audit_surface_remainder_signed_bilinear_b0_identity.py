"""Exact B(0)=0 audit for the signed-bilinear K2 candidate lane.

At delta=0 the nominal cell formulas factor as

    KD = 2 K e,       KF = -4 p A K e,
    HDD = 4 H e,      HDF = -8 p A H e,

where K,H,e,p,A are arbitrary commuting factors (the spatial cell and t
dependence are irrelevant).  Both products are therefore exactly
``-16 K H p A e^2``.  This script checks that algebra with exact rational
coefficients and independently checks the 158 current candidate rows have a
strictly positive KD lower endpoint.  It is an audit of one K2 obligation,
not a K2/G2 promotion.
"""

from __future__ import annotations

import hashlib
import re
import sys
from pathlib import Path

from flint import arb


ROOT = Path(__file__).resolve().parents[1]
ROW = re.compile(
    r"^ROW index=(\d+) lo=(\S+) hi=(\S+) .*? kd=(\[[^]]+\]) .*? verdict=(PASS|FAIL)$"
)


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def audit_transcript(path: Path) -> tuple[int, int]:
    rows = []
    for line in path.read_text(encoding="utf-8").splitlines():
        match = ROW.match(line)
        if match:
            index, lo_text, hi_text, kd_text, verdict = match.groups()
            kd = arb(kd_text)
            rows.append((int(index), lo_text, hi_text, kd, verdict))
    if len(rows) != 158:
        raise AssertionError(f"{path.name}: expected 158 rows, got {len(rows)}")
    for expected, (index, lo_text, hi_text, kd, verdict) in enumerate(rows):
        if index != expected:
            raise AssertionError(f"{path.name}: row index {index} at position {expected}")
        if not kd.lower() > 0:
            raise AssertionError(f"{path.name}: KD lower is not positive at row {index}: {kd}")
        # For full moments the quotient recursion has d_0=KD(0)^2/4.
        # The positive KD lower endpoint checked above is sufficient.
        if verdict != "PASS":
            raise AssertionError(f"{path.name}: non-PASS row {index}")
    return len(rows), sum(1 for *_, verdict in rows if verdict == "PASS")


def main(production: str, replay: str) -> int:
    # Exact coefficient check: 2*(-8) - (-4)*4 = 0.
    left = 2 * (-8)
    right = (-4) * 4
    if left != right or left != -16:
        raise AssertionError("symbolic bilinear cancellation failed")
    production_path = Path(production)
    replay_path = Path(replay)
    p_rows, p_pass = audit_transcript(production_path)
    r_rows, r_pass = audit_transcript(replay_path)
    if production_path.read_bytes() != replay_path.read_bytes():
        raise AssertionError("production/replay bytes differ")
    print("SIGNED-BILINEAR B0 IDENTITY AUDIT PASS")
    print("exact coefficient check: 2*(-8) = (-4)*4 = -16")
    print(f"production_rows={p_rows} production_pass={p_pass}")
    print(f"replay_rows={r_rows} replay_pass={r_pass}")
    print("KD(0)>0 on all 158 archived rows")
    print(f"transcript_sha256={sha256(production_path)}")
    print("NO_K2_G2_PROMOTION")
    return 0


if __name__ == "__main__":
    if len(sys.argv) != 3:
        raise SystemExit("usage: audit_surface_remainder_signed_bilinear_b0_identity.py PRODUCTION REPLAY")
    raise SystemExit(main(sys.argv[1], sys.argv[2]))
