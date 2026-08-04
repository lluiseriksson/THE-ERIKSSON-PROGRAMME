"""Run the quarantined low-z carrier substitution against the L3 design smoke."""

from __future__ import annotations

import hashlib
import json
import subprocess
import sys
from pathlib import Path

import surface_remainder_carrier_jet_lowz_candidate as candidate


def main() -> int:
    candidate.install()
    # Import only after installation: the smoke's carrier functions resolve
    # the patched module globals while all historical source files remain
    # untouched.
    import surface_remainder_complement_l3_smoke as smoke

    print("=== K4 COMPLEMENT LOW-Z CARRIER CANDIDATE ===")
    print("adapter sha256:", hashlib.sha256(Path(candidate.__file__).read_bytes()).hexdigest())
    print("smoke sha256:", hashlib.sha256(Path(smoke.__file__).read_bytes()).hexdigest())
    print("mode: candidate-only; carrier_jet patched in this process")
    for grid in (32, 64):
        totals = smoke.centered_complement_second_coefficients(grid)
        finite = all(value.is_finite() for value in totals.values())
        print("grid", grid, "finite", finite)
        print({name: value.str(8) for name, value in totals.items()})
        if not finite:
            return 2
        print("adapter calls:", candidate.LOWZ_CALLS, "historical fallback:", candidate.FALLBACK_CALLS)
        print("observed z bounds:", candidate.Z_BOUNDS)
    print("LOW-Z CARRIER CANDIDATE SMOKE FINITE; NO K4/G2/G6 PROMOTION")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
