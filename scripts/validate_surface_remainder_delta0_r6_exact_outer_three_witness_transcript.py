"""Replay/provenance validator for the R6 three-witness design transcript.

This validator deliberately proves only transcript integrity and strict
printed margins.  It does not promote the three-witness probe to an
exhaustive K2, H_tail, S1'''/S2''', G2, or G6 certificate.
"""

from __future__ import annotations

import hashlib
from pathlib import Path
import re


ROOT = Path(__file__).resolve().parents[1]
TRANSCRIPT = ROOT / "scripts" / "surface_remainder_delta0_r6_exact_outer_three_witness_transcript.txt"
DEPS = (
    "scripts/surface_remainder_delta0_r6_exact_outer_three_witness.py",
    "scripts/surface_remainder_delta0_r6_extension_010_cover.py",
    "scripts/surface_remainder_delta0_outer_domain_r6split.py",
    "scripts/surface_remainder_delta0_r4_extension_010_hybrid_contract.py",
    "scripts/surface_remainder_delta0_extension_probe.py",
)


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> int:
    lines = TRANSCRIPT.read_text(encoding="utf-8").splitlines()
    assert lines[0] == "R6 EXACT-OUTER THREE-WITNESS DESIGN TRANSCRIPT"
    assert lines[-2] == "R6 EXACT-OUTER THREE-WITNESS PASS"
    assert "SCOPE design-only;" in lines[-1]
    deps = {}
    for line in lines:
        if line.startswith("DEPENDENCY "):
            path, digest = line.split()[1], line.split()[3]
            deps[path] = digest
    assert tuple(deps) == DEPS
    assert deps == {path: sha256(ROOT / path) for path in DEPS}
    rows = []
    pattern = re.compile(
        r"^ROW index (\d+) grid (\d+) radius (\S+) Y5_upper (\S+) "
        r"value_upper (\S+) margin_lower (\S+)$"
    )
    for line in lines:
        match = pattern.match(line)
        if match:
            rows.append(match.groups())
    assert rows == [
        ("0", "384", "59/5", "1677.30864853774438483214",
         "0.0717982159058678257211363", "5922.61955324634974734214"),
        ("50", "192", "59/5", "1508.22792938190568534651",
         "0.0661579572557526086430606", "6091.70591266083856204485"),
        ("156", "384", "59/5", "561.473009131801115145777",
         "0.0324719215620177237676158", "7038.49451894663686713046"),
    ]
    assert all(float(row[-1]) > 0 for row in rows)
    print("R6 EXACT-OUTER THREE-WITNESS TRANSCRIPT VALIDATION PASS")
    print("SCOPE DESIGN ONLY; NO GATE PROMOTION")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
