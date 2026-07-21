"""Validate R6 exact-outer production/replay transcripts."""

import hashlib
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
EXPECTED = {
    "script_sha256": "scripts/certify_surface_remainder_r6_exact_outer_010.py",
    "judge_sha256": "scripts/surface_remainder_delta0_r6_exact_outer_three_witness.py",
    "cover_sha256": "scripts/surface_remainder_delta0_r6_extension_010_cover.py",
    "split_outer_sha256": "scripts/surface_remainder_delta0_outer_domain_r6split.py",
    "exact_integral_sha256": "scripts/probe_surface_remainder_r6_exact_box_integral.py",
    "companion_sha256": "scripts/probe_surface_remainder_r6_companion_charge.py",
    "contract_sha256": "scripts/surface_remainder_delta0_r4_extension_010_hybrid_contract.py",
}


def validate(production, replay):
    p = Path(production).read_bytes()
    r = Path(replay).read_bytes()
    assert p == r, "production/replay are not byte-identical"
    lines = p.decode("utf-8").splitlines()
    assert lines[0] == "R6 EXACT-OUTER PRODUCTION"
    assert any(line.startswith("CONFIG start=0 stop=158 ") for line in lines)
    assert "ROWS 158 PASS_COUNT 158" in lines
    assert "R6 EXACT-OUTER PRODUCTION PASS" in lines
    assert all("FAIL" not in line for line in lines if line.startswith("ROW "))
    for key, relative in EXPECTED.items():
        row = next(line for line in lines
                   if line.startswith("PROVENANCE "+key+"="))
        claimed = row.split("=", 1)[1]
        actual = hashlib.sha256((ROOT / relative).read_bytes()).hexdigest().upper()
        assert claimed == actual, (relative, claimed, actual)
    indices = [int(line.split()[1]) for line in lines
               if line.startswith("ROW ")]
    assert indices == list(range(158))
    print("R6 exact-outer production/replay validator PASS; design scope retained")


if __name__ == "__main__":
    import sys
    validate(sys.argv[1], sys.argv[2])
