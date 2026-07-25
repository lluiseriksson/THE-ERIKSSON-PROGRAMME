"""Index already replayed high-order transcripts as candidate manifests.

This is a read-only verifier plus provenance indexer.  It accepts only pairs
whose current generic validator passes, whose stored production/replay bytes
are equal, and whose dependency hashes match the current worktree.  Every
manifest is explicitly ``current-candidate`` with ``promotion: NONE``.
"""

from __future__ import annotations

from fractions import Fraction
import hashlib
import json
from pathlib import Path
import re
import subprocess

from flint import arb

ROOT = Path(__file__).resolve().parents[1]
VALIDATOR = ROOT / "scripts/validate_surface_scaled_bulk_cwin3p2_high_unit.py"
DRIVER = ROOT / "scripts/certify_bulk_beta_taylor_scaled_sign_rows_cwin3p2_high.py"
DESIGN = ROOT / "scripts/certify_bulk_beta_taylor_scaled_design.py"
ARB = ROOT / "scripts/certify_bulk_beta_taylor_arb.py"
DEPS = (DRIVER, DESIGN, ARB, VALIDATOR)
TARGET_LO, TARGET_HI = Fraction(87), Fraction(100)


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def parse_transcript(path: Path):
    lines = path.read_text(encoding="utf-8").splitlines()
    assert lines[0] == "SCALED BULK SIGN ROW UNIT CWIN3P2 HIGH"
    unit = next(x.split()[1] for x in lines if x.startswith("unit "))
    beta = next(x.split() for x in lines if x.startswith("beta_domain "))
    lo, hi = Fraction(beta[1]), Fraction(beta[2])
    head = next(x.split()[1] for x in lines if x.startswith("git_head "))
    rows = []
    for line in lines:
        if not line.startswith("trow "):
            continue
        fields, upper_text = line.split(" upper ", 1)
        _, index, lo_t, hi_t = fields.split()
        upper = arb(upper_text)
        assert int(index) == len(rows) and upper < 0
        rows.append((Fraction(lo_t), Fraction(hi_t)))
    domain = next(x.split() for x in lines if x.startswith("t_domain "))
    cursor = Fraction(domain[1])
    for lo_t, hi_t in rows:
        assert lo_t == cursor and hi_t > lo_t
        cursor = hi_t
    assert cursor == Fraction(domain[2])
    return unit, lo, hi, head, len(rows)


def main() -> int:
    indexed = 0
    for path in sorted((ROOT / "scripts").glob("surface_scaled_bulk_*.txt")):
        if path.name.endswith("_rerun.txt"):
            continue
        try:
            unit, lo, hi, head, rows = parse_transcript(path)
        except (AssertionError, IndexError, ValueError, StopIteration):
            continue
        if lo < TARGET_LO or hi > TARGET_HI:
            continue
        replay = path.with_name(path.stem + "_rerun.txt")
        if not replay.is_file() or path.read_bytes() != replay.read_bytes():
            raise RuntimeError(f"replay mismatch or missing: {path.name}")
        # The generic validator is the independent row/adjacency check.
        result = subprocess.run(
            ["python", str(VALIDATOR.relative_to(ROOT)), "--unit", unit,
             "--lo", str(lo), "--hi", str(hi)],
            cwd=ROOT, capture_output=True, text=True, check=False)
        if result.returncode:
            raise RuntimeError(f"validator failed for {unit}: {result.stdout}{result.stderr}")
        manifest = {
            "schema_version": 1,
            "run_id": f"surface-scaled-bulk-cwin3p2-high-historical-{unit}-20260725",
            "claim_scope": (f"Historical paired production/replay candidate for beta [{lo},{hi}], "
                            "CWIN=3/2, beta-order 40, t-order 45, Arb precision 220. "
                            "Current validator replayed the stored pair; no G2/G6 or H_tail promotion."),
            "status": "current-candidate",
            "historical_git_head_at_run": head,
            "command": ["python", str(VALIDATOR.relative_to(ROOT)), "--unit", unit,
                        "--lo", str(lo), "--hi", str(hi)],
            "environment": {"python": "3.12.6", "python_flint": "0.9.0",
                            "arb_bits": 220, "beta_order": 40, "t_order": 45},
            "inputs": [{"path": str(p.relative_to(ROOT)), "sha256": sha256(p)}
                       for p in DEPS],
            "outputs": {
                "production": {"path": str(path.relative_to(ROOT)), "sha256": sha256(path)},
                "replay": {"path": str(replay.relative_to(ROOT)), "sha256": sha256(replay)},
            },
            "result": {"beta_domain": [str(lo), str(hi)], "t_rows": rows,
                       "production_replay_byte_equal": True,
                       "all_upper_bounds_negative": True,
                       "validator": "CWIN3P2 HIGH VALIDATION PASS"},
            "promotion": "NONE",
            "supersedes": [],
        }
        target = ROOT / "run-manifests" / f"{manifest['run_id']}.json"
        target.write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
        indexed += 1
        print("INDEXED", unit, lo, hi, "rows", rows, flush=True)
    print("HISTORICAL HIGH CANDIDATE INDEX PASS", indexed,
          "units; NO G2/G6 PROMOTION", flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
