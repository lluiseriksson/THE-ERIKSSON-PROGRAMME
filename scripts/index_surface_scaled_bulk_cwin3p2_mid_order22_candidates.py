"""Index replayed order-22 mid-cover pairs as quarantined candidates.

The source driver itself registers this lane as a repair/quarantine route.
This indexer therefore never creates an admissible G2 manifest: it records
only byte-identical, independently validated pairs for the candidate-union
audit and preserves the explicit non-promotion boundary.
"""

from __future__ import annotations

from fractions import Fraction
import hashlib
import json
from pathlib import Path
import subprocess

from flint import arb

ROOT = Path(__file__).resolve().parents[1]
VALIDATOR = ROOT / "scripts" / "validate_surface_scaled_bulk_cwin3p2_mid_cover_order22_unit.py"
DEPS = (
    ROOT / "scripts" / "run_surface_scaled_bulk_cwin3p2_mid_cover_order22_repair.py",
    ROOT / "scripts" / "certify_bulk_beta_taylor_scaled_design.py",
    ROOT / "scripts" / "certify_bulk_beta_taylor_arb.py",
    ROOT / "docs" / "SURFACE-G2-CWIN3P2-MID-COVER-ORDER22-REPAIR-PREREG-20260722.md",
)


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def parse(path: Path):
    lines = path.read_text(encoding="utf-8").splitlines()
    assert lines[0] == "SCALED BULK SIGN ROW UNIT CWIN3P2 MID COVER ORDER22 REPAIR"
    unit = next(line.split()[1] for line in lines if line.startswith("unit "))
    beta = next(line.split() for line in lines if line.startswith("beta_domain "))
    lo, hi = Fraction(beta[1]), Fraction(beta[2])
    head = next(line.split()[1] for line in lines if line.startswith("git_head "))
    rows = []
    domain = next(line.split() for line in lines if line.startswith("t_domain "))
    cursor = Fraction(domain[1])
    for line in lines:
        if not line.startswith("trow "):
            continue
        fields, upper_text = line.split(" upper ", 1)
        _, index, left, right = fields.split()
        upper = arb(upper_text)
        assert int(index) == len(rows) and Fraction(left) == cursor
        assert Fraction(right) > cursor and upper < 0
        rows.append((Fraction(left), Fraction(right)))
        cursor = Fraction(right)
    assert cursor == Fraction(domain[2])
    assert int(next(line.split()[1] for line in lines if line.startswith("t_rows "))) == len(rows)
    return unit, lo, hi, head, len(rows)


def main() -> int:
    indexed = 0
    for path in sorted((ROOT / "scripts").glob("surface_scaled_bulk_mid_cover_*.txt")):
        if path.name.endswith("_rerun.txt"):
            continue
        try:
            unit, lo, hi, head, rows = parse(path)
        except (AssertionError, IndexError, ValueError, StopIteration):
            continue
        replay = path.with_name(path.stem + "_rerun.txt")
        if not replay.is_file() or path.read_bytes() != replay.read_bytes():
            continue
        result = subprocess.run(
            ["python", str(VALIDATOR.relative_to(ROOT)), "--unit", unit,
             "--lo", str(lo), "--hi", str(hi)],
            cwd=ROOT, capture_output=True, text=True, check=False,
        )
        if result.returncode:
            raise RuntimeError(f"validator failed for {unit}: {result.stdout}{result.stderr}")
        manifest = {
            "schema_version": 1,
            "run_id": f"surface-scaled-bulk-cwin3p2-mid-order22-quarantined-{unit}-20260725",
            "claim_scope": (f"Quarantined order-22 repair pair for beta [{lo},{hi}], "
                            "CWIN=3/2; candidate sign rows only; no G2/G6 promotion."),
            "status": "quarantined",
            "historical_git_head_at_run": head,
            "command": ["python", str(VALIDATOR.relative_to(ROOT)), "--unit", unit,
                        "--lo", str(lo), "--hi", str(hi)],
            "environment": {"python": "3.12.6", "python_flint": "0.9.0",
                            "arb_bits": 180, "beta_order": 22, "t_order": 25},
            "inputs": [{"path": str(dep.relative_to(ROOT)), "sha256": sha256(dep)}
                       for dep in DEPS],
            "outputs": {
                "production": {"path": str(path.relative_to(ROOT)), "sha256": sha256(path)},
                "replay": {"path": str(replay.relative_to(ROOT)), "sha256": sha256(replay)},
            },
            "result": {"beta_domain": [str(lo), str(hi)], "t_rows": rows,
                       "production_replay_byte_equal": True,
                       "all_upper_bounds_negative": True,
                       "validator": "ORDER22 UNIT VALIDATION PASS"},
            "promotion": "NONE",
            "supersedes": [],
        }
        target = ROOT / "run-manifests" / f"{manifest['run_id']}.json"
        target.write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
        indexed += 1
        print("INDEXED", unit, lo, hi, "rows", rows, flush=True)
    print("ORDER22 MID CANDIDATE INDEX PASS", indexed,
          "pairs; QUARANTINED; NO G2/G6 PROMOTION")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
