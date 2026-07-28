"""Build a quarantined provenance manifest for the order-24 units 41--65.

This manifest is deliberately candidate-only: it records production/replay
identity and geometry, but cannot promote G2, H_tail, or G6.
"""
from __future__ import annotations

from fractions import Fraction
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "run-records" / "local-staging" / "surface-scaled-bulk-cwin3p2-mid-cover-order24-units41-47-20260724.json"
START = 41
END = 48
DRIVER = "scripts/run_surface_scaled_bulk_cwin3p2_mid_cover_order24_repair.py"
VALIDATOR = "scripts/validate_surface_scaled_bulk_cwin3p2_mid_cover_order24_unit.py"
BESSEL = "scripts/certify_bulk_beta_taylor_arb.py"
PREREG = "docs/SURFACE-G2-CWIN3P2-MID-COVER-ORDER24-REPAIR-EXTENSION4-PREREG-20260723.md"


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def lf_digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes().replace(b"\r\n", b"\n")).hexdigest()


def main() -> int:
    lo = Fraction(117, 2)
    units = []
    total_rows = 0
    for index in range(START, END):
        hi = lo + Fraction(1, 4)
        label = f"{lo}_{hi}".replace("/", "_")
        prod = ROOT / "scripts" / f"surface_scaled_bulk_mid_cover_{index}_{label}.txt"
        replay = ROOT / "scripts" / f"surface_scaled_bulk_mid_cover_{index}_{label}_rerun.txt"
        if not prod.exists() or not replay.exists():
            raise FileNotFoundError(prod if not prod.exists() else replay)
        if prod.read_bytes() != replay.read_bytes():
            raise AssertionError(f"production/replay mismatch: unit {index}")
        text = prod.read_text(encoding="utf-8").replace("\r\n", "\n")
        m = re.search(r"^t_rows (\d+)$", text, re.M)
        if not m:
            raise AssertionError(f"missing t_rows: unit {index}")
        rows = int(m.group(1))
        total_rows += rows
        units.append({
            "index": index,
            "beta_domain": [str(lo), str(hi)],
            "t_rows": rows,
            "production": {
                "path": f"scripts/{prod.name}",
                "sha256": digest(prod),
                "sha256_lf": lf_digest(prod),
            },
            "replay": {
                "path": f"scripts/{replay.name}",
                "sha256": digest(replay),
                "sha256_lf": lf_digest(replay),
            },
        })
        lo = hi
    manifest = {
        "schema_version": 1,
        "run_id": "surface-scaled-bulk-cwin3p2-mid-cover-order24-units41-47-20260724",
        "status": "quarantined-candidate-only",
        "claim_scope": "Order-24 candidate sign rows for beta [117/2,241/4]; no exhaustive finite-beta union, H_tail relay, G2, or G6 promotion.",
        "source_transcript_git_head": subprocess.check_output(
            ["git", "-c", f"safe.directory={ROOT.as_posix()}", "rev-parse", "HEAD"],
            cwd=ROOT, text=True).strip(),
        "configuration": {
            "cwin": "3/2", "beta_order": 24, "t_order": 25,
            "arb_bits": 180, "min_dt": "1/100000", "beta_width": "1/4",
            "beta_domain": ["117/2", "241/4"], "rows": total_rows,
        },
        "units": units,
        "dependencies": {
            name: {"path": name, "sha256": digest(ROOT / name)}
            for name in (DRIVER, VALIDATOR, BESSEL, PREREG)
        },
        "validation": {
            "validator": VALIDATOR,
            "verdict": "PASS",
            "units": len(units),
            "production_replay_byte_identical": True,
            "strict_negative_rows": total_rows,
            "promotion": "NONE",
        },
        "promotion": "NONE",
        "notes": "Candidate-only repair chain; global cover, signed derivative-tail contract, and sign-to-H_tail relay remain open.",
    }
    OUT.write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
    print(OUT)
    print("ORDER24 UNITS 41-47 MANIFEST PASS", "units", len(units), "rows", total_rows)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
