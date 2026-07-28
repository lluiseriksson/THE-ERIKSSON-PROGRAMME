"""Build the quarantined extension-5 provenance manifest after validation."""
from fractions import Fraction
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "run-records" / "local-staging" / "surface-scaled-bulk-cwin3p2-mid-cover-order24-repair-extension5-20260723.json"
DRIVER = "scripts/run_surface_scaled_bulk_cwin3p2_mid_cover_order24_repair_extension5.py"
PREREG = "docs/SURFACE-G2-CWIN3P2-MID-COVER-ORDER24-REPAIR-EXTENSION5-PREREG-20260723.md"
VALIDATOR = "scripts/validate_surface_scaled_bulk_cwin3p2_mid_cover_order24_repair_extension5.py"
BESSEL = "scripts/certify_bulk_beta_taylor_arb.py"


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def lf_digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes().replace(b"\r\n", b"\n")).hexdigest()


def main() -> None:
    units = []
    total_rows = 0
    lo = Fraction(259, 4)
    for index in range(66, 82):
        hi = lo + Fraction(1, 4)
        label = f"{lo}_{hi}".replace("/", "_")
        stem = f"scripts/surface_scaled_bulk_mid_cover_{index}_{label}"
        prod = ROOT / (stem + ".txt")
        replay = ROOT / (stem + "_rerun.txt")
        assert prod.read_bytes() == replay.read_bytes()
        text = prod.read_text(encoding="utf-8").replace("\r\n", "\n")
        rows = int(next(line.split()[1] for line in text.splitlines() if line.startswith("t_rows ")))
        total_rows += rows
        units.append({
            "index": index,
            "beta_domain": [str(lo), str(hi)],
            "t_rows": rows,
            "production": {"path": stem + ".txt", "sha256": digest(prod), "sha256_lf": lf_digest(prod)},
            "replay": {"path": stem + "_rerun.txt", "sha256": digest(replay), "sha256_lf": lf_digest(replay)},
        })
        lo = hi
    manifest = {
        "schema_version": 1,
        "run_id": "surface-scaled-bulk-cwin3p2-mid-cover-order24-repair-extension5-20260723",
        "claim_scope": "Quarantined order-24 sign evidence for beta [259/4,275/4]; no G2/G6 or H_tail promotion.",
        "status": "quarantined",
        "config": {"cwin": "3/2", "beta_order": 24, "t_order": 25, "prec": 180, "min_dt": "1/100000", "beta_width": "1/4"},
        "beta_union": ["259/4", "275/4"],
        "units": units,
        "total_t_rows": total_rows,
        "dependencies": {name: {"path": name, "sha256": digest(ROOT / name)} for name in (DRIVER, PREREG, VALIDATOR, BESSEL)},
        "failure_boundary": {"unit": 82, "beta_domain": ["275/4", "69"], "near_t": "3.1178733989897687", "reason": "min_dt boundary; no transcript admitted"},
        "validator": {"path": VALIDATOR, "verdict": "PASS", "units": len(units), "production_replay_byte_identical": True},
        "promotion": "NONE",
    }
    OUT.write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
    print(OUT)
    print("EXTENSION5 MANIFEST WRITTEN", "units", len(units), "rows", total_rows)


if __name__ == "__main__":
    main()
