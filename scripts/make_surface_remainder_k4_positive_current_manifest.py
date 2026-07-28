"""Write a current-head provenance manifest for the K4 positive campaign."""

from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import subprocess

from validate_surface_remainder_k4_positive_0305_0500 import BANDS

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "run-manifests" / "surface-remainder-k4-positive-0305-0500-current-20260724.json"


def digest(relative: str, normalize_lf: bool = False) -> str:
    data = (ROOT / relative).read_bytes()
    if normalize_lf:
        data = data.replace(b"\r\n", b"\n")
    return hashlib.sha256(data).hexdigest()


def artifact(relative: str):
    return {"path": relative, "sha256": digest(relative),
            "sha256_lf": digest(relative, True)}


def main():
    outputs = [artifact(f"scripts/surface_remainder_{unit}_current_regen{suffix}.txt")
               for unit in BANDS for suffix in ("", "_rerun")]
    inputs = [artifact(relative) for relative in (
        "scripts/certify_surface_remainder_k4_positive_0305_0500.py",
        "scripts/run_surface_remainder_k4_positive_0305_0500.py",
        "scripts/validate_surface_remainder_k4_positive_0305_0500.py",
        "scripts/audit_surface_remainder_k4_positive_current_regen.py",
        "scripts/surface_remainder_centered_delta_integrator_design.py",
        "scripts/surface_remainder_centered_delta_carrier.py",
        "scripts/surface_remainder_complement_l3_smoke.py",
        "scripts/surface_remainder_complement.py",
        "docs/SURFACE-REMAINDER-K4-POSITIVE-0305-0500-PREREG.md",
    )]
    source_head = next(
        line.split()[-1]
        for line in (ROOT / "scripts/surface_remainder_k4p_00_current_regen.txt")
        .read_text(encoding="utf-8").splitlines()
        if line.startswith("PROVENANCE git_head ")
    )
    manifest_head = subprocess.check_output(
        ["git", "-c", "safe.directory=*", "rev-parse", "HEAD"],
        cwd=ROOT, text=True).strip()
    data = {
        "schema_version": 1,
        "run_id": "surface-remainder-k4-positive-0305-0500-current-20260724",
        "claim_scope": "Current-head candidate-only K4 centred-delta local bands [0.0305,0.05] at t=2.9; 39 adjacent rational bands, 2304 cells each. No K4/G2/G6/S1'''/S2''' promotion.",
        "status": "current-candidate-local-only",
        "git_head": source_head,
        "manifest_generated_head": manifest_head,
        "finished_utc": datetime.now(timezone.utc).isoformat().replace("+00:00", "Z"),
        "commands": {
            "production_replay": "python scripts/run_surface_remainder_k4_positive_0305_0500.py --unit <unit> [--replay]",
            "unit_validator": "python scripts/validate_surface_remainder_k4_positive_current_regen.py",
            "union_audit": "python scripts/audit_surface_remainder_k4_positive_current_regen.py",
        },
        "environment": {"python": "3.12", "python_flint": "0.9.0", "arb_bits": 140},
        "bands": {unit: [str(lo), str(hi), cells]
                  for unit, (lo, hi, cells) in BANDS.items()},
        "inputs": inputs,
        "outputs": outputs,
        "coverage": {"bands": len(BANDS), "cells": 89856,
                      "worst_fraction": "0.501826306922418",
                      "worst_unit": "k4p_00", "worst_name": "nuD_main"},
        "supersedes": ["surface-remainder-k4-positive-0305-0500-20260719"],
        "promotion": "NONE",
        "notes": "Current-hash production/replay pairs and union audit pass. This is only a local positive-delta witness: regular endpoint, t-union, overlap, and literal global weighted S1'''/S2''' judges remain open.",
    }
    OUT.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
    print("WROTE", OUT.relative_to(ROOT), "outputs", len(outputs))


if __name__ == "__main__":
    main()
