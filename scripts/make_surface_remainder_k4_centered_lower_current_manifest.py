"""Write provenance manifest for the current centred-lower K4 candidate."""

import hashlib
import json
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]
UNITS = (
    "k4_00275_00280", "k4_00280_00285", "k4_00285_00290",
    "k4_00290_00295", "k4_00295_0030", "k4_0030",
)
OUT = ROOT / "run-records" / "local-staging" / "surface-remainder-k4-centered-lower-current-20260724.json"


def digest(path: Path, lf: bool = False) -> str:
    data = path.read_bytes()
    if lf:
        data = data.replace(b"\r\n", b"\n")
    return hashlib.sha256(data).hexdigest()


def artifact(relative: str) -> dict:
    path = ROOT / relative
    return {"path": relative, "sha256": digest(path), "sha256_lf": digest(path, True)}


def main() -> None:
    outputs = []
    source_heads = set()
    dependencies = set()
    for unit in UNITS:
        for suffix in ("_current_regen", "_current_regen_rerun"):
            relative = f"scripts/surface_remainder_k4_{unit}{suffix}.txt"
            outputs.append(artifact(relative))
            lines = (ROOT / relative).read_text(encoding="utf-8").splitlines()
            source_heads.add(next(line.split()[-1] for line in lines
                                  if line.startswith("PROVENANCE git_head ")))
            dependencies.update(line.split()[1] for line in lines
                                if line.startswith("DEPENDENCY "))
    assert len(source_heads) == 1, source_heads
    inputs = [artifact(relative) for relative in sorted(dependencies)]
    inputs.append(artifact("scripts/audit_surface_remainder_k4_centered_lower_current_regen.py"))
    manifest_head = subprocess.check_output(
        ["git", "-c", "safe.directory=*", "rev-parse", "HEAD"], cwd=ROOT,
        text=True).strip()
    data = {
        "schema_version": 1,
        "run_id": "surface-remainder-k4-centered-lower-current-20260724",
        "status": "current-candidate-local-only",
        "claim_scope": "Current-head candidate K4 centred lower union delta=[0.0275,0.0305], t=2.9; six adjacent units and 55296 cells. No K4/G2/G6/S1'''/S2''' promotion.",
        "git_head": next(iter(source_heads)),
        "manifest_generated_head": manifest_head,
        "config": {"precision": 140, "cells_per_unit": 9216},
        "units": list(UNITS),
        "total_cells": 6 * 9216,
        "inputs": inputs,
        "outputs": outputs,
        "validator": {"path": "scripts/audit_surface_remainder_k4_centered_lower_current_regen.py",
                       "verdict": "PASS", "production_replay_byte_identical": True},
        "promotion": "NONE",
        "notes": "Current dependency hashes and local fractions pass. Regular delta=0 splice, full delta/t union, overlap theorem, and literal weighted judges remain open.",
    }
    OUT.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
    print("WROTE", OUT.relative_to(ROOT), "outputs", len(outputs))


if __name__ == "__main__":
    main()
