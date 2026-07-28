"""Validate the committed lambda-eighteen-fifths production/replay pair."""

from __future__ import annotations

import hashlib
from pathlib import Path

from flint import arb

import certify_surface_high_beta_lambda18_5_interior as cert
from surface_eol_hashes import validate_recorded_dependencies


ROOT = Path(__file__).resolve().parents[1]
PRODUCTION = (
    ROOT / "scripts"
    / "surface_high_beta_lambda18_5_interior_production_20260728.txt"
)
REPLAY = (
    ROOT / "scripts"
    / "surface_high_beta_lambda18_5_interior_replay_20260728.txt"
)
SOURCE_HEAD = "f30e918676a4149384d461a1bb11f23bd41e9a80"


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate() -> dict[str, object]:
    production_bytes = PRODUCTION.read_bytes()
    replay_bytes = REPLAY.read_bytes()
    if production_bytes != replay_bytes:
        raise AssertionError("production/replay byte mismatch")
    lines = production_bytes.decode("utf-8").splitlines()
    if lines[0] != f"PROVENANCE git_head {SOURCE_HEAD}":
        raise AssertionError("wrong source head")
    recorded = {
        line.split()[1]: line.split()[2]
        for line in lines if line.startswith("DEPENDENCY ")
    }
    validate_recorded_dependencies(recorded, cert.DEPENDENCIES, ROOT)
    pass_line = (
        "HIGH-BETA LAMBDA18_5 INTERIOR ABSOLUTE-MOMENT PASS"
    )
    if pass_line not in lines:
        raise AssertionError("missing terminal pass")
    rho_line = next(line for line in lines if line.startswith("rho "))
    adverse_line = next(
        line for line in lines if line.startswith("adverse_upper ")
    )
    margin_line = next(
        line for line in lines if line.startswith("relay_margin ")
    )
    rho = arb(rho_line[4:].split(" worst ", 1)[0])
    adverse = arb(adverse_line[14:].split(" < ", 1)[0])
    margin = arb(margin_line[13:].split(" =", 1)[0])
    if not arb(rho.upper()) < arb(3) / 200:
        raise AssertionError("rho upper endpoint is not below 3/200")
    if not arb(adverse.upper()) < arb(9) / 10:
        raise AssertionError("adverse upper endpoint is not below 9/10")
    if not arb(margin.lower()) > 0:
        raise AssertionError("relay margin lower endpoint is not positive")
    return {
        "sha256": hashlib.sha256(production_bytes).hexdigest(),
        "rho": rho,
        "adverse": adverse,
        "margin": margin,
    }


def main() -> int:
    result = validate()
    print("HIGH-BETA LAMBDA18_5 INTERIOR REPLAY VALIDATION PASS")
    print("sha256", result["sha256"])
    print("rho", result["rho"].str(50))
    print("adverse", result["adverse"].str(50))
    print("margin", result["margin"].str(50))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
