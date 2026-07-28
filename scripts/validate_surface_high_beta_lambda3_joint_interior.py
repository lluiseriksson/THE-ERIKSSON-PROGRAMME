"""Validate the committed lambda-three joint production/replay pair."""

from __future__ import annotations

import hashlib
from pathlib import Path

from flint import arb

import certify_surface_high_beta_lambda3_joint_interior as cert
from surface_eol_hashes import sha256_variants, validate_recorded_dependencies


ROOT = Path(__file__).resolve().parents[1]
PRODUCTION = (
    ROOT / "scripts"
    / "surface_high_beta_lambda3_joint_production_20260728.txt"
)
REPLAY = (
    ROOT / "scripts"
    / "surface_high_beta_lambda3_joint_replay_20260728.txt"
)
SOURCE_HEAD = "77fe27772e8a1686bbaf1194042925dadee37bce"
EXPECTED_SHA256 = (
    "a2e9f9b7db49ddc3b6186552ef33c0b7bb6d15cc2a64929137e3f3032bc8f4c9"
)


def validate() -> dict[str, object]:
    production_bytes = PRODUCTION.read_bytes()
    replay_bytes = REPLAY.read_bytes()
    if production_bytes != replay_bytes:
        raise AssertionError("production/replay byte mismatch")
    if EXPECTED_SHA256 not in sha256_variants(PRODUCTION):
        raise AssertionError("unexpected transcript digest")
    lines = production_bytes.decode("utf-8").splitlines()
    if lines[0] != f"PROVENANCE git_head {SOURCE_HEAD}":
        raise AssertionError("wrong source head")
    recorded_dependencies = {
        line.split()[1]: line.split()[2]
        for line in lines
        if line.startswith("DEPENDENCY ")
    }
    validate_recorded_dependencies(
        recorded_dependencies, cert.DEPENDENCIES, ROOT
    )
    if "HIGH-BETA LAMBDA3 JOINT INTERIOR PASS" not in lines:
        raise AssertionError("missing terminal pass")
    config = (
        "CONFIG beta>=1000/9 lambda>=3 p>=101/200 "
        f"x_boxes={cert.MOVING_BOXES}+{cert.FIXED_BOXES} arb_bits=180"
    )
    if config not in lines:
        raise AssertionError("wrong domain configuration")
    rho_line = next(line for line in lines if line.startswith("rho "))
    adverse_line = next(
        line for line in lines if line.startswith("joint_adverse_upper ")
    )
    margin_line = next(
        line for line in lines if line.startswith("relay_margin ")
    )
    rho = arb(rho_line[4:].split(" worst ", 1)[0])
    adverse = arb(adverse_line[20:].split(" worst ", 1)[0])
    margin = arb(margin_line[13:].split(" =", 1)[0])
    if not arb(rho.upper()) < arb(1) / 25:
        raise AssertionError("rho upper endpoint is not below 1/25")
    if not arb(adverse.upper()) < arb(9) / 10:
        raise AssertionError("joint adverse endpoint is not below 9/10")
    if not arb(margin.lower()) > 0:
        raise AssertionError("relay margin lower endpoint is not positive")
    return {
        "sha256": EXPECTED_SHA256,
        "checkout_sha256": hashlib.sha256(production_bytes).hexdigest(),
        "rho": rho,
        "adverse": adverse,
        "margin": margin,
    }


def main() -> int:
    result = validate()
    print("HIGH-BETA LAMBDA3 JOINT REPLAY VALIDATION PASS")
    print("sha256", result["sha256"])
    print("rho", result["rho"].str(50))
    print("adverse", result["adverse"].str(50))
    print("margin", result["margin"].str(50))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
