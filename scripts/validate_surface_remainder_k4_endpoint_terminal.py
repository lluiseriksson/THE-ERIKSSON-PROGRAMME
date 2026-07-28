"""Validate the scoped one-box K4 endpoint transcript."""

import hashlib
from pathlib import Path

from flint import arb
from surface_eol_hashes import validate_recorded_dependencies


ROOT = Path(__file__).resolve().parents[1]
TRANSCRIPT = ROOT / "scripts" / "surface_remainder_k4_endpoint_terminal_transcript.txt"
DEPENDENCIES = (
    "scripts/surface_remainder_k4_endpoint_terminal.py",
    "scripts/surface_remainder_centered_delta_integrator_design.py",
    "scripts/surface_remainder_centered_delta_carrier.py",
    "scripts/surface_remainder_complement_l3_smoke.py",
    "scripts/surface_remainder_tjet.py",
    "scripts/surface_remainder_complement.py",
    "scripts/surface_bessel_integral_remainder.py",
)


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate():
    lines = TRANSCRIPT.read_text(encoding="utf-8").splitlines()
    assert lines[0] == "K4 ENDPOINT ONE-BOX TERMINAL"
    assert "K4 ENDPOINT ONE-BOX PASS" in lines
    assert "SCOPE one positive delta box only; no K4 union or theorem claim" in lines
    assert "box delta 0.049 0.05" in lines
    assert "cells 1152" in next(line for line in lines if line.startswith("cells "))
    dependencies = {
        line.split()[1]: line.split()[3]
        for line in lines if line.startswith("dependency ")
    }
    validate_recorded_dependencies(dependencies, DEPENDENCIES, ROOT)
    fractions = {
        line.split()[1]: arb(line.split(maxsplit=2)[2])
        for line in lines if line.startswith("fraction ")
    }
    expected = {"MD_mirror", "MF_mirror", "MD2r_mirror", "MDFr_mirror",
                "muF_main", "nuD_main", "nuF_main"}
    assert set(fractions) == expected
    # Arb's interval comparison against a scalar is not the terminal
    # acceptance predicate: a ball straddling 1 can compare truthily.  The
    # budget judge requires the outward upper endpoint to be strictly below 1.
    assert all(value.is_finite() and value.upper() < 1
               for value in fractions.values())
    print("K4 ENDPOINT TRANSCRIPT PASS: one scoped box; seven fractions < 1")
    return fractions


if __name__ == "__main__":
    validate()
