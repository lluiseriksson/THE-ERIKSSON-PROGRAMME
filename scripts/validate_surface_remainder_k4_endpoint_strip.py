"""Validate the scoped two-box K4 endpoint strip transcript."""

import hashlib
from pathlib import Path

from flint import arb


ROOT = Path(__file__).resolve().parents[1]
TRANSCRIPT = ROOT / "scripts" / "surface_remainder_k4_endpoint_strip_transcript.txt"
DEPENDENCIES = (
    "scripts/surface_remainder_k4_endpoint_strip_terminal.py",
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
    assert lines[0] == "K4 ENDPOINT TWO-BOX STRIP TERMINAL"
    assert "K4 ENDPOINT TWO-BOX STRIP PASS" in lines
    assert "SCOPE t=2.9 only; delta [0.048,0.05]; no global K4 theorem claim" in lines
    segments = [line for line in lines if line.startswith("segment ")]
    assert len(segments) == 2
    assert "delta 0.048 0.049 cells 2304" in segments[0]
    assert "delta 0.049 0.05 cells 1152" in segments[1]
    dependencies = {
        line.split()[1]: line.split()[3]
        for line in lines if line.startswith("dependency ")
    }
    assert dependencies == {relative: sha256(ROOT / relative)
                            for relative in DEPENDENCIES}
    totals = {
        line.split()[1]: arb(line.split(maxsplit=2)[2])
        for line in lines if line.startswith("total_fraction ")
    }
    expected = {"MD_mirror", "MF_mirror", "MD2r_mirror", "MDFr_mirror",
                "muF_main", "nuD_main", "nuF_main"}
    assert set(totals) == expected
    assert all(value.is_finite() and value.upper() < 1
               for value in totals.values())
    print("K4 ENDPOINT STRIP TRANSCRIPT PASS: two scoped boxes; seven totals < 1")
    return totals


if __name__ == "__main__":
    validate()
