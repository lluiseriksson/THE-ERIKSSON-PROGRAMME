import importlib.util
from pathlib import Path

import sympy as sp


ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location(
    "delta0_first",
    ROOT/"scripts"/"surface_remainder_delta0_first_coefficient.py",
)
MOD = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MOD)


def test_leading_bilinear_zero_and_first_coefficient_target():
    assert MOD.leading_bilinear == 0
    target = (4*MOD.c**2-1)/(8*MOD.c**3)
    assert sp.simplify(MOD.y0-target) == 0
    r2 = (-8*MOD.c**4+15*MOD.c**2-4)/(32*MOD.c**6)
    assert sp.simplify(MOD.y1-r2) == 0


def test_regular_phase_has_exact_gaussian_limit():
    assert sp.simplify(MOD.phase0+MOD.c*(MOD.s2+MOD.t2)/2) == 0
