from fractions import Fraction
import importlib.util
from pathlib import Path
import sys

import mpmath as mp


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT/"scripts"))
SPEC = importlib.util.spec_from_file_location(
    "left_edge", ROOT/"scripts"/"certify_left_edge_beta_taylor_arb.py")
MOD = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MOD)


def independent_W(beta, t):
    FA = FB = FAt = FBt = mp.mpf("0")
    for m in range(1, 80):
        im = mp.besseli(m, beta)
        a = im**2*((m-1)*mp.besseli(m-1, beta)**2
                   +(m+1)*mp.besseli(m+1, beta)**2)
        b = m*im**4
        FA += a*mp.sin(m*t); FB += b*mp.sin(m*t)
        FAt += m*a*mp.cos(m*t); FBt += m*b*mp.cos(m*t)
    return 2*(FAt*FB-FA*FBt)


def test_normalized_left_box_contains_independent_samples():
    mp.mp.dps = 70
    box = MOD.LeftEdgeBox(Fraction(6), Fraction(61, 10))
    enclosure = box.normalized_W(Fraction(0), Fraction(1, 100))
    lo, hi = float(enclosure.lower()), float(enclosure.upper())
    for beta in (mp.mpf(6), mp.mpf("6.05"), mp.mpf("6.1")):
        for t in (mp.mpf("0.001"), mp.mpf("0.005"), mp.mpf("0.01")):
            value = float(independent_W(beta, t)/t**3)
            assert lo <= value <= hi


def test_left_edge_pilot_beta_box_passes():
    box = MOD.LeftEdgeBox(Fraction(6), Fraction(601, 100))
    normalized, regular = MOD.cover_t(box)
    assert normalized > 0
    assert regular > 0
