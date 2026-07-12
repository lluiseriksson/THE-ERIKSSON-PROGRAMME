from fractions import Fraction
import importlib.util
from pathlib import Path
import sys

import mpmath as mp


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT/"scripts"))
SPEC = importlib.util.spec_from_file_location(
    "right_edge", ROOT/"scripts"/"certify_right_edge_beta_taylor_arb.py")
MOD = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MOD)


def independent_W(beta, t):
    fa = fb = fat = fbt = mp.mpf("0")
    for m in range(1, 90):
        im = mp.besseli(m, beta)
        a = im**2*((m-1)*mp.besseli(m-1, beta)**2
                   +(m+1)*mp.besseli(m+1, beta)**2)
        b = m*im**4
        fa += a*mp.sin(m*t); fb += b*mp.sin(m*t)
        fat += m*a*mp.cos(m*t); fbt += m*b*mp.cos(m*t)
    return 2*(fat*fb-fa*fbt)


def test_normalized_right_box_contains_independent_samples():
    mp.mp.dps = 80
    box = MOD.RightEdgeBox(Fraction(6), Fraction(61, 10))
    enclosure = box.normalized_W(Fraction(0), Fraction(1, 100))
    lo, hi = float(enclosure.lower()), float(enclosure.upper())
    for beta in (mp.mpf(6), mp.mpf("6.05"), mp.mpf("6.1")):
        for d in (mp.mpf("0.001"), mp.mpf("0.005"), mp.mpf("0.01")):
            value = float(independent_W(beta, mp.pi-d)/d**3)
            assert lo <= value <= hi


def test_right_edge_pilot_beta_box_passes():
    box = MOD.RightEdgeBox(Fraction(6), Fraction(601, 100))
    assert MOD.cover_d(box) > 0


def test_beta_refinement_is_local_and_base_step_is_restored(monkeypatch):
    calls = []

    class FakeBox:
        def __init__(self, lo, hi):
            self.beta_lo, self.beta_hi = lo, hi
            calls.append((lo, hi))

    def fake_cover(box):
        if box.beta_lo == Fraction(1) and box.beta_hi-box.beta_lo > Fraction(1, 20):
            raise RuntimeError("forced local refinement")
        return 1

    monkeypatch.setattr(MOD, "RightEdgeBox", FakeBox)
    monkeypatch.setattr(MOD, "cover_d", fake_cover)
    boxes, d_boxes = MOD.cover_beta(Fraction(1), Fraction(13, 10), Fraction(1, 10))
    assert boxes == d_boxes == 4
    assert (Fraction(11, 10), Fraction(6, 5)) in calls
