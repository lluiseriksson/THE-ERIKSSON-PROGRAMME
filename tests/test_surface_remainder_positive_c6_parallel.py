import importlib.util
from pathlib import Path
import sys

from flint import arb


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT/"scripts"))
SPEC = importlib.util.spec_from_file_location(
    "positive_c6_parallel",
    ROOT/"scripts"/"surface_remainder_positive_c6_parallel.py")
MOD = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MOD)


def test_wire_roundtrip_contains_input():
    value = arb("1.234 +/- 0.005")
    assert (MOD._unwire(MOD._wire(value))-value).contains(0)


def test_uncalibration_is_exact_for_constant_series():
    q = [arb(2)]+[arb(0)]*(MOD.PREC-1)
    kd = MOD.arb_series([arb(3)]+[arb(0)]*(MOD.PREC-1), MOD.PREC)
    hdd = MOD.arb_series([arb(5)]+[arb(0)]*(MOD.PREC-1), MOD.PREC)
    moments = {
        "KD": kd, "HDD": hdd,
        "KF": MOD.arb_series([arb(1-6)]+[arb(0)]*(MOD.PREC-1), MOD.PREC),
        "HDF": MOD.arb_series([arb(7-10)]+[arb(0)]*(MOD.PREC-1), MOD.PREC),
    }
    restored = MOD.uncalibrated_moments(moments, q)
    assert restored["KF"].coeffs()[0].contains(1)
    assert restored["HDF"].coeffs()[0].contains(7)
