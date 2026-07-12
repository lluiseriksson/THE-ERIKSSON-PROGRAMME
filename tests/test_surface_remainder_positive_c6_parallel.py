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


def test_nominal_kd_floor_pays_order_six_companion_error():
    wide = MOD.arb_series([arb("1 +/- 2")]+[arb(0)]*(MOD.PREC-1), MOD.PREC)
    restricted, floor = MOD.apply_nominal_kd_floor({"KD": wide}, arb("0.05"))
    assert floor < arb("0.5") and floor > arb("0.499")
    assert restricted["KD"].coeffs()[0] > 0


def test_robust_assembly_overlaps_original_on_resolved_point():
    delta = arb("0.04975")
    def series(values):
        return MOD.arb_series([arb(str(value)) for value in values], MOD.PREC)
    moments = {
        "KD": series([2, .1, .02, 0, 0, 0, 0]),
        "KF": series([.3, -.1, .01, 0, 0, 0, 0]),
        "HDD": series([1.1, .2, -.01, 0, 0, 0, 0]),
        "HDF": series([-.4, .05, .02, 0, 0, 0, 0]),
    }
    robust = MOD.robust_assemble_y(moments, delta)
    original = MOD.base.assemble_y(moments, delta)
    assert all((left-right).contains(0)
               for left, right in zip(robust.coeffs(), original.coeffs()))
