import importlib.util
from pathlib import Path
import sys

from flint import arb


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT/"scripts"))
SPEC = importlib.util.spec_from_file_location(
    "dual", ROOT/"scripts"/"surface_remainder_positive_dual_parallel.py")
MOD = importlib.util.module_from_spec(SPEC); SPEC.loader.exec_module(MOD)


def test_dual_calibration_preserves_bilinear_series():
    def row(a): return [MOD.tjet(arb(a+k)/10) for k in range(MOD.PREC)]
    original = {"KD": row(20), "KF": row(3), "HDD": row(11), "HDF": row(-4)}
    qk, qh = [arb("0.2")]+[arb(0)]*6, [arb("-0.1")]+[arb(0)]*6
    calibrated = dict(original)
    calibrated["KF"] = MOD.algebra._sadd(
        original["KF"], MOD.algebra._sneg(MOD.algebra._smul(
            [MOD.tjet(x) for x in qk], original["KD"])))
    calibrated["HDF"] = MOD.algebra._sadd(
        original["HDF"], MOD.algebra._sneg(MOD.algebra._smul(
            [MOD.tjet(x) for x in qh], original["HDD"])))
    left = MOD.assemble(calibrated, arb("0.05"), qk, qh)
    right = MOD.algebra.assemble_y(original, arb("0.05"))
    assert all((a.v-b.v).contains(0) for a, b in zip(left, right))
