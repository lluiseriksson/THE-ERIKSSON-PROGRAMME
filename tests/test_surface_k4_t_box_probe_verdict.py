import sys
from pathlib import Path

from flint import arb

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))

from scripts.surface_remainder_centered_delta_integrator_design import (
    fractions_pass,
)


def test_k4_t_box_verdict_accepts_only_finite_fractions_below_one():
    assert fractions_pass({"a": arb("0.999"), "b": arb("0.25")})
    assert not fractions_pass({"a": arb("1.001"), "b": arb("0.25")})
    assert not fractions_pass({"a": arb("0 +/- 2"), "b": arb("0.25")})
