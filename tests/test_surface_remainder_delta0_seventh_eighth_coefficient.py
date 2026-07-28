import sys
from pathlib import Path

import pytest
import sympy as sp


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT/"scripts"))

import surface_remainder_delta0_seventh_eighth_coefficient as mod  # noqa: E402


def test_frozen_r7_r8_targets_have_registered_normal_forms():
    c = sp.symbols("c", positive=True)
    y6 = sp.factor(mod.target_y6(c))
    y7 = sp.factor(mod.target_y7(c))
    assert sp.degree(sp.together(y6).as_numer_denom()[0], c) == 14
    assert sp.degree(sp.together(y7).as_numer_denom()[0], c) == 16
    assert sp.together(y6).as_numer_denom()[1] == 33554432*c**21
    assert sp.together(y7).as_numer_denom()[1] == 524288*c**24


def test_verify_rejects_a_perturbed_target_vector():
    c = sp.symbols("c", positive=True)
    values = mod.frozen_targets(c)
    values[7] += sp.Rational(1, 10**30)
    with pytest.raises(AssertionError, match="Y7 target mismatch"):
        mod.verify(values)


def test_companion_order_is_frozen_at_eight():
    assert mod.RETAINED == 9
