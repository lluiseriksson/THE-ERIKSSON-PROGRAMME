from fractions import Fraction
from pathlib import Path
import sys

import sympy as sp


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT/"scripts"))

from surface_bessel_relative_coefficients_exact import (  # noqa: E402
    relative_coefficients,
)
from surface_remainder_delta0_exact_targets import (  # noqa: E402
    frozen_targets,
)


def test_pure_relative_coefficients_registered_heads():
    assert relative_coefficients("A", 2) == [
        Fraction(1), Fraction(-3, 8), Fraction(-15, 128)
    ]
    assert relative_coefficients("B", 2) == [
        Fraction(1), Fraction(-15, 8), Fraction(105, 128)
    ]


def test_pure_target_vector_has_eight_exact_rationals():
    c = sp.symbols("c", positive=True)
    targets = frozen_targets(c)
    assert len(targets) == 8
    assert all(not value.has(sp.Float) for value in targets)
