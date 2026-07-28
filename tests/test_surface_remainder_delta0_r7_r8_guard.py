from pathlib import Path
import sys


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT/"scripts"))

import surface_remainder_delta0_r7_r8_guard as guard  # noqa: E402


def test_guard_order_has_two_spare_coefficients():
    assert guard.GUARD_RETAINED == 11


def test_guard_does_not_mutate_registered_default():
    assert guard.exact.RETAINED == 9
