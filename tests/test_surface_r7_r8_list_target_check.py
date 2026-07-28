from pathlib import Path
import sys


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT/"scripts"))

import check_surface_remainder_delta0_r7_r8_list_targets as check  # noqa: E402


def test_sparse_checker_has_eight_frozen_targets():
    import sympy as sp

    c = sp.symbols("c", positive=True)
    assert len(check.frozen_targets(c)) == 8
