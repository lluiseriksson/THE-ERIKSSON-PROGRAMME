import importlib.util
from pathlib import Path

from flint import ctx


ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location(
    "h_tail_budget_audit", ROOT / "scripts" /
    "audit_surface_h_tail_companion_budget.py")
MOD = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MOD)


def test_corrected_order_five_companion_route_exceeds_registered_budget():
    ctx.prec = 150
    # The executable audit contains the outward-rounded comparisons and
    # asserts that both historical sufficient bounds exceed the budget after
    # the full-moment normalization repair.  This pins a negative result.
    assert MOD.main() == 0
