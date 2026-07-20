import importlib.util
from pathlib import Path

from flint import ctx


ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location(
    "h_tail_budget_audit", ROOT / "scripts" /
    "audit_surface_h_tail_companion_budget.py")
MOD = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MOD)


def test_order_five_companion_route_fits_registered_budget():
    ctx.prec = 150
    # The executable audit contains the outward-rounded comparisons and
    # asserts order four fails while order five passes at beta=beta1.
    assert MOD.main() == 0
