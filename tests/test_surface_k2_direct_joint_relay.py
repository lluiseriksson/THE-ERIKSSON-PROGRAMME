from pathlib import Path
import importlib.util


ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location(
    "verify_surface_k2_direct_joint_relay",
    ROOT / "scripts" / "verify_surface_k2_direct_joint_relay.py",
)
MOD = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MOD)


def test_direct_joint_normalization_and_remainder_implication():
    MOD.verify_symbolic_relay()


def test_certified_delta_budget_is_inside_old_extraction_budget():
    MOD.verify_budget_inclusion()
    assert MOD.DELTA_MAX < MOD.Fraction(1, MOD.BETA_OLD)
