import importlib.util
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location(
    "k4_lower_union", ROOT / "scripts" /
    "audit_surface_remainder_k4_centered_lower_union.py")
MOD = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MOD)


def test_local_lower_union_audit():
    assert MOD.main() == 0
