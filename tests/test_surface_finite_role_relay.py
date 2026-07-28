from pathlib import Path
import importlib.util


ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location(
    "audit_surface_finite_role_relay",
    ROOT / "scripts" / "audit_surface_finite_role_relay.py",
)
MOD = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MOD)


def test_finite_role_relay_is_complete_and_logically_bound():
    result = MOD.audit_role()
    assert result["promotion"] == "FINITE_ROLE_PROVED"
    assert all(result["checks"].values())
    assert result["beta"] == ["20", "1000/9"]


def test_theorem_a_detector_rejects_a_nonpositive_or_slotted_substitute():
    assert not MOD.theorem_a_present(
        r"\begin{theorem}[exact]\label{thm:A}[SLOT]\end{theorem}"
    )
