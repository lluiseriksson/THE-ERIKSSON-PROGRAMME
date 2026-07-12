from __future__ import annotations

import importlib.util
import sys
from decimal import Decimal
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location(
    "audit_v88_sanitation", ROOT / "scripts" / "audit_v88_sanitation.py"
)
assert SPEC and SPEC.loader
auditor = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = auditor
SPEC.loader.exec_module(auditor)


def test_committed_v88_sanitation_evidence() -> None:
    errors, metrics = auditor.audit(ROOT)
    assert errors == []
    assert metrics["pairs"] == 5
    assert metrics["numbers_compared"] == 639
    assert metrics["max_absolute_difference"] == Decimal(0)
    assert metrics["richardson_rows"] == 9
    assert metrics["mirror_drift_rows"] == 12
    assert metrics["domination_rows"] == 17
    assert metrics["m_sharp"] == Decimal("0.36461")
    assert metrics["independent_rerun_matches"] == 5
    assert metrics["arb_files"] == 6


def test_t7_scope_is_the_frozen_v88_certificate_set() -> None:
    assert auditor.V88_ARB_CERTIFICATES == (
        "cascade1_floor_arb.py",
        "certify_bridge_matrix_arb.py",
        "certify_bulk_arb.py",
        "certify_thmB_arb.py",
        "certify_time3_negative_arb.py",
        "exp_integrator_arb.py",
    )
