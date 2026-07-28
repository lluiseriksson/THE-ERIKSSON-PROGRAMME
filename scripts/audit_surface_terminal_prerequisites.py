"""Execute the non-G2 prerequisite chain for the terminal Surface Theorem.

The closure board is an editorial ledger, not evidence.  This auditor rebuilds
the prerequisite verdict from the committed sanitation, analytic manuscript
role checks, the two-witness beta<=3 certificate, and the four compact-range
interval transcript validators.  It does not promote or edit the board.
"""

from __future__ import annotations

import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SCRIPTS = ROOT / "scripts"
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

import audit_surface_optional_hcube_removed as optional_hcube
import audit_surface_thmb_witnesses as thmb_witnesses
import audit_v88_sanitation as v88_sanitation
import validate_bulk_arb_transcript as bulk_3_6
import validate_bulk_beta_taylor_15_20_transcript as bulk_15_20
import validate_bulk_beta_taylor_transcript as bulk_6_15
import validate_left_edge_beta_taylor_transcript as left_3_20
import validate_right_edge_beta_taylor_transcript as right_3_20


def audit() -> dict[str, object]:
    sanitation_errors, sanitation_metrics = v88_sanitation.audit()
    assert not sanitation_errors, "; ".join(sanitation_errors)
    assert optional_hcube.audit() is True
    witness_errors = thmb_witnesses.audit()
    assert not witness_errors, "; ".join(witness_errors)

    bulk_plain = bulk_3_6.validate()
    bulk_mid = bulk_6_15.validate()
    bulk_upper = bulk_15_20.validate()
    left = left_3_20.validate()
    right = right_3_20.validate()

    assert bulk_plain["beta_boxes"] == 3472
    assert bulk_plain["t_boxes"] == 592_068
    assert bulk_mid["beta_boxes"] == 90
    assert bulk_mid["t_boxes"] == 3222
    assert bulk_upper["beta_boxes"] == 89
    assert bulk_upper["t_boxes"] == 4736
    assert left["beta_boxes"] == 170
    assert left["normalized_boxes"] == 170
    assert left["regular_boxes"] == 883
    assert right["beta_boxes"] == 410
    assert right["normalized_boxes"] == 410
    assert right["regular_boxes"] == 6448

    return {
        "promotion": "TERMINAL_PREREQUISITES_PROVED",
        "v88_pairs": sanitation_metrics["pairs"],
        "v88_numbers": sanitation_metrics["numbers_compared"],
        "thmb_witnesses": 2,
        "bulk_beta_boxes": 3472 + 90 + 89,
        "bulk_t_boxes": 592_068 + 3222 + 4736,
        "left_beta_boxes": left["beta_boxes"],
        "right_beta_boxes": right["beta_boxes"],
    }


def main() -> int:
    try:
        result = audit()
    except Exception as exc:
        print(f"TERMINAL PREREQUISITES BLOCKED: {exc}")
        return 1
    print(
        "TERMINAL PREREQUISITES PASS:",
        result["v88_pairs"],
        "v88 sanitation pairs;",
        result["thmb_witnesses"],
        "beta<=3 witnesses;",
        result["bulk_beta_boxes"],
        "bulk beta boxes;",
        result["bulk_t_boxes"],
        "bulk t boxes;",
        result["left_beta_boxes"],
        "left-edge beta boxes;",
        result["right_beta_boxes"],
        "right-edge beta boxes",
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
