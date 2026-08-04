"""Independent exact anchors required by the Surface final seal."""

from __future__ import annotations

from fractions import Fraction
from pathlib import Path
import sys


ROOT = Path(__file__).resolve().parents[1]
SCRIPTS = ROOT/"scripts"
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

import audit_surface_full_moment_y_normalization as normalization
import verify_surface_high_beta_bilinear_residual as two_block
import verify_surface_high_beta_q_half_algebra as q_algebra
import verify_surface_high_beta_weak_main_far_relay as far_relay
import verify_surface_high_beta_weak_main_relay as near_relay
import verify_surface_k2_companion_zero_cancellation as companion_zero
import verify_surface_three_block_decomposition as three_block


def finite_w_anchor() -> None:
    a, b, ap, bp = (
        Fraction(7, 5),
        Fraction(11, 6),
        Fraction(-3, 4),
        Fraction(5, 9),
    )
    e_prime = (ap*b-a*bp)/(2*b*b)
    w = 2*(ap*b-a*bp)
    assert b > 0
    assert 4*b*b*e_prime == w
    scale = Fraction(3, 7)
    scaled_w = 2*((scale*ap)*(scale*b)-(scale*a)*(scale*bp))
    assert scaled_w == scale**2*w


def audit() -> dict[str, object]:
    normalized_files = normalization.audit(ROOT)
    assert len(normalized_files) == 16
    companion_zero.verify()
    q_algebra.verify()
    two_block.verify()
    three_block.identities()
    near = near_relay.verify()
    far = far_relay.verify()
    assert near["lower_margin"] > 0
    assert far["lower_margin"] > 0
    finite_w_anchor()
    return {
        "normalization_files": len(normalized_files),
        "near_margin": near["lower_margin"],
        "far_margin": far["lower_margin"],
        "promotion": "CLOSED_FORM_ANCHORS_PROVED",
    }


def main() -> int:
    result = audit()
    print("SURFACE CLOSED-FORM ANCHOR GATE PASS")
    print("normalization_files", result["normalization_files"])
    print("near_margin", result["near_margin"])
    print("far_margin", result["far_margin"])
    print("promotion", result["promotion"])
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
