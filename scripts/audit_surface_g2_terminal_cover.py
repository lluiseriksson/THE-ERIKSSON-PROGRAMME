"""Terminal evidence and domain audit for Surface-Theorem gate G2.

This is a read-only composition audit.  It does not manufacture numerical
evidence and it never edits the gate board.  Its purpose is to make the
finite/high-beta ownership split and every rational seam executable.
"""

from __future__ import annotations

from fractions import Fraction
from pathlib import Path

from flint import arb

import audit_surface_finite_role_relay as finite_role
import certify_surface_high_beta_q_half as q_certificate
import validate_surface_high_beta_g5_lambda2 as g5_lambda2
import validate_surface_high_beta_g5_ratio_side4_lambda3 as g5_lambda3
import validate_surface_high_beta_lambda3_joint_interior as lambda3_joint
import validate_surface_remainder_delta0_r4_extension_008_transcripts as k2_008
import validate_surface_remainder_delta0_r4_extension_009_hybrid_mixed_provenance as k2_009
import validate_surface_right_edge_five_family_finite_transcripts as g5_finite
import validate_surface_right_edge_five_family_halfline_historical as g5_halfline
import verify_surface_high_beta_bilinear_residual as bilinear_algebra
import verify_surface_high_beta_far_mirror_bound as far_mirror
import verify_surface_high_beta_main_positive as main_positive
import verify_surface_high_beta_q_half_algebra as q_algebra
import verify_surface_high_beta_rest_perturbation_bound as third_block
import verify_surface_k2_direct_joint_relay as k2_relay
import verify_surface_three_block_decomposition as three_block_algebra
from surface_eol_hashes import sha256_variants


ROOT = Path(__file__).resolve().parents[1]
BETA0 = Fraction(1000, 9)
BETA_G5_SPLIT = Fraction(125)
DELTA_MAX = Fraction(9, 1000)
DELTA_G5_SPLIT = Fraction(1, 125)
LAMBDA_EDGE = Fraction(3, 2)
LAMBDA_TWO = Fraction(2)
LAMBDA_THREE = Fraction(3)
PI_UP = Fraction(31415927, 10_000_000)
K2_T_CUT = Fraction(313, 100)
P_SPLIT = Fraction(101, 200)


def _aq(value: Fraction) -> arb:
    return arb(value.numerator) / value.denominator


def _q_transcript_bound() -> None:
    transcript = (
        ROOT / "scripts" / "surface_high_beta_q_half_transcript_20260727.txt"
    ).read_text(encoding="utf-8").splitlines()
    script = ROOT / "scripts" / "certify_surface_high_beta_q_half.py"
    recorded = {
        line.removeprefix("PROVENANCE script_sha256=")
        for line in transcript
        if line.startswith("PROVENANCE script_sha256=")
    }
    assert len(recorded) == 1
    assert recorded.pop() in sha256_variants(script)
    assert (
        "CONFIG beta>=1000/9 t=(0,pi-3/(2beta)] "
        "main_boxes=800 moving_boxes=80 deep_edge=1"
    ) in transcript
    assert transcript[-1].startswith(
        "CERTIFIED: <Phi>-(19/20)<D>>0"
    )


def _row_union(
    rows: list[dict],
    delta_indices: range,
    lambda_indices: range,
) -> None:
    got = {
        (row["delta_index"], row["lambda_index"])
        for row in rows
    }
    expected = {
        (delta_index, lambda_index)
        for delta_index in delta_indices
        for lambda_index in lambda_indices
    }
    assert got == expected


def audit_domain_geometry() -> dict[str, object]:
    """Check the parameter conversion and all non-numerical seams."""

    assert 1 / BETA0 == DELTA_MAX
    assert 1 / BETA_G5_SPLIT == DELTA_G5_SPLIT
    assert DELTA_G5_SPLIT < DELTA_MAX
    lambda_lanes = (
        (Fraction(0), LAMBDA_EDGE),
        (LAMBDA_EDGE, LAMBDA_TWO),
        (LAMBDA_TWO, LAMBDA_THREE),
    )
    assert all(
        lambda_lanes[index][1] == lambda_lanes[index + 1][0]
        for index in range(len(lambda_lanes) - 1)
    )
    assert lambda_lanes[0][0] == 0
    assert lambda_lanes[-1][1] == LAMBDA_THREE

    # On the last K2 birth, lambda>=3 means
    # t<=pi-3*delta<=pi_up-3/125<313/100.
    assert PI_UP - LAMBDA_THREE * DELTA_G5_SPLIT < K2_T_CUT

    # Pin the actual lambda-three certifier domain, not merely the display
    # value used by this composition audit.
    joint_cert = lambda3_joint.cert
    assert joint_cert.LAMBDA0 == LAMBDA_THREE
    assert joint_cert.base.BETA0 == BETA0
    assert joint_cert.X_SPLIT * BETA0 == LAMBDA_THREE
    assert 0 < joint_cert.X_SPLIT < joint_cert.base.X_MAX < PI_UP

    # The far-mirror lane owns p<=101/200.  The joint lane owns
    # x=pi-t in [0,X_MAX], hence p=sin((pi-x)/4) down to the endpoint
    # at X_MAX.  Prove an actual overlap rather than only 0<P_SPLIT<1.
    assert far_mirror.BETA0 == BETA0
    assert far_mirror.P0 == P_SPLIT
    joint_p_floor = (
        (arb.pi() - _aq(joint_cert.base.X_MAX)) / 4
    ).sin()
    assert arb(joint_p_floor.upper()) <= _aq(P_SPLIT)
    return {
        "beta_seams": [BETA0, BETA_G5_SPLIT],
        "delta_seams": [DELTA_G5_SPLIT, DELTA_MAX],
        "lambda_lanes": lambda_lanes,
        "p_seam": P_SPLIT,
        "joint_p_floor_upper": arb(joint_p_floor.upper()),
        "k2_cut_margin": (
            K2_T_CUT
            - (PI_UP - LAMBDA_THREE * DELTA_G5_SPLIT)
        ),
    }


def audit() -> dict[str, object]:
    geometry = audit_domain_geometry()
    finite = finite_role.audit_role()
    assert finite["promotion"] == "FINITE_ROLE_PROVED"

    # K2 owns the main-saddle carrier.  The older delta<=1/125 lane has
    # full t coverage; the last birth owns [0,313/100].
    k2_008.validate()
    assert k2_009.main() == 0
    k2_relay.verify_symbolic_relay()
    k2_relay.verify_budget_inclusion()
    main = main_positive.verify()
    assert main["passed"] and main["worst_lower"] > 0
    # The positivity audit uses the same 158 born t-boxes as the historical
    # delta<=1/125 K2 archive, including the terminal box ending at the
    # frozen rational upper enclosure of pi.
    k2_t_boxes = list(main_positive.born_t_boxes())
    assert main["boxes"] == len(k2_t_boxes) == 158
    assert k2_t_boxes[0][0] == 0
    assert all(
        k2_t_boxes[index][1] == k2_t_boxes[index + 1][0]
        for index in range(len(k2_t_boxes) - 1)
    )
    assert k2_t_boxes[-1][1] > Fraction(3_141_592_6, 10_000_000)

    # The two historical G5 families meet exactly at delta=1/125 and cover
    # lambda in [0,3/2].  The finite family is larger than the subrange used
    # here, which is beta in [1000/9,125].
    finite_g5_rows = g5_finite.validate()
    halfline_rows = g5_halfline.validate()
    _row_union(finite_g5_rows, range(5), range(75))
    _row_union(halfline_rows, range(8), range(75))
    finite_delta_bands = g5_finite.cert.cover.DELTA_BANDS
    assert finite_delta_bands[0][0] == DELTA_G5_SPLIT
    assert finite_delta_bands[0][1] >= DELTA_MAX
    assert (
        "CONFIG delta_partition 0:1/125:1/1000 "
        "lambda_partition 0:3/2:1/50 "
    ) in (
        ROOT
        / "scripts"
        / "certify_surface_right_edge_five_family_halfline_lambda_00_05_transcript.txt"
    ).read_text(encoding="utf-8")

    lambda2 = g5_lambda2.validate(
        g5_lambda2.COMMITTED_PRODUCTION,
        g5_lambda2.COMMITTED_REPLAY,
    )
    assert lambda2["rows"] == 225
    lambda3 = g5_lambda3.validate()
    assert lambda3["rows"] == 450

    # The analytic lambda>=3 lane uses exact algebra, a bound Q>19/20,
    # the fixed-gap mirror lane, the common-x near lane, and the third block.
    q_algebra.verify()
    _q_transcript_bound()
    assert q_certificate.BETA0 == BETA0
    assert q_certificate.CWIN == LAMBDA_EDGE
    q_result = q_certificate.certify()
    assert q_result["passed"] and q_result["worst"].lower() > 0
    far = far_mirror.verify()
    assert far["upper"] < arb(1) / 10**30
    rest = third_block.verify()
    assert third_block.BETA0 == BETA0
    assert rest["upper"] < arb(1) / 100_000
    three_block_algebra.identities()
    bilinear_algebra.verify()
    joint = lambda3_joint.validate()
    assert joint["adverse"].upper() < arb(9) / 10
    assert joint["margin"].lower() > 0

    return {
        "finite_beta": ["20", "1000/9"],
        "high_beta": {
            "beta": ["1000/9", "infinity"],
            "delta": ["0", "9/1000"],
            "lambda_lanes": [
                {
                    "lambda": ["0", "3/2"],
                    "owners": [
                        "[1000/9,125]: finite G5",
                        "[125,infinity): half-line G5",
                    ],
                },
                {"lambda": ["3/2", "2"], "owner": "G5 lambda-two"},
                {"lambda": ["2", "3"], "owner": "G5 ratio-side4"},
                {
                    "lambda": ["3", "infinity"],
                    "owners": [
                        "p<=101/200: fixed-gap mirror",
                        "p>=101/200: common-x joint splice",
                    ],
                },
            ],
        },
        "seams": {
            "beta": ["1000/9", "125"],
            "delta": ["1/125", "9/1000"],
            "lambda": ["3/2", "2", "3"],
            "p": ["101/200"],
        },
        "k2_geometry": "pi_up-3/125<313/100",
        "geometry": geometry,
        "promotion": "G2_TERMINAL_COVER_PROVED",
    }


def main() -> int:
    result = audit()
    print("SURFACE G2 TERMINAL COVER PASS")
    print("finite beta", result["finite_beta"])
    print("high beta", result["high_beta"])
    print("seams", result["seams"])
    print("K2 geometry", result["k2_geometry"])
    print("promotion", result["promotion"])
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
