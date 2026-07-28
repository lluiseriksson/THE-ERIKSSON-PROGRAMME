"""Read-only terminal G2 composition using the two weak-main lanes."""

from __future__ import annotations

from fractions import Fraction
import hashlib
from pathlib import Path

from flint import arb

import audit_surface_finite_role_relay as finite_role
import certify_surface_high_beta_q_half as q_certificate
import validate_surface_high_beta_g5_lambda2 as g5_lambda2
import validate_surface_high_beta_g5_ratio_side4_lambda3 as g5_lambda3
import validate_surface_high_beta_lambda3_joint_interior as lambda3_joint
import validate_surface_high_beta_lambda3_weak_relay_inputs as weak_inputs
import validate_surface_k2_weak_main_covariance_transcripts as weak_transcripts
import validate_surface_right_edge_five_family_finite_transcripts as g5_finite
import validate_surface_right_edge_five_family_halfline_historical as g5_halfline
import verify_surface_high_beta_bilinear_residual as bilinear_algebra
import verify_surface_high_beta_far_mirror_bound as far_mirror
import verify_surface_high_beta_q_half_algebra as q_algebra
import verify_surface_high_beta_rest_perturbation_bound as third_block
import verify_surface_high_beta_weak_main_far_relay as far_relay
import verify_surface_high_beta_weak_main_relay as near_relay
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
PI_UP = Fraction(31_415_927, 10_000_000)
P_SPLIT = Fraction(101, 200)
RELAY_PAIRS = {
    "near": {
        "stem": "surface-high-beta-weak-main-relay",
        "sha256": (
            "4C3F3D8CEE1DCB26C947807D7C3243CA0B291C6592E824CBAEBAE1F982E415EC"
        ),
        "pass": "HIGH-BETA WEAK-MAIN RELAY EXACT PASS",
    },
    "far": {
        "stem": "surface-high-beta-weak-main-far-relay",
        "sha256": (
            "11D437B925042C366E743C79D39A58A8F8F07384DDAEDA2EA47C5CA439DE6AC0"
        ),
        "pass": "HIGH-BETA WEAK-MAIN FAR RELAY EXACT PASS",
    },
}


def _aq(value: Fraction) -> arb:
    return arb(value.numerator)/value.denominator


def _row_union(rows: list[dict], delta_indices: range, lambda_indices: range) -> None:
    got = {(row["delta_index"], row["lambda_index"]) for row in rows}
    expected = {
        (delta_index, lambda_index)
        for delta_index in delta_indices
        for lambda_index in lambda_indices
    }
    assert got == expected


def _validate_relay_pair(name: str) -> str:
    contract = RELAY_PAIRS[name]
    stem = contract["stem"]
    production = ROOT/"outputs"/f"{stem}-production-20260728.txt"
    replay = ROOT/"outputs"/f"{stem}-replay-20260728.txt"
    production_stderr = ROOT/"outputs"/f"{stem}-production-20260728.stderr.txt"
    replay_stderr = ROOT/"outputs"/f"{stem}-replay-20260728.stderr.txt"
    payload = production.read_bytes()
    assert payload == replay.read_bytes()
    assert not production_stderr.read_bytes()
    assert not replay_stderr.read_bytes()
    digest = hashlib.sha256(payload).hexdigest().upper()
    assert contract["sha256"].lower() in sha256_variants(production)
    assert contract["pass"] in payload.decode("utf-8").splitlines()
    return contract["sha256"]


def _q_transcript_bound() -> None:
    transcript = (
        ROOT/"scripts"/"surface_high_beta_q_half_transcript_20260727.txt"
    ).read_text(encoding="utf-8").splitlines()
    script = ROOT/"scripts"/"certify_surface_high_beta_q_half.py"
    prefix = "PROVENANCE script_sha256="
    recorded = {
        line[len(prefix):] for line in transcript if line.startswith(prefix)
    }
    assert len(recorded) == 1
    assert recorded.pop() in sha256_variants(script)
    assert transcript[-1].startswith("CERTIFIED: <Phi>-(19/20)<D>>0")


def audit_domain_geometry() -> dict[str, object]:
    assert 1/BETA0 == DELTA_MAX
    assert 1/BETA_G5_SPLIT == DELTA_G5_SPLIT
    assert DELTA_G5_SPLIT < DELTA_MAX
    assert LAMBDA_EDGE < LAMBDA_TWO < LAMBDA_THREE
    far = weak_transcripts.LANES["far"]
    near = weak_transcripts.LANES["near"]
    assert far["t_min"] == 0
    assert far["t_max"] == near["t_min"] == Fraction(21, 10)
    assert near["t_max"] == PI_UP
    assert _aq(PI_UP) > arb.pi()
    # The near rectangle starts strictly before the p seam.  Together with
    # the adjacent far rectangle this provides the weak premise on all t.
    assert (_aq(Fraction(21, 10))/4).sin() < _aq(P_SPLIT)
    joint_cert = lambda3_joint.cert
    assert joint_cert.LAMBDA0 == LAMBDA_THREE
    assert joint_cert.base.BETA0 == BETA0
    assert joint_cert.X_SPLIT*BETA0 == LAMBDA_THREE
    joint_p_floor = (
        (arb.pi()-_aq(joint_cert.base.X_MAX))/4
    ).sin()
    assert arb(joint_p_floor.upper()) <= _aq(P_SPLIT)
    return {
        "weak_t_union": [Fraction(0), PI_UP],
        "weak_t_seam": Fraction(21, 10),
        "p_seam": P_SPLIT,
        "joint_p_floor_upper": arb(joint_p_floor.upper()),
    }


def audit() -> dict[str, object]:
    geometry = audit_domain_geometry()
    finite = finite_role.audit_role()
    assert finite["promotion"] == "FINITE_ROLE_PROVED"

    finite_g5_rows = g5_finite.validate()
    halfline_rows = g5_halfline.validate()
    _row_union(finite_g5_rows, range(5), range(75))
    _row_union(halfline_rows, range(8), range(75))
    lambda2 = g5_lambda2.validate(
        g5_lambda2.COMMITTED_PRODUCTION,
        g5_lambda2.COMMITTED_REPLAY,
    )
    lambda3 = g5_lambda3.validate()
    assert lambda2["rows"] == 225
    assert lambda3["rows"] == 450

    q_algebra.verify()
    _q_transcript_bound()
    q_result = q_certificate.certify()
    assert q_result["passed"] and q_result["worst"].lower() > 0

    near_certificate = weak_transcripts.validate("near")
    far_certificate = weak_transcripts.validate("far")
    assert near_certificate["rows"] == far_certificate["rows"] == 576
    weak_input_result = weak_inputs.validate()
    assert weak_input_result["rho_upper"] < weak_inputs.RHO_THRESHOLD
    assert weak_input_result["adverse_upper"] < weak_inputs.ADVERSE_THRESHOLD

    near_result = near_relay.verify()
    far_result = far_relay.verify()
    assert near_result["lower_margin"] > 0
    assert far_result["lower_margin"] > Fraction(899, 1000)
    relay_digests = {
        name: _validate_relay_pair(name) for name in RELAY_PAIRS
    }

    far_bound = far_mirror.verify()
    assert far_bound["upper"] < arb(1)/10**30
    rest = third_block.verify()
    assert rest["upper"] < arb(1)/100_000
    bilinear_algebra.verify()
    three_block_algebra.identities()

    return {
        "finite_beta": ["20", "1000/9"],
        "high_beta": ["1000/9", "infinity"],
        "weak_main_lanes": {
            "far": ["0", "21/10"],
            "near": ["21/10", "31415927/10000000"],
        },
        "lambda_seams": ["3/2", "2", "3"],
        "p_seam": "101/200",
        "geometry": geometry,
        "relay_digests": relay_digests,
        "promotion": "G2_WEAK_TERMINAL_COVER_PROVED",
    }


def main() -> int:
    result = audit()
    print("SURFACE G2 WEAK TERMINAL COVER PASS")
    print("finite_beta", result["finite_beta"])
    print("high_beta", result["high_beta"])
    print("weak_main_lanes", result["weak_main_lanes"])
    print("lambda_seams", result["lambda_seams"])
    print("p_seam", result["p_seam"])
    print("promotion", result["promotion"])
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
