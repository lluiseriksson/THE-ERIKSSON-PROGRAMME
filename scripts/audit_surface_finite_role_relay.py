"""Role audit for the finite beta Surface-Theorem relay.

This combines already certified range witnesses with exact sign algebra.
It proves the *role implication* on beta in [20,1000/9]; it does not rerun
the interval campaigns and it makes no claim for the high-beta half-line.
"""

from __future__ import annotations

import importlib.util
import json
import re
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SCRIPTS = ROOT / "scripts"
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))


def load_script(name: str):
    path = ROOT / "scripts" / f"{name}.py"
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


G2 = load_script("audit_surface_g2_relay_admissibility")
SIGN = load_script("verify_surface_direct_sign_relay")
LEFT = load_script("validate_surface_finite_beta_scaled_left_transcripts")
LEFT_REPLAY = load_script(
    "validate_surface_finite_beta_scaled_left_independent_rerun"
)
TAIL = load_script("verify_surface_scaled_tail_contract")
RIGHT_COMPACT = load_script(
    "validate_right_edge_beta_taylor_cached_extension"
)
RIGHT_COMPACT_REPLAY = load_script(
    "validate_right_edge_beta_taylor_cached_extension_replay"
)
RIGHT_LOWER = load_script(
    "validate_surface_right_edge_five_family_finite_lower_transcripts"
)
RIGHT_LOWER_REPLAY = load_script(
    "validate_surface_right_edge_five_family_finite_lower_rerun"
)
RIGHT_UPPER = load_script(
    "validate_surface_right_edge_five_family_finite_transcripts"
)
RIGHT_UPPER_REPLAY = load_script(
    "validate_surface_right_edge_five_family_finite_rerun"
)


def theorem_a_present(tex: str) -> bool:
    match = re.search(
        r"\\begin\{theorem\}\[exact\]\\label\{thm:A\}"
        r"(?P<body>.*?)\\end\{theorem\}",
        tex,
        flags=re.DOTALL,
    )
    if not match:
        return False
    body = match.group("body")
    return (
        r"\FB(t)>0" in body
        and r"t\in(0,\pi)" in body
        and r"\beta>0" in body
        and "[SLOT" not in body
    )


def audit_role() -> dict:
    cover = G2.audit_summary()
    SIGN.verify_algebra()
    left_rows = LEFT.validate()
    LEFT_REPLAY.validate()
    TAIL.main()
    compact_totals = RIGHT_COMPACT.validate()
    RIGHT_COMPACT_REPLAY.validate()
    lower_rows = RIGHT_LOWER.validate()
    RIGHT_LOWER_REPLAY.validate()
    upper_rows = RIGHT_UPPER.validate()
    RIGHT_UPPER_REPLAY.validate()
    tex = (
        ROOT / "papers" / "surface-complete" / "surface_theorem_complete.tex"
    ).read_text(encoding="utf-8")

    checks = {
        "bulk_terminal_fingerprint": (
            cover["promotion"] == "FINITE_BULK_SIGN_CERTIFIED"
            and cover["canonical_subcover_owner_count"]
            == G2.EXPECTED_OWNER_COUNT
            and cover["canonical_subcover_fingerprint"]
            == G2.EXPECTED_TERMINAL_FINGERPRINT
        ),
        "bulk_exact_union": cover["beta_union_complete"],
        "bulk_canonical_subcover": cover["canonical_subcover_complete"],
        # A unit enters the canonical subcover only if parse_transcript()
        # found a nonempty adjacent t partition and every outward upper
        # endpoint was strictly negative.  Historical rejected units may
        # remain in ``deficiencies`` without invalidating a complete accepted
        # subcover; they are diagnostics, not members of the ownership chain.
        "bulk_strict_negative_rows": (
            cover["units_admissible"] > 0
            and bool(cover["canonical_subcover"])
        ),
        "left_edge_production": len(left_rows) == 4636,
        "left_edge_replay_and_tail": True,
        "right_edge_compact_20_25": compact_totals == [721, 721, 18659],
        "right_edge_lower_25_30": len(lower_rows) == 225,
        "right_edge_upper_30_125": len(upper_rows) == 375,
        "right_edge_replays": True,
        "denominator_theorem_a_exact": theorem_a_present(tex),
        "direct_sign_algebra": True,
    }
    passed = all(checks.values())
    return {
        "contract": "SURFACE-FINITE-ROLE-RELAY-20260727",
        "beta": ["20", "1000/9"],
        "partition": {
            "left": "0<t<=3/5 (G4)",
            "bulk": "3/5<=t<=pi-3/(2 beta) (scaled W cover)",
            "right": "pi-3/(2 beta)<=t<pi (G5)",
        },
        "checks": checks,
        "logic": [
            "Theorem A gives F_B>0.",
            "W=4*F_B^2*E_prime.",
            "The common scaled-family factor is positive, so W_scaled<0 iff W<0.",
            "The three certified t-ranges cover (0,pi).",
        ],
        "conclusion": (
            "E_prime<0 on beta in [20,1000/9], 0<t<pi"
            if passed else "ROLE_AUDIT_FAILED"
        ),
        "promotion": "FINITE_ROLE_PROVED" if passed else "NONE",
    }


def main() -> int:
    result = audit_role()
    print(json.dumps(result, indent=2, sort_keys=True))
    if result["promotion"] != "FINITE_ROLE_PROVED":
        return 1
    print("SURFACE FINITE ROLE RELAY PASS")
    print("SCOPE finite beta only; no K2/high-beta/G6 promotion")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
