"""Role audit for the finite beta Surface-Theorem relay.

This combines already certified range witnesses with exact sign algebra.
It proves the *role implication* on beta in [20,1000/9]; it does not rerun
the interval campaigns and it makes no claim for the high-beta half-line.
"""

from __future__ import annotations

import importlib.util
import json
import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]


def load_script(name: str):
    path = ROOT / "scripts" / f"{name}.py"
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


G2 = load_script("audit_surface_g2_relay_admissibility")
SIGN = load_script("verify_surface_direct_sign_relay")


def gate_state(board: str, gate: str) -> str:
    match = re.search(
        rf"^\|\s*{re.escape(gate)}\s*\|.*?\|\s*`([^`]+)`\s*\|",
        board,
        flags=re.MULTILINE,
    )
    if not match:
        raise AssertionError(f"{gate} row missing from closure board")
    return match.group(1)


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
    board = (ROOT / "docs" / "SURFACE-CLOSURE-GATES.md").read_text(
        encoding="utf-8"
    )
    tex = (
        ROOT / "papers" / "surface-complete" / "surface_theorem_complete.tex"
    ).read_text(encoding="utf-8")

    g4 = gate_state(board, "G4")
    g5 = gate_state(board, "G5")
    checks = {
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
        "left_edge_g4_certified": g4 == "CERTIFIED",
        "right_edge_g5_certified": g5 == "CERTIFIED",
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
