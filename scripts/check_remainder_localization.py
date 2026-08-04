"""Executable L0 checks for the pre-registered Surface remainder cutoff."""

from __future__ import annotations

import sys

import sympy as sp


R0 = sp.Integer(4)
R1 = sp.Integer(10)
DELTA_R2 = R1**2 - R0**2
q = sp.symbols("q", real=True)
smooth = 1 - 10*q**3 + 15*q**4 - 6*q**5


def check() -> list[str]:
    errors: list[str] = []
    for order, expected_left, expected_right in (
        (0, 1, 0),
        (1, 0, 0),
        (2, 0, 0),
    ):
        derivative = sp.diff(smooth, q, order)
        if sp.simplify(derivative.subs(q, 0) - expected_left) != 0:
            errors.append(f"C2 left junction fails at derivative {order}")
        if sp.simplify(derivative.subs(q, 1) - expected_right) != 0:
            errors.append(f"C2 right junction fails at derivative {order}")

    delta, rho2, u = sp.symbols("delta rho2 u", positive=True)
    q_delta = (rho2/delta - R0**2)/DELTA_R2
    chi_delta = smooth.subs(q, q_delta)
    chi_u = smooth.subs(q, (u-R0**2)/DELTA_R2)
    first_target = -(u/delta)*sp.diff(chi_u, u)
    second_target = (u**2*sp.diff(chi_u, u, 2)
                     + 2*u*sp.diff(chi_u, u))/delta**2
    substitution = {rho2: u*delta}
    if sp.simplify(sp.diff(chi_delta, delta).subs(substitution)
                   - first_target) != 0:
        errors.append("first delta derivative formula fails")
    if sp.simplify(sp.diff(chi_delta, delta, 2).subs(substitution)
                   - second_target) != 0:
        errors.append("second delta derivative formula fails")

    inside_f, inside_chi_f, outside_chi_f = sp.symbols(
        "inside_f inside_chi_f outside_chi_f"
    )
    core = inside_chi_f + outside_chi_f
    complement = inside_f - inside_chi_f - outside_chi_f
    if sp.expand(core + complement - inside_f) != 0:
        errors.append("core/complement identity fails")

    # pi>3 gives pi*sqrt(15)>sqrt(135)>10, so support avoids the
    # first scaled z=0 point uniformly for beta>=15.
    if not (R1**2 < 15*sp.Integer(3)**2):
        errors.append("support-radius z=0 separation fails")
    return errors


def main() -> int:
    errors = check()
    if errors:
        for error in errors:
            print(f"ERROR: {error}")
        return 1
    print("Surface remainder localization L0 OK: C2, delta derivatives, identity, z=0 separation")
    return 0


if __name__ == "__main__":
    sys.exit(main())
