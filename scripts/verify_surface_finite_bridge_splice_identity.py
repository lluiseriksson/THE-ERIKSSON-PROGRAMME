"""Executable exact checks for the finite-bridge scaling and seam geometry.

This script proves only algebraic identities and interval ownership.  It does
not certify any interval sign row, the finite-beta relay, or H_tail.
"""

from fractions import Fraction

import sympy as sp


def verify_scaling_identity() -> None:
    q = sp.symbols("q", positive=True)
    fa, fb, fat, fbt = sp.symbols("fa fb fat fbt")
    w = 2 * (fat * fb - fa * fbt)
    w_scaled = 2 * ((q * fat) * (q * fb) - (q * fa) * (q * fbt))
    assert sp.expand(w_scaled - q**2 * w) == 0
    e = fa / (2 * fb)
    e_scaled = (q * fa) / (2 * q * fb)
    assert sp.simplify(e_scaled - e) == 0


def verify_seam_geometry() -> None:
    # The regular R6/hybrid lane ends at T_CUT.  The G5 wedge begins at
    # pi - CWIN*delta.  pi_hi is the repository's registered rational upper
    # enclosure, so this is an exact rational inclusion check.
    pi_hi = Fraction(31415927, 10_000_000)
    cwin = Fraction(3, 2)
    delta_lo = Fraction(9, 1000)
    delta_hi = Fraction(1, 100)
    t_cut = Fraction(313, 100)
    assert delta_lo < delta_hi
    edge_at_left = pi_hi - cwin * delta_lo
    edge_at_right = pi_hi - cwin * delta_hi
    assert edge_at_left < t_cut
    assert edge_at_right < edge_at_left
    # Therefore every delta in the tenth birth has
    # [0,T_CUT] union [pi-CWIN*delta,pi] = [0,pi] at the registered enclosure.
    print("SCALE IDENTITY PASS")
    print("SEAM GEOMETRY PASS", "edge_left", edge_at_left, "edge_right", edge_at_right,
          "t_cut", t_cut)


if __name__ == "__main__":
    verify_scaling_identity()
    verify_seam_geometry()
    print("FINITE BRIDGE IDENTITY/SEAM CHECK PASS")
    print("SCOPE algebra and interval ownership only; no sign, H_tail, G2, or G6 claim")
