"""Isolated low-z carrier adapter for candidate diagnostics only.

This module deliberately does not modify ``surface_remainder_carrier_jet``.
It replaces the two scaled Bessel carrier jets only when the complete ``z``
box lies in ``[0,4]``.  Crossing boxes are delegated to the historical
implementation, so a diagnostic cannot silently splice two formulae across
the branch boundary.  The adapter is quarantined and must not be used as a
K4/G2/G6 certificate.
"""

from __future__ import annotations

from flint import arb

from surface_remainder_arb_jet2 import Jet2, compose
from surface_bessel_entire_lowz import entire_outer_derivatives
import surface_remainder_carrier_jet as _historical

_ORIGINAL_A = _historical.a_scaled_jet
_ORIGINAL_B = _historical.b_scaled_jet
LOWZ_CALLS = {"A": 0, "B": 0}
FALLBACK_CALLS = {"A": 0, "B": 0}
Z_BOUNDS = {"lower": None, "upper": None}


def _record_z(z: arb) -> None:
    lo, hi = float(z.lower()), float(z.upper())
    if Z_BOUNDS["lower"] is None or lo < Z_BOUNDS["lower"]:
        Z_BOUNDS["lower"] = lo
    if Z_BOUNDS["upper"] is None or hi > Z_BOUNDS["upper"]:
        Z_BOUNDS["upper"] = hi


def _lowz_derivatives(z: arb, family: str) -> tuple[arb, arb, arb] | None:
    """Return ordinary derivatives only for a box wholly inside ``[0,4]``."""

    if z.lower() < 0 or z.upper() > 4:
        return None
    d = entire_outer_derivatives(z, family, order=2, terms=96)
    return d[0], d[1], d[2]


def a_scaled_jet(z: Jet2) -> Jet2:
    _record_z(z.c0)
    derivatives = _lowz_derivatives(z.c0, "A")
    if derivatives is None:
        FALLBACK_CALLS["A"] += 1
        return _ORIGINAL_A(z)
    LOWZ_CALLS["A"] += 1
    return compose(z, *derivatives)


def b_scaled_jet(z: Jet2) -> Jet2:
    _record_z(z.c0)
    derivatives = _lowz_derivatives(z.c0, "B")
    if derivatives is None:
        FALLBACK_CALLS["B"] += 1
        return _ORIGINAL_B(z)
    LOWZ_CALLS["B"] += 1
    return compose(z, *derivatives)


def install() -> None:
    """Patch the historical module for one explicitly isolated smoke run."""

    _historical.a_scaled_jet = a_scaled_jet
    _historical.b_scaled_jet = b_scaled_jet


def uninstall() -> None:
    """Restore the original functions after a diagnostic run."""

    # Reload is intentionally avoided: callers should run this adapter in a
    # short-lived process and never mix patched and authoritative imports.
    raise RuntimeError("run candidate adapter in a fresh process")


__all__ = ["a_scaled_jet", "b_scaled_jet", "install"]
