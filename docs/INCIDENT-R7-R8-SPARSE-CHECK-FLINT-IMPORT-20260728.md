# R7/R8 sparse checker Flint-import incident (2026-07-28)

After repairing the script-path issue, the second alternate-runtime
invocation stopped before derivation because
`surface_bessel_integral_remainder.py` imports `python-flint` globally even
when the caller needs only its exact `Fraction` coefficients.

The traceback is preserved at
`outputs/surface-r7-r8-sparse-exact-target-FAILED-FLINT-IMPORT-20260728.stderr.txt`.
It is an import-layer failure and carries no mathematical evidence.

The exact rational companion coefficients and frozen Y targets have now been
split into dependency-free modules.  The Arb remainder implementation remains
unchanged; the sparse symbolic checker imports only the pure modules.
Production restarts from empty authoritative output.  No gate or manuscript
claim changes.
