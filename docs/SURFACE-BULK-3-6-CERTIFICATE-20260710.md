# Compact bulk certificate `[3,6]`

The canonical plain-mode Arb run certifies

\[
 W(t,\beta)<0\qquad(3\leq\beta\leq6,
 0.6\leq t\leq\pi-\tfrac{3}{2\beta}).
\]

It contains 3472 adjacent beta boxes (2528 of width `0.001` and 944 of
width `0.0005`, after one recorded refinement at `beta=5.528`) and 592,068
outward-rounded t boxes. The moving boundary uses the upper beta endpoint
and the rational upper bound `PI_UP=31415927/10000000`, so the wedge is
covered without an endpoint under-approximation.

The transcript is the historical canonical output committed in
`31663045ec3482f81b3577cbf491d706c7668de1`. Its script and output hashes,
environment, and command are recorded in
`run-manifests/surface-bulk-3-6-20260710T072307Z.json`; the executable
validator is `scripts/validate_surface_bulk_3_6.py`.

Scope is deliberately local: this closes only the formerly amber compact
bulk row. It supplies no evidence for the scaled finite bridge, `H_tail`,
the moving-edge splice, or the global paper seal.
