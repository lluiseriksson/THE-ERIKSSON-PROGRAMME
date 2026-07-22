# Finite-bridge identity and seam check

The executable `scripts/verify_surface_finite_bridge_splice_identity.py`
checks two exact prerequisites of a possible direct finite-bridge relay:

1. If every Bessel coefficient is scaled by `q=exp(-4 beta)`, then
   `W_scaled=q^2 W=exp(-8 beta)W` and the ratio `F_A/(2F_B)` is unchanged.
2. With the registered rational enclosure `pi_hi=31415927/10000000`, the
   regular interval `[0,313/100]` overlaps the moving G5 wedge for every
   `delta in [9/1000,1/100]`; the edge is already below `313/100` at the
   left endpoint and decreases with `delta`.

The check is deliberately narrow.  It supplies no Wronskian sign, no
finite-tail domination, no `H_tail` implication, and no G2/G6 promotion.
