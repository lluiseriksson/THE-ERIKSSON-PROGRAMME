# Surface remainder localized core — L1/L2 result

**Date:** 2026-07-11
**State:** `DESIGN_PASS`; `K4_OPEN`; `S1_S2_OPEN`

The pre-registered localization in `SURFACE-REMAINDER-PREREG.md` has an
executable Arb implementation:

- `scripts/surface_remainder_arb_jet2.py`;
- `scripts/surface_remainder_carrier_jet.py`;
- `scripts/surface_remainder_centered_prefactor.py`;
- `scripts/surface_remainder_core_l2_arb.py`.

The implementation differentiates the exact Bessel recurrences and evaluates
orders 0--4 by complete-monotone endpoint hulls. It uses positive square
forms for the chart radius and a dedicated square enclosure when an Arb ball
crosses zero. All seven delta-second carriers and their spatial Hessians were
checked against independent multiprecision differentiation during design.

The manifested production run at `(delta,t)=(1/15,2.9)` gives:

```text
mirror64: MD 6.31, MF 4.00, MD2r 4.82, MDFr 4.73
main128:  muF 2.88, nuD 0.835, nuF 2.61
```

against global bucket scales

```text
mirror: 56.801, 156.28, 12.577, 44.352
main:   26.467, 0.94119, 8.1751.
```

Thus L1 finiteness and the L2 localized-core design gate pass. This does not
bound the complementary integrals, their cutoff derivatives, the moving
physical-boundary terms, the analytic `delta=0` patch, or the weighted sums.
Consequently `(H_cube)`, `(H_tail)`, G1, and G2 remain open. The only terminal
judges remain the literal S1'''/S2''' sums after K2/K4.
