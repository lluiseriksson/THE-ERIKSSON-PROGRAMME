# INC-K2 — rejected hybrid parameter jet in the positive-box prototype

**Opened:** 2026-07-12  
**Status:** `CONTAINED`; `PROTOTYPE_REPAIRED`; `TERMINAL_CERTIFICATE_PENDING`

## Finding

The first `surface_remainder_positive_t_centered.py` prototype stored a
moment's value enclosure at the centre of a `t` box together with a first
derivative enclosure on the complete box, then passed that hybrid object
through the nonlinear quotient assembly.  That is not a closed jet algebra:
the product rule for a box derivative needs box value enclosures for both
factors.  A centre value cannot be substituted merely because it is tighter.

The affected runs were design runs only.  They were not manifested, cited by
the paper, or used to close a gate.  In particular, the compact right-edge
certificate and the sealed K2 endpoint certificate use different programs
and are unaffected.

## Containment

1. The two long hybrid-jet design runs were stopped/rejected.
2. `surface_remainder_tjet.py` now carries ordinary derivatives through
   order two and has direct chain-rule tests.
3. Centre and whole-box tracks are integrated and assembled nonlinearly in
   separate calls.  Only after both quotient assemblies are complete does
   the terminal judge apply

   ```text
   |R(t)| <= |R(t0)| + h |R'(t0)| + h^2 sup_box |R''| / 2.
   ```

4. A regression test verifies that `residual_box` requests two separate
   tracks and applies the second-order Taylor charge only at the terminal
   level.

No K2 positive-box result may be promoted until a finite outward-rounded
run of this repaired program, the order-six Bessel companion charge, and the
sixth delta-Taylor charge jointly pass the preregistered budget.
