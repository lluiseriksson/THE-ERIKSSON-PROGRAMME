# Scaled-bulk cancellation diagnostic — 2026-07-21

## Status

Diagnostic only.  This note carries no G2 or G6 load and does not alter the
gate board.  The remaining scaled seam is still unsealed.

## What was corrected

The first exploratory implementation converted `math.sin`/`math.cos`
binary64 values into Arb balls.  At the beta values in the open seam this
introduced a 53-bit angular input floor, exactly where the Wronskian is
exponentially small.  The implementation now evaluates every `sin(m*t)` and
`cos(m*t)` in Arb at the active precision.  The corrected script is
`scripts/probe_surface_scaled_bulk_cancellation.py` (SHA-256
`453EDC229ADE3B42A3930CB4C0E8376E57E16C4A409C9ABCD57A0820757159E8`).

## Corrected finite-sum probe

At `ctx.prec=180`, the 25 registered beta points
`1629/16 + i/16`, `0 <= i <= 24`, and 121 t samples per beta produced:

* `positive = 0`, `negative = 3025` for the direct finite sum;
* worst reported cancellation index `kappa = 181.1427380769523`;
* the smallest reported `|W|` was `1.2560e-108`, at the moving right edge.

The earlier `857/2168` sign split was therefore an input-precision artefact,
not evidence of a counterexample.  This remains a floating-point/sample
diagnostic: finite truncation and endpoint suppression are not enclosed.

## Pairwise sanity route

`scripts/probe_surface_scaled_bulk_pair_sanity.py` (SHA-256
`53131DAA78B0C76E60B76F4F3563232E91FFE7201698D7FECDA5EC9F8B3C59C2`)
evaluates the exact finite identity

`W = 2 * sum_{m<n} (a_m b_n-a_n b_m)
       (m cos(mt) sin(nt)-n sin(mt) cos(nt))`.

At `t=0.8,1.5` the direct and pair forms agree to the displayed precision at
100, 180, and 260 Arb bits.  Near the moving endpoint they become badly
conditioned (the pair form is often an Arb ball containing zero), so the pair
identity is a route for regrouping, not a certificate by itself.

## Consequence for the next proof step

The correct next implementation is an Arb/Taylor evaluator with (i) Arb
trigonometric jets, (ii) a certified coefficient/tail budget, and (iii) a
right-edge factorization by `(pi-t)^2`.  Direct sampled signs cannot promote
G2.  A future registered run must first calibrate the same evaluator in a
closed beta strip, then certify `B>0`, and only then decide the sign of `W`.

