# Weak-main floor-grid-48 diagnostic — preregistration (2026-07-28)

This is a diagnostic evidence-quality pass, not a theorem gate and not a
replacement for either canonical weak-main certificate.

## Motivation

The canonical runner stops at the first grid whose lower enclosure clears
`-1/20`.  Its reported `WORST_LOWER` is therefore biased toward boxes that have
only just cleared the decision threshold.  It measures the adaptive stopping
artifact, not the analytic margin of `X_main`.

`GRID_COUNTS` and the adaptive `WORST_LOWER` are reproducibility facts for the
recorded Python/flint/Arb binary and must not be presented in the paper as
mathematical constants or platform-stable margins.

## Frozen diagnostic

After both canonical near/far production/replay pairs independently validate:

1. select every row accepted at grid 24 in the canonical transcripts;
2. recompute each selected box at fixed grid 48, with the same 180-bit
   arithmetic, companion order, tail charges, and rational box endpoints;
3. retain the canonical grid-48 and grid-96 enclosures for all other boxes;
4. report the worst explicit lower endpoint in the combined evidence.

The result is called a **floor-grid-48 diagnostic**.  It is not a uniform
grid-48 run because the far boxes that required grid 96 remain at grid 96.

If any selected box errors or its grid-48 lower endpoint fails to improve its
grid-24 lower endpoint, print the complete diagnostic failure map and do not
quote a combined margin.  If this diagnostic is cited in the manuscript, it
requires byte-identical production and replay outputs, empty stderr, and
current dependency hashes.  Regardless of its result, the theorem continues
to consume only the preregistered strict predicate `X_main>-1/20`.

No acceptance cushion is retrofitted into the current certificate.  A future
certificate version may preregister a platform-robust stopping cushion such as
`lower > target + 1/1000`.
