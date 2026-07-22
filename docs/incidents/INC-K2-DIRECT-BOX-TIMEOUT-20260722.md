# Incident: direct positive-K2 box judge remains nonterminal

**Date:** 2026-07-22  
**Status:** `DESIGN_TIMEOUT`; no K2/G2 promotion

The registered direct judge was exercised on the representative box

```text
delta = [0.001, 0.0015]
t     = [1.00, 1.02]
```

The first attempt exposed an implementation error: the centered pilot
enclosure contained zero in its `KD` leading coefficient, so forming `KF/KD`
raised `leading term in denominator is not nonzero`.  The runner was repaired
to use the exact zero calibration when the pilot does not separate `KD`; this
is a conservative gauge choice, while the independent pointwise `KD` floor
remains separate.

The repaired run then exposed the registered spatial contract honestly.  The
8x8 auxiliary mesh failed the `linear-moment Taylor tail is not contractive`
guard, so the runner advanced through the frozen 16, 24, and 32 meshes.  Even
the resulting single-box execution exceeded the 900-second wall-clock limit
without producing a terminal margin or transcript.  No output row, budget, or
coverage claim is inferred from the timeout.

The calibration fallback is regression-tested in
`tests/test_surface_remainder_positive_calibration.py`.  A future production
route needs a faster cancellation-preserving integrator or a preregistered
analytic majorant; brute-force repetition of this direct box judge is not a
credible route to the 49-by-158 K2 union.
