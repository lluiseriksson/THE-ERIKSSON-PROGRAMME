# Incident G2 — high-order gap probes timed out

**Date:** 2026-07-24  
**Status:** negative engineering evidence; no promotion

The registered high-order CWIN=`3/2`, order-30/t-order-37 driver was tested on
the first unresolved finite-beta component after the existing `[80,81]`
archive:

```text
beta=[81,81.25]       timeout 180 s
beta=[81,81+1/16]     timeout 300 s
```

Both commands were run against the current checkout with the recorded Arb
environment.  Neither produced a terminal transcript or a sign verdict; the
process was stopped by the enclosing timeout.  These are not mathematical
failures and they are not evidence of positivity or negativity.  No output was
added to a manifest and no existing archive was overwritten.

The result is an engineering constraint: a quarter-width or naive narrow-box
campaign with this evaluator is not an admissible closure route without a
separate performance/partition design.  The G2 relay audit therefore remains
unchanged, with gaps `[193/4,225/4]`, `[241/4,69]`, `[81,401/4]`, and
`[1635/16,1000/9]`, and with `RELAY_LEMMA_UNPROVED`.  A future attempt must be
pre-registered with an explicit cost bound and must still supply production,
independent replay, current dependency hashes, exhaustive adjacency, and the
separate absolute `(H_tail)` implication.
