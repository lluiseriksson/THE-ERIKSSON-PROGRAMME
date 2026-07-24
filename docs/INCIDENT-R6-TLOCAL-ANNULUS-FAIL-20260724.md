# R6 t-local annulus diagnostic — still fails the tenth K2 birth

**Date:** 2026-07-24  
**Status:** `DESIGN_FAIL`, no K2/G2/G6 promotion

The R6 annulus majorant was rerun with the actual born `t` interval carried
through the nominal moment engine, instead of the previous global hull
`t∈[0,π]`.  This is a valid outward-rounded refinement of the diagnostic
only; the spatial domain, physical split, endpoint tail, companion charge,
and target remain unchanged.

Reproduction (repository root, with the standard `PYTHONPATH`):

```text
python scripts/probe_surface_remainder_r6_annulus_single.py --index 0 --grid 96
R6 ANNULUS-INCLUSIVE SINGLE-BOX PROBE 0 t 0 1/50 grid 96
RESULT radius 59/5
head [0.073277502177734277211129665374755859375000 +/- 3.61e-44]
Y5 [18796.033330809000517547247000038623809814 +/- 4.54e-37]
value [0.4633930901948809869439715305758582687474 +/- 3.94e-41]
margin_lower [-11196.496723899195398534190971569199668083 +/- 2.19e-37]
R6 ANNULUS-INCLUSIVE SINGLE-BOX FAIL
```

The local-`t` repair reduces the companion value charge dramatically, but the
annulus-inclusive order-five coefficient remains larger than the registered
target `7600`; the margin is strictly negative.  Thus the earlier exact-outer
158-row pass remains quarantined for the same reason: it omitted the annulus.
The next admissible K2 attempt must preserve signed carrier cancellation (or
change constants under a new pre-registration); finer interval partitioning
alone is not a closure.
