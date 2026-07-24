# G2 high-rescue timeout at the first post-102 cell

**Date:** 2026-07-24  
**Status:** `DESIGN_TIMEOUT`, no relay or G2/G6 promotion

The preregistered 300-bit rescue driver was run on the smallest unresolved
post-102 interval:

```text
python scripts/run_surface_scaled_bulk_cwin3p2_rescue300.py \
  --unit 102_102p03125_rescue300_codex \
  --lo 102 --hi 3265/32
```

The bounded execution was stopped by the 300-second wall-clock limit.  It
produced neither a production transcript nor a replay transcript, and no
temporary output was admitted.  The existing authoritative audit therefore
remains unchanged: the beta gap starts at `102`, the relay status is
`RELAY_LEMMA_UNPROVED`, and no manuscript slot may be removed on this result.

This is a computational limit of the current order-40/order-50, 300-bit
driver, not a sign counterexample.  A future attempt needs a separately
registered algorithmic change (cache/partition/order or a different signed
carrier), not an unrecorded increase of the timeout.
