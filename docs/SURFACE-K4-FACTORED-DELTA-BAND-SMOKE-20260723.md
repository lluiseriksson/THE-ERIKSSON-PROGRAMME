# Factored one-sided delta-band smoke — 2026-07-23

The isolated candidate driver
`scripts/probe_surface_k4_factored_delta_band.py` evaluates the centred-delta
scaled core on the one-sided band
`delta=[0.0660,0.0661]`, `t=2.9`, with 256 adaptive cells and the low-z Bessel
dispatcher.  It uses the cancellation-safe Taylor weight
`(hi-lo)(delta_final-(hi+lo)/2)` from the separate factored helper.

Production and replay are byte-identical and pass
`scripts/validate_surface_k4_factored_delta_band.py`.  The largest recorded
weighted fraction is `nuD_main=0.0003439366459453`.  This is a narrow scaled
core band only: the moving outer band, the remaining delta range, the global
`t`-union, and the literal S1'''/S2''' judges are absent.  The manifest is
`run-records/legacy/surface-k4-factored-delta-band-0660-0661-20260723.json` and
explicitly carries `promotion: NONE`.
