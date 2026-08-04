# Incident: first real-axis K4 stress probe hits the existing Bessel gap

The pre-registered positive-delta diagnostic
`scripts/probe_surface_k4_ball_reach_realaxis.py` was run from commit
`d3b3d415595f1eaa3f70d359893448cf3e7a7fa1` at 140 Arb bits.

Frozen configuration: `t=29/10`, `delta=[1/100,1/15]`, scaled square
`[-4,4]^2`, grid `8x8`. The first cell terminates with

```text
K4 REALAXIS DOMAIN_GAP (0, 0, centred K4 Bessel cell lies in unproved gap 4<z<20)
```

This is a domain-partition failure, not a mathematical counterexample. The
existing `scaled_bessel_jet` backend requires a cell to lie wholly in one of
the certified `z<=4`, `4<=z<=20`, or `z>=20` branches; the frozen whole cell
crosses the unproved branch boundary. No totals, K4 claim, S1'''/S2'''
judge, or G6 state are changed. A future attempt must first preregister an
explicit low-z partition or a new certified branch; silently subdividing this
run would invalidate its frozen contract.
