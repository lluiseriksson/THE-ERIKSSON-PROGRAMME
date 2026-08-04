# G2 mid-order cover width-1/2 failure

**Date:** 2026-07-22  
**Status:** `DESIGN_FAILURE; NO OUTPUT ADMITTED`

The first execution of the preregistered cover attempted the unit
`[193/4,195/4]` under the accidentally specified beta width `1/2`.  With
180-bit Arb, beta/t orders 20/25 and minimum `t` width `1/100000`, the
adaptive sign cover reached its minimum width near
`t=3.1044923904604693` and raised `mid-order cover failure`.  No transcript,
row or manifest was emitted for the unit.

The two feasibility probes that motivated the cover were `[193/4,97/2]` and
`[97/2,195/4]`, each of width `1/4`; they did not justify width `1/2`.  The
cover contract is therefore amended before any accepted rerun to width
`1/4`, with the fixed rational partition and 83 units recorded in the
companion preregistration.  This incident adds no G2 evidence.
