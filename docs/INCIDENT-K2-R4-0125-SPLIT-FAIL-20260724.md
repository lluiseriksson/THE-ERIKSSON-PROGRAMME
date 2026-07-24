# Incident: exact-r4 probe fails at `delta_max=1/80`

**Date:** 2026-07-24  
**Scope:** design-only positive-delta K2 lane; no `(H_tail)`, G2, or G6 load.

The pre-registered three-witness probe
`scripts/surface_remainder_delta0_r4_extension_0125_split_probe.py` was run
with `--split-index 0`, using the registered physical split `1181/1000`,
`delta_max=1/80`, and witnesses `(0,384)`, `(50,192)`, `(157,384)`.

It completed all three witnesses, but every outward margin was negative:

```text
index 0   margin_lower <= -33640.261918861824874...
index 50  margin_lower <= -33695.083853974003895...
index 157 margin_lower <= -14173.186534919870899...
```

The dominant reported `C_value` terms were approximately
`2.153e8`, `2.157e8`, and `9.070e7`, respectively.  The result is therefore
`R4 0125 SPLIT DESIGN FAIL`, not a timeout and not a sign counterexample.
No transcript, replay, or terminal manifest was produced.  The split and
this exact-r4 whole-box architecture are rejected for the `1/80` birth; any
retry requires a separately registered analytic or enclosure change.
