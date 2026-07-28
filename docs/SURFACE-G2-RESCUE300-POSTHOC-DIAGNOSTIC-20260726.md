# G2 300-bit narrow rescue — post-hoc diagnostic

Date: 2026-07-26  
Status: diagnostic only; deliberately not admitted to the candidate union.

After the 180-bit high-split box of width `1/512` failed, the existing
300-bit/order-40/50 rescue lane was run on the same narrow beta interval:

```text
beta = [3409/32,54545/512]
CWIN = 3/2; Arb = 300 bit; MIN_DT = 1/100000
```

It produced 235 strictly negative adjacent `t` rows.  The subsequent replay
was byte-identical and the existing independent validator reported:

```text
CWIN3P2 RESCUE300 VALIDATION PASS gap106p53125_106p533203125_r300 t_rows 235
```

The transcripts are retained as
`scripts/surface_scaled_bulk_gap106p53125_106p533203125_r300.txt` and its
`_rerun.txt` pair.  This run was launched before a dedicated preregistration
for this exact unit, so it is intentionally classified as post-hoc diagnostic
evidence and carries no G2/G6 load.  It does not justify extrapolating the
300-bit lane to the full residual `[3409/32,1000/9]`; every additional beta
unit would require its own preregistration, production/replay pair, and
independent audit.

