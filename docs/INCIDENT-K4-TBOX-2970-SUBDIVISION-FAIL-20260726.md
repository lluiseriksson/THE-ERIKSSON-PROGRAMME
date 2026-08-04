# K4 t-box subdivision failure near t=2.97 — 2026-07-26

The width-`0.005` box `[2.97,2.975]` failed with
`nuD_main≈1.03915`.  The registered width-`0.0025` repair was then run on
both adjacent boxes, with byte-identical production/replay in each case:

```text
[2.97,2.9725]:  nuD_main = [1.00437351348503 +/- 3.47e-15]
[2.9725,2.975]: nuD_main = [1.01210220711619 +/- 3.21e-15]
```

Both remain above the fixed budget.  Their transcripts are retained in
`scripts/surface_remainder_k4_tbox_2970_29725.txt` and
`scripts/surface_remainder_k4_tbox_29725_2975.txt` (and replay companions),
but no positive manifests are generated.  This retires blind t-subdivision
as a completion strategy for this strip: a new analytic majorant or a
different carrier representation is required for global K4/S1'''/S2'''.
