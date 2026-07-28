# K4 t-box [2.94,2.95] boundary failure — 2026-07-26

The generic endpoint t-box driver was run with the frozen contract on
`t=[2.94,2.95]` and delta boxes `[0.048,0.049]`, `[0.049,0.05]`.  Production
and replay transcripts are byte-identical, but the validator correctly
rejects the box because the aggregate second segment has

```text
nuD_main = [1.01597038201752 +/- 1.50e-15]
```

The other six rows remain strictly below one.  The complete transcripts are
retained as a negative design witness in
`scripts/surface_remainder_k4_tbox_294_295.txt` and its `_rerun` companion;
no positive manifest was generated.  The preceding boxes through
`[2.93,2.94]` pass, so this is the first observed boundary of the current
fixed-delta/t-box architecture.  A narrower t partition, stronger spatial
majorant, or analytic interpolation lemma is required; no K4 or
S1'''/S2''' promotion follows.
