# Naive weighted-judge box enclosure blows the registered budgets — 2026-07-23

This is a negative design diagnostic for the literal `S1'''` weighted
remainder route.  It is not a K4, `H_tail`, G2, or G6 result.

## Reproduction

The run used the committed `scripts/surface_remainder_weighted_judge_design.py`
at git head `6b9a7b7d4b9c54ac8be84cdb0002aea3e38279f0` (SHA-256
`0cff7c2c9c8c4ed59518f225fb2cb927e4123d38121a15483033cb3fe790f5dc`), the
pinned Python/Arb runtime, `ctx.prec=100`, and:

```text
full_second_bounds(lo=0.05, hi=0.055, core_grid=8, complement_grid=8)
```

The resulting absolute second-derivative enclosures and ratios to the frozen
budgets were:

```text
muF_main   850790901.893076365   ratio 32145347.10745745
MD_mirror  155818556.710236272   ratio 2743236.152712739
MF_mirror  58680227.9655018456   ratio 375481.36655683290
nuD_main, nuF_main, MD2r_mirror, MDFr_mirror: nan
```

## Interpretation

The direct interval hull over the present localized/complement boxes is many
orders of magnitude too wide (and returns `nan` for four carriers).  This does
not disprove the underlying inequalities; it rejects this unweighted
whole-box enclosure as a viable certification architecture.  A successful
route must introduce cancellation-aware scaled coordinates, a sharper
partition, or a separately proved analytic carrier majorant before any
`S1'''/S2'''` promotion can be considered.

No manuscript state, gate state, or candidate manifest was changed by this
diagnostic.
