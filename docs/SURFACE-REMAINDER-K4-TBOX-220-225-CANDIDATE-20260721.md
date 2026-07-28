# K4 candidate t-box extension: `[11/5,9/4]`

The centred fixed-physical integrator was rerun on

```text
delta = [1/25,81/2000],  t = [11/5,9/4],
seed_grid = 12, max_cells = 9216, Arb precision = 140 bits.
```

Production and replay use the same frozen HEAD and are byte-identical. The
validator checks all 9,216 cells, dependency hashes, finite values, and the
seven literal carrier fractions. The worst fraction is
`MD2r_mirror = 0.893169468797528...`, so this box is strictly subunit.

This is a single candidate t-box only. It does not provide the regular-ball
endpoint patch, a full delta/t cover, the overlap proof, or the weighted
S1'''/S2''' union; `NO_K4_PROMOTION` therefore remains unchanged.
