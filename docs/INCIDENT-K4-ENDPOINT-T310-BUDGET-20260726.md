# K4 endpoint strip t=3.10 budget boundary — 2026-07-26

The centred fixed-domain endpoint integrator was probed with the same
contract as the scoped t=2.9 and t=2.95 witnesses: delta boxes
`[0.048,0.049]` and `[0.049,0.05]`, spatial limits 2304/1152, and seven
literal weighted rows.

The first box remains strictly below one in every row.  The second box also
passes six rows, but `nuD_main` has outward fraction

```text
[1.09872381553627 +/- 4.16e-15]
```

and therefore fails the fixed budget.  This is a design diagnostic only; no
transcript or manifest is promoted from the probe.  It shows that the existing
endpoint strip cannot simply be extended to the full t-range by reusing the
same two delta boxes and budget.  A genuine t partition or a new analytic
majorant is required before any K4/S1'''/S2''' promotion.
