# Direct-sign unit `[251/4,65]` timeout — 2026-07-23

## Scope

I preregistered a fresh CWIN=3/2 high-order sign-row unit with
`beta_order=30`, `t_order=37`, `min_dt=1/100000`, and 180-bit Arb precision,
covering the seam block `[251/4,65]`. The intended purpose was only to fill
candidate gaps in the direct `W^J<0` archive.

## Result

The production command

```text
python scripts/run_surface_scaled_bulk_cwin3p2_high_unit.py \
  --unit codex_62p75_65_20260723 --lo 251/4 --hi 65
```

was allowed 600 seconds and timed out without producing a committed
transcript. No partial output, manifest, or coverage credit is retained. The
replay was therefore not attempted.

This is a computational feasibility failure only; it neither proves nor
disproves the sign inequality. The direct-sign audit and the G2 relay remain
unchanged, and no K2/K4/G2/G6 promotion is made.

The narrower subunit `[251/4,253/4]` was then attempted with the same
configuration and a 360-second allowance. It also timed out before producing
production output. This rules out the current high-order driver as a practical
way to close these seams by brute-force subdivision; a different certificate
or analytic majorant is required.
