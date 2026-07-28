# G2 direct-sign candidate preregistration: beta `[85,85.25]`

This record freezes one bounded continuation of the CWIN=`3/2` scaled bulk
campaign before execution.  The target is the strict sign of the scaled
Wronskian `W^J` on

```text
beta in [85, 341/4],
t in [3/5, pi - (3/2)/beta],
```

using the existing high-order backend, production/replay pair, and an
independent transcript validator.  The unit is candidate evidence only.  It
does not promote G2/G6, does not assert `(H_tail)`, and does not alter K2/K4.

Frozen command shape:

```text
python scripts/run_surface_scaled_bulk_cwin3p2_high_split.py \
  --unit 85_85p25_20260725 --lo 85 --hi 341/4
```

The required checks are: CWIN=`3/2`, outward-rounded Arb enclosures, ordered
`trow` partition covering the complete moving-endpoint domain, strict negative
upper bounds, production/replay equality, dependency hashes, and a fresh
validator pass.  Any timeout or nonnegative row is recorded as an incident;
there is no fallback promotion.

