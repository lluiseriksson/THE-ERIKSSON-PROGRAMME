# CWIN=3/2 high-order campaign [74,78] — preregistration

**Registered before the campaign reruns:** 2026-07-21

This campaign tests the order-30, `t_order=37`, 180-bit Arb backend on the
fixed rational boxes

```text
[74+i/4, 74+(i+1)/4],  i=0,...,15.
```

For every box, production and replay use

```text
python scripts/run_surface_scaled_bulk_cwin3p2_high_unit.py \
  --unit high_<box> --lo <lo> --hi <hi>
```

The required scaled `t` domain is `[3/5, pi-(3/2)/beta]`.  Midpoint
subdivision is deterministic, with `min_dt=1/100000`; every terminal row must
have an outward-rounded strict upper bound below zero.  The validator requires
the production and replay transcripts to be byte-identical and to carry the
registered dependency hashes.

The box `[74,297/4]` already has a separate preregistration and is included
here only as the first member of the fixed partition.  A passing row archive is
candidate evidence for the pointwise sign only.  It does not prove the global
beta union, the sign-to-`H_tail` relay, K2/K4, S1'''/S2''', G2, or G6, and no
manuscript slot may be removed from these outputs.
