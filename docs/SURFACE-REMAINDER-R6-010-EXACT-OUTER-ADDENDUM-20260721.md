# R6 tenth-birth exact-outer addendum

**Registered:** 2026-07-21, before the exhaustive run

The three-witness R6 probe exposed that the global Gaussian moving-band rate
is unusably coarse on the tenth birth.  This addendum admits one sharper,
still rigorous replacement: on each born `t` box use the lower endpoint
`c_min = cos(t_hi/4)` and the exact nonzero physical deficit
`w >= sin(physical_inner/2)^2`.  The resulting rate is propagated through
the existing positive polynomial majorant and outward incomplete-gamma tail.

The spatial outer derivative charge is the isolated adaptive delta-base
split in `surface_remainder_delta0_outer_domain_r6split.py`; every failed
interval is recursively subdivided and the absolute local coefficient bounds
are summed.  Evaluating only at `delta=0` is forbidden.

Acceptance for the next stage is strict: all 158 born boxes must pass the
R6 target with `margin_lower>0`, using exact monomial core moments,
production/replay byte identity, dependency hashes, and an order-free union
validator.  This remains a design lane until those artifacts exist; no gate
promotion is implied by the three-witness result.
