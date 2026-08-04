# R6 tenth-birth exact-outer cover result

The preregistered exact-monomial core plus adaptive split outer wrapper was
run over all 158 born `t` boxes on `delta in [0,1/100]`.  Production and an
independent replay are byte-identical:

```text
production/replay SHA-256 = 222DF0569E96050DAB05AABF4738BE3237ED79B1F16C36145EC02706FB41DC0F
rows = 158, pass_count = 158
worst margin_lower = 5919.975343772661672451132482499288402819 (index 5)
```

The validator recomputes the row coverage and all dependency hashes.  The
local t-dependent physical-deficit rate is the decisive improvement over the
rejected global moving-band majorant; every row remains strictly below the
registered budget `7600`.

This is not a gate promotion.  The manifest is explicitly
`DESIGN_COVER_PASS_NO_PROMOTION`: G2 still needs the finite-beta relay and
contract review, the G5 moving wedge must be spliced for this birth, later
positive births remain open, and G6 still requires the literal weighted
S1'''/S2''' union plus manuscript seal.
