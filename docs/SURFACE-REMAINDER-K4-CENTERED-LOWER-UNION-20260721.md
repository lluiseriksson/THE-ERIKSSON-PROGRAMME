# K4 centred lower union audit (2026-07-21)

The six isolated candidate bands

```text
[0.0275,0.0280], [0.0280,0.0285], [0.0285,0.0290],
[0.0290,0.0295], [0.0295,0.0300], [0.0300,0.0305]
```

form an exact rationally adjacent local union. The executable audit
`scripts/audit_surface_remainder_k4_centered_lower_union.py` re-runs each
cell validator on production and replay, checks byte equality, adjacency and
strictly subunit fractions, and reports:

```text
units 6
cells 55296
domain 11/400:61/2000
worst nuD_main = 0.51010862419287...
```

This is only a local `t=2.9` candidate union. It supplies no regular-endpoint
patch, full `t` cover, overlap theorem, or literal global S1'''/S2''' judge;
K4 and G6 remain unpromoted.
