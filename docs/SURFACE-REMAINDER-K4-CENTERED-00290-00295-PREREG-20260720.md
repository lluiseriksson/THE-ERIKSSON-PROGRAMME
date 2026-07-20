# K4 centred band `[0.0290,0.0295]` preregistration

Registered before reading the production output. This is a candidate-only
continuation of the clean centred fixed-domain integrator; it carries no K4,
G2, G6, S1''' or S2''' promotion.

## Frozen contract

```text
unit       k4_00290_00295
delta      [29/1000, 59/2000]
t          29/10
seed_grid  12
max_cells  9216
precision  140 Arb bits
```

The implementation is isolated in
`scripts/certify_surface_remainder_k4_centered_00290_00295.py`; production
and replay use the corresponding runner and validator. The existing frozen
centred integrator is imported without modification. Refinement and fallback
rules are identical to the already manifested `[0.0295,0.0300]` witness.

## Decision rule

Production and independent replay must be byte-identical. The validator must
recompute all seven totals from the recorded terminal cells, verify finite
enclosures, matching dependency hashes, and strict fraction `< 1` for every
carrier. Any failure is retained as a negative design result and does not
change the gate board.

Even a passing pair proves only this one local band at `t=2.9`; the regular
endpoint, the remaining delta cover, the full `t`-union, overlap, and literal
weighted S1'''/S2''' judges remain open.

## Result

Production and replay both completed with 9,216 terminal cells and 262
fallback cells. The byte-identical SHA-256 is
`848345bbecb3296a0564414309e161535c72358eff83206b2ba1f4c13dda6e22`.
The largest normalized fraction is `muF_main = 0.232586926083349...`; all
seven fractions are strictly below one. The candidate manifest is
`run-manifests/surface-remainder-k4-centered-00290-00295-20260720.json`.
This is a local witness only and leaves the gate board unchanged.
