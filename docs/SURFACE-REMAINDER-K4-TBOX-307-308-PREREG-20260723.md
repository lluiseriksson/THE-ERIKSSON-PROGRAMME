# K4 t-box candidate pre-registration: `[3.07,3.08]`

**Status:** candidate-only design; no gate promotion.

Frozen configuration: `delta=[1/25,81/2000]`, `t=[307/100,77/25]`,
`seed_grid=12`, `max_cells=2304`, Arb precision 140 bits, with independent
byte-identical production and replay transcripts.  The validator must check
all seven literal carrier fractions are `<1`.

Even a passing box supplies only a local candidate witness.  It does not
close K4, S1'''/S2''', G2, or G6; the global t union, overlap, low-z, moving
boundaries, and outer-tail obligations remain in force.
