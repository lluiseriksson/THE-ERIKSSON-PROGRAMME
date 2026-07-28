# Sine-normalized finite-beta unit preregistration

**Status:** candidate-only; no G2/G6 promotion.

This unit freezes the remaining-gap beta box
`[101.8125,101.84375]=[3258/32,3259/32]` and uses:

- common positive normalization `J_1(beta_*)^4` at the beta midpoint;
- exact t-jet division by `sin(t)` for both Fourier families;
- CWIN `3/2`;
- beta order 40, t-order 45;
- 220-bit Arb and `min_dt=1/200000`;
- adaptive t subdivision from `3/5` to the frozen moving seam;
- independent production and byte-identical replay.

The stress boxes in the preceding preregistration pass strictly at order
40/45.  This unit is the first exhaustive test of the same fixed design.  A
green transcript remains candidate evidence until the union validator, tail
contract, exact splice, and independent claim audit are all complete.
