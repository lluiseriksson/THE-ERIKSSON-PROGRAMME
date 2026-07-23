# K4 low-z entire-series majorant: preregistration

**Registered:** 2026-07-23, before implementation

This design supplies value/derivative enclosures for the scaled Bessel
families used by the centred K4 carrier when `0 <= z <= 4`.  It uses the
positive entire series for `I_1(z)/z` and `I_2(z)/z^2`, with an explicit
geometric tail at 32 terms and ordinary derivatives through order four after
the factor `exp(-z)`.  The check must compare the resulting intervals with
independent Arb evaluations at exact stress points and reject non-finite or
non-containing enclosures.

This is only a low-z dependency repair.  It carries no K4, S1'''/S2''', G2,
or G6 promotion until a complete regular-ball delta/t union, outer-tail
bound, overlap certificate, and independent production/replay are supplied.

## Analytic enclosure contract

The endpoint hull is licensed by the complete-monotonicity identity, not by
an unrecorded numerical monotonicity guess.  For `nu=1,2`,

`z^(-nu) exp(-z) I_nu(z) = c_nu * integral_0^2 exp(-z*u)
 [u*(2-u)]^(nu-1/2) du`,

with `c_nu>0`.  Hence every ordinary derivative has sign `(-1)^n` and is
strictly monotone on `[0,4]`; the hull of the endpoint values is therefore
the exact range.  The implementation must still retain the positive-series
tail after differentiating through order five.  Order five is required to
justify monotonicity of the reported order-four enclosure.  The direct Arb
value checks and sign checks are recorded by
`validate_surface_k4_lowz_entire_majorant.py`.
