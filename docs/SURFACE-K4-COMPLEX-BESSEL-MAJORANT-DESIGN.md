# Complex Bessel majorant for the regular-ball design

**Status:** `DESIGN_ONLY`; no K4, S1'''/S2''', G2, or G6 promotion.

This note records an elementary majorant that may remove one source of
dependency loss in the regular-ball route.  It is not a certificate for the
remaining spatial or tail union.

For the modified Bessel function

\[
 I_0(z)=\sum_{k\ge0}\frac{(z/2)^{2k}}{(k!)^2},
\]

the coefficients are nonnegative.  Therefore, for every complex `z`,

\[
 |I_0(z)|\le \sum_{k\ge0}\frac{(|z|/2)^{2k}}{(k!)^2}=I_0(|z|).
\]

Whenever `I_0` is nonzero on a simply connected disk, any holomorphic branch
of `log I_0` satisfies

\[
 \Re\log I_0(z)=\log|I_0(z)|\le \log I_0(|z|).
\]

The same argument applies to `I_1`, whose power series also has nonnegative
coefficients after factoring its positive linear term.  This is an exact
analytic inequality, not an interval-convergence claim.

The nonvanishing side condition must still be certified.  A sufficient scalar
check on a disk `D(x_0,r)` with `x_0>0` is

\[
 I_0(x_0)-r\,I_1(x_0+r)>0,
\]

because `I_0'=I_1` and the same coefficient majorant bounds `|I_1(z)|` by
`I_1(|z|)`.  This check only legitimizes the logarithm; it does not bound the
full K4 integrand, moving boundaries, or the outer tail.

For interval implementation, boxes touching the real axis must not be judged
by a strict gap: equality holds for real nonnegative `z`.  Use the exact
majorant above there, and reserve direct interval evaluation for boxes at a
positive distance from the axis.  If a quantitative gap is required, write
`g(x,y)=log I_0(|x+iy|)-log|I_0(x+iy)|`; conjugation symmetry gives
`g(x,0)=0` and evenness in `y`, so an axis-adjacent Taylor model should certify
`g/y^2` rather than divide an interval containing zero by `y^2`.

The next executable check should record only the scalar nonvanishing margin
and the resulting Bessel majorant.  It must not alter the gate board until the
majorant is integrated with the physical carrier, chart boundaries, and both
tails.
