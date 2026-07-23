# Common positive scaling preregistration for the finite-beta seam

**Status:** design-only; no G2/G6 promotion.

The high-order scaled bridge loses absolute resolution near the moving seam
because every coefficient carries the common factor `exp(-4 beta)`.  This
experiment fixes a second, beta-box-local positive normalization before any
new output is read:

\[
 s_0=J_1(\beta_*)^4,
 \qquad J_m(\beta)=e^{-\beta}I_m(\beta),
 \qquad \widetilde a_m=a_m^J/s_0,
 \quad \widetilde b_m=b_m^J/s_0,
\]

where `beta_*` is the exact midpoint of the frozen beta box.  Since `s_0>0`
is constant with respect to both `beta` and `t`, the exact identity is

\[
 \widetilde W=W^J/s_0^2.
\]

Thus the sign predicate is unchanged, while all beta and t derivatives are
scaled by the same positive constant.  The implementation must scale the
finite coefficient jets, their Fourier-tail majorants, and every absolute
derivative sum used by the Taylor remainder.  It may not change the mesh,
orders, stopping rule, CWIN, or beta endpoints.

The first frozen diagnostic is the previously unresolved box
`[101.8125,101.84375]`, with the standard high contract
`CWIN=3/2`, beta order 30, t order 37, 180-bit Arb, and `min_dt=1/100000`.
A pass remains candidate evidence only and requires an independent replay and
validator.  A failure or timeout is retained as an incident.  This scaling
does not address the separate sign-to-`H_tail` relay.
