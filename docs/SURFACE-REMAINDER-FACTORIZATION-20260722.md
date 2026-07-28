# Exact carrier factorization (2026-07-22)

## Status

`ALGEBRAICALLY_VALIDATED`; design support only.  This note carries no K4,
S1'''/S2''', G2, or G6 promotion.

For `u = cos(s)`, `v = cos(alpha)`, and
`c_c = 2 cos(t/4)^2 - 1`, the carrier code uses

\[
d=u+v,
\qquad
n=c_c(2u^2-1)+v(c_cu-1+u^2),
\]

and the exact identity

\[
n-c_cd=(u-1)\bigl[c_c(2u+1)+v(u+c_c+1)\bigr].
\]

The mirror chart is the same identity with `u = -cos(s_j)` and
`v = -cos(alpha_j)`, equivalently

\[
(x+1)\bigl[c_c(2x-1)+y(c_c+1-x)\bigr].
\]

The factored form is used in the centred/scaled carrier paths and in the
delta-jet prefactor paths.  The independent `physical_carriers` path keeps
the original subtraction `n - c_c d` deliberately: it is the independent
implementation required by the K4 overlap gate.

The identity was checked symbolically and the existing carrier, scaled-centre,
and K4-overlap tests pass (`12 passed`).  It improves interval conditioning for
the carriers containing `f`, especially near the principal saddle, but it
does not affect the dominant `nuD_main` (`d^2`) carrier.  Consequently the
low-`z` contract, the global `t`- and `delta`-cover, and the literal
weighted S1'''/S2''' judges remain open.
