# Sine-normalized seam stress preregistration

The common beta-midpoint scaling did not resolve the one-box seam stress.
This separate design keeps that fixed positive scale and additionally
replaces both Fourier families by

\[
 \widehat F_A=F_A^J/\sin t,\qquad
 \widehat F_B=F_B^J/\sin t.
\]

Because `sin(t)>0` on `(0,pi)` and the same factor is used for both families,
the exact identity is `widehat W=W^J/sin(t)^2`.  The implementation must form
the full t-jet of the quotient by the product recurrence, not divide a final
interval by an interval containing zero.  Its remainder sums use the same
recurrence with the outward lower bound of `sin(t)` on the frozen t-box.

The first stress uses beta `[3258/32,3259/32]`, the fixed t-box
`[31268/10000,312686/100000]`, CWIN `3/2`, beta order 30, t-order 37, and
180-bit Arb.  It is diagnostic only; no coverage or gate promotion follows.
