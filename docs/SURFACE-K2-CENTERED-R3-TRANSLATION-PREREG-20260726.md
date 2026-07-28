# K2 centered-to-absolute R3 translation — preregistration (2026-07-26)

This is the first proof-bearing single-cell test after the centered
denominator cover. It is fixed to birth index `144`,
`t=[72/25,29/10]`, `delta=[9/1000,1/100]`, midpoint `19/2000`, half-width
`1/2000`, spatial grid `192 x 192`, physical split `1181/1000`, and Arb
precision 140 bits.

The nominal moment jets are computed about the exact midpoint. Their
coefficients are translated by `x=delta-19/2000` to an absolute-delta jet.
The registered outer-domain coefficient radii are translated by the same
binomial map using absolute radii; no radius is treated as a signed Taylor
coefficient. The quotient is then formed in the absolute-delta jet, after the
constant bilinear zero is enclosed and `K_D(0)>0` is checked.

Acceptance requires the quotient to form without an unresolved denominator,
the fourth coefficient and all registered companion/value charges to be
finite, and the existing R4 margin formula to have a strictly positive
outward-rounded lower endpoint. Production and byte-identical replay are
required. Any failure is terminal for this construction; no post-hoc constant
or delta exclusion is allowed. A pass remains one cell only and does not
promote K2/G2/G6.
