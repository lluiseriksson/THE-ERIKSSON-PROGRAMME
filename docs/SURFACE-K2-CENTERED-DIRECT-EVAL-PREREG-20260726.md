# K2 centered direct evaluation — preregistration (2026-07-26)

This diagnostic tests a different use of the centered jet after the failed
absolute translation. It is fixed to index `144`,
`t=[72/25,29/10]`, `delta=[9/1000,1/100]`, midpoint `19/2000`, half-width
`1/2000`, grid `192`, physical split `1181/1000`, and Arb precision 140 bits.

The moment jets remain in `x=delta-19/2000`. The quotient is formed as
`B(x)/(2 cos(t/4) (19/2000+x) K_D(x)^2)`, so no interval containing zero is
divided. The resulting truncated polynomial is evaluated over the full
centered x-box and compared with `T(c)+r2(c)delta` using the minimum registered
budget `Theta3(c)*(9/1000)^2`.

This is explicitly a diagnostic of nominal-plus-outer arithmetic: the
fifth-order Bessel companion remainder and the truncation tail are printed as
unresolved charges and are not silently treated as zero. A favorable raw
margin is not an R3 certificate; a nonpositive raw margin rejects this direct
evaluation architecture on the frozen cell.
