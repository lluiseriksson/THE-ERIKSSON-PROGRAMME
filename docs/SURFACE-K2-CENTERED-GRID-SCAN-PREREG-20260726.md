# K2 centered grid scan — preregistration (2026-07-26)

This diagnostic tests whether the failed centered direct quotient is caused by
spatial quadrature enclosure width. It is fixed to cell 144,
`t=[72/25,29/10]`, `delta=[9/1000,1/100]`, midpoint `19/2000`, half-width
`1/2000`, physical split `1181/1000`, and Arb precision 140 bits. The frozen
grid ladder is `(192,384,768)`.

For each grid the centered direct quotient is evaluated over the same x-box,
and the raw residual margin is printed. Companion and truncation tails remain
unresolved and no result can promote R3/K2. The scan is diagnostic: it may
identify a viable grid for a fresh full-cover preregistration, or it may
reject quadrature refinement as a repair.
