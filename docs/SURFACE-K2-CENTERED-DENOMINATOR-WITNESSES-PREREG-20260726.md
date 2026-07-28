# K2 centered-denominator witnesses — preregistration (2026-07-26)

This diagnostic extends the favorable centered-carrier test to five frozen
t-box witnesses. It remains conditioning evidence only; it carries no K2,
G2, G6, `(H_tail)`, or manuscript promotion.

Frozen witness indices are `(0, 50, 100, 144, 156)` from the sealed ordered
birth partition. Every run uses `delta=[9/1000,1/100]`, midpoint
`19/2000`, half-width `1/2000`, spatial grid `192 x 192`, physical split
`1181/1000`, and Arb precision 140 bits. Each output must print a strictly
positive uniform denominator floor and end in `CENTERED DENOMINATOR PASS`.

The acceptance rule is per witness and requires a byte-identical rerun. A
failure is recorded as a carrier limitation. Even five passes do not imply a
uniform t-cover or the R3 residual inequality; those remain prerequisites for
any K2 promotion.
