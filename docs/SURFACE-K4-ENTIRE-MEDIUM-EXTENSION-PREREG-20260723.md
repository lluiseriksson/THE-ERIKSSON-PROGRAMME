# K4 entire-series medium-z extension: preregistration

**Registered:** 2026-07-23, before the extension regression

This design extension removes the artificial `4<z<20` branch gap in an
isolated copy of the centred K4 carrier.  It uses the same positive Bessel
series and geometric remainder as the low-z lane, with 96 terms and ordinary
derivatives through order four; the finite range is enlarged to `0<=z<=20`.
It is not wired into the authoritative carrier: doing so would change shared
dependency hashes and require a complete regeneration of existing manifests.
No mesh, stopping rule, or weighted K4 judge is changed.

The analytic endpoint-hull contract is the positive Laplace representation

`z^(-nu) exp(-z) I_nu(z) = c_nu * integral_0^2 exp(-z*u)
 [u*(2-u)]^(nu-1/2) du`,

for `nu=1,2` and `c_nu>0`.  Thus all derivatives alternate in sign on the
whole half-line.  The regression must check finite Arb enclosures, direct
`Arb.bessel_i` containment, and strict alternating signs through order five
at `z=4,8,12,16,20`, plus interval containment on `[4,20]`.

This is an isolated design route and remains candidate-only.  It carries no K4,
S1'''/S2''', G2, or G6 promotion until the global delta/t union, coefficient
and outer-tail budgets, overlap, and independent production/replay judges
are complete.
