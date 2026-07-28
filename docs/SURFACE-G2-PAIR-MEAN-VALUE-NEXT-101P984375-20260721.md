# Preregistration: next paired mean-value cell

**Registered:** 2026-07-21, before reading the result.

Run the existing certificate-grade paired mean-value driver on the next
dyadic beta cell

    beta   [13054/128,13055/128] = [101.984375,101.9921875]
    lambda [3/2,19/10]
    modes 115, beta_order 50, lambda_order 50, Arb precision 500

The production and replay runs must use the same committed driver and exact
rational endpoints.  A pass means only a strictly negative total_upper and
exact production/replay equality after parsing; it is candidate evidence for
the finite-beta seam and carries no G2/G6 promotion.  A timeout or failure is
retained as a route diagnostic and does not alter any gate.
