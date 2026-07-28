# Preregistration: paired mean-value width probe

**Registered:** 2026-07-21, before reading the result.

Test whether the paired mean-value enclosure can widen at the next beta
range:

    beta   [102, 102+1/32] = [102,3265/32]
    lambda [3/2,19/10]
    modes 115, beta_order 50, lambda_order 50, Arb precision 500

Run production and an exact replay.  A successful negative upper endpoint is
candidate-only and needs an audit manifest; a failure is a retained
width-diagnostic and does not change G2/G6.
