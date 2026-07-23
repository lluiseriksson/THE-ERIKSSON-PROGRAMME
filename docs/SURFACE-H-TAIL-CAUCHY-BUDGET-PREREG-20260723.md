# `(H_tail)` Cauchy budget: preregistration

This note registers the numerical budget for a possible complex-delta
majorant.  It is an obligation ledger, not a certificate.

Take `rho=7/100`, `delta_1=1/15`, and the endpoint budget
`B_4=(1000/9)*Theta_3(1)`.  If a complete integrand majorant proves
`M=sup_{|delta|=rho}|f(delta)|`, Cauchy's estimate gives

```text
|a_4| <= M/rho^4,
tail_{n>=5} <= M*q^5/(1-q),  q=delta_1/rho=20/21.
```

The necessary threshold for the order-four coefficient is
`M <= B_4*rho^4 = 0.002763129991...`.  The geometric tail multiplier is
`q^5/(1-q) = 20^5/21^4 = 16.454049495...`.

The missing quantity is the full complex supremum, including Jacobian,
normalization, Bessel factors, complex sinc factors, square-root/exponential
factors, and any Euler-transport terms.  The executable
`audit_surface_h_tail_cauchy_budget.py` prints these exact constants and
always ends with `NO_H_TAIL_PROMOTION`; a future majorant may replace that
footer only after its independently hashed suprema and margins are supplied.
