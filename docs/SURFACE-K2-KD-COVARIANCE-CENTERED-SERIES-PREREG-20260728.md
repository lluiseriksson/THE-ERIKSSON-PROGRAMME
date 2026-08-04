# K2 cellwise-centered KD-covariance series — preregistration

**Registered:** 2026-07-28, after the direct coefficient-series failure and
before either centered-series grid was executed.

**State:** nominal stress-point design only; no K2, K4, S1/S2, gate, or
manuscript promotion.

The four global moment series lose interval cancellation.  This successor
uses the exact law of total covariance before global summation:

```text
Cov(A,G)
 = sum_i p_i Cov_i(A,G)
 + sum_i p_i (A_i-Abar)(G_i-Gbar).
```

Each cell's conditional means and covariance are formed before summing.
All integration, grid, precision, exact-head overlap checks, and the
grid-24 `radius(Y_3)<1968` predicate are identical to
`SURFACE-K2-KD-COVARIANCE-SERIES-PREREG-20260728.md`.

Failure retires coefficientwise second-spatial-derivative Taylor integration
even with cellwise centering.  Pass licenses only a higher-order,
t-uniform, companion-and-exterior successor; it cannot restore K2.

## Result

The frozen grid-24 predicate fails:

```text
radius(Y0) = 11.8315
radius(Y1) = 1301.63
radius(Y2) = 270611.8
radius(Y3) = 138684127.5 > 1968
terminal = KD COVARIANCE CENTERED SERIES DESIGN FAIL; NO K2 PROMOTION
```

This is worse than the direct four-global-series assembly because interval
division by each cell's weight is repeated before summation.  The route is
retired as preregistered.  Transcript SHA-256:
`DD57DFCBFDBFBFC93A17B566830B0BDD71354785883CFB1A744FC79D2F5C83DF`
raw CRLF and
`D1B4604D9BFB40928997227BADDA1738BC5493488AEBF7F3D63F4C1037F9EF58`
normalized LF.
