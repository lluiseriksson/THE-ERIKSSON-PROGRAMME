# High-beta weak-main relay — preregistration (2026-07-28)

**State:** exact relay design; the weak main-saddle bound is open.

## Purpose

The Surface-Theorem sign does not require the standalone sharp assertion
`X_main>=0`.  The exact two-stage decomposition is

```text
X_1
 = X_main/(1-rho) + C_mirror,

X_full
 = (d_1/d) X_1 + C_rest
 = (a/d) X_main + (d_1/d) C_mirror + C_rest,
```

where `d_1=a(1-rho)`.  Thus a negative lower bound for `X_main` is admissible
provided its fully scaled charge fits the already certified final margin.
This record freezes that weaker relay before attempting such a certificate.

## Frozen rational inputs

On the common-`x` lane

```text
beta >= 1000/9,
lambda = beta(pi-t) >= 3,
p = sin(t/4) >= 101/200,
```

use only the following outward rational consequences of the existing
production/replay evidence:

```text
Q > 19/20,
0 <= rho < 7/200,
|C_mirror| < 43/50,
|C_rest| < 1/100000.
```

For the third-block mass, write `e=d-d_1`.  Its certified mass majorant gives
`|e|<=2L`, `d>=1/2`, and `L<10^-18`.  Hence

```text
0 < d_1/d <= 1 + |e|/d < 1 + 10^-15.
```

The relaxed main-saddle target is

```text
X_main >= -1/20.
```

## Exact terminal arithmetic

From the identities above,

```text
Q + X_full
>
19/20
 -(1+10^-15) * (43/50 + (1/20)/(1-7/200))
 -1/100000.
```

The exact rational verifier must prove this lower bound strictly positive.
It must also verify each elementary implication used to replace the mass
ratios by the displayed rational factors.

## Promotion boundary

A green algebra check promotes only this relay implication.  Terminal
high-beta closure additionally requires:

1. a new outward-rounded certificate of `X_main>=-1/20` on precisely the
   lane above;
2. validation of the existing production/replay pair against the tighter
   consequences `rho<7/200` and `|C_mirror|<43/50`;
3. re-execution of the third-block bound and a dependency audit;
4. a fresh domain-union audit.

This relay does not restore the withdrawn K2 manifests and does not prove
K4, S1'''/S2''', G2, G6, or the manuscript theorem by itself.
