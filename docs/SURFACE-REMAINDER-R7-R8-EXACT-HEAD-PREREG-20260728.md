# R7/R8 exact-head checker — preregistration (2026-07-28)

## Purpose

The design calculation in
`scripts/derive_surface_remainder_delta0_r7_design.py` propagated truncated
power-series coefficients by hand-written list recurrences.  It proposed the
coefficients of `delta^6` and `delta^7` in the regularized nominal K2 carrier
`Y(delta,c)`, but did not promote them.

This preregistration freezes a second exact engine and its acceptance
criterion before that engine is run.  The second engine must construct the
univariate `delta` expressions directly and use SymPy's own series expansion
and coefficient extraction.  It must not import the design derivation or any
value produced by it.

## Frozen targets

For positive `c`, the checker must prove exact symbolic equality with

```text
Y6(c) =
 (2085412*c^14 + 6775103*c^12 + 11636676*c^10
  - 52644752*c^8 + 1046587520*c^6 - 2880628992*c^4
  + 2254849024*c^2 - 513015808)
 / (33554432*c^21)

Y7(c) =
 (19936*c^16 + 119595*c^14 + 323054*c^12 + 637408*c^10
  - 12653880*c^8 + 104539328*c^6 - 219463616*c^4
  + 153352416*c^2 - 33064504)
 / (524288*c^24).
```

It must also reproduce the already certified heads `Y0,...,Y5`.  A mismatch
at any order is terminal failure.

## Frozen mathematical construction

The checker uses the same exact definitions of `p`, `q`, `w`, the square
root, phase correction, `D`, `F`, and the four Gaussian moments
`KD,KF,HDD,HDF` as the lower-order exact checkers.  The independence is in
the series engine:

1. build complete SymPy expressions in `delta,sigma,tau,c`;
2. truncate every analytic composition with `sympy.series(..., delta, 0, 9)`;
3. evaluate Gaussian monomials exactly;
4. assemble
   `B = KD*HDF - KF*HDD`;
5. extract `Y = B/(2*c*delta*KD^2)` through `delta^7`;
6. reduce each difference from the frozen target by `cancel` and require
   exact zero.

The relative Bessel companion polynomials are retained through degree eight.
This is necessary: because their argument is `h=O(delta)`, a polynomial of
degree below eight is not allowed in a checker that constructs all moment
coefficients through `delta^8` and the carrier through `delta^7`.

## Cauchy consequence to be checked separately

Promotion of the exact heads does not itself prove K2.  A later interval
checker may use:

```text
|Y(delta)-sum_{k=0}^m Y_k delta^k|
    <= M (|delta|/rho)^(m+1)/(1-|delta|/rho)
```

only for the fixed-square holomorphic polynomial-companion surrogate.
For `m=6` the exponent is seven; for `m=7` it is eight.  The true Bessel
companion remainder and the moving/exterior domain remain real-axis error
terms and must be charged separately with outward rounding.  No result of
this checker may be used to claim those two patches.

## Acceptance and publication

Acceptance requires:

- exact matches for `Y0,...,Y7`;
- exact cancellation of the constant bilinear coefficient;
- script, dependency, interpreter, SymPy, and Git provenance;
- a complete transcript and a second replay with identical normalized
  mathematical output;
- tests that freeze both target expressions and reject a perturbed target.

Until all of these pass, R7/R8 remain design-only.  Even after they pass, K2,
G2, G6, and the manuscript remain unpromoted until the complex surrogate,
true-companion, and exterior budgets all close.
