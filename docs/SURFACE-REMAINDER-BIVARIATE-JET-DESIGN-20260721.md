# Bivariate delta--t jet design (2026-07-21)

## Status

`DESIGN_ONLY`.  This note and
`scripts/surface_remainder_bivariate_jet.py` do **not** promote K2, K4,
S1''', S2''', G2, or G6.  The final-seal gate remains unchanged.

## What was added

The existing parameter differentiation code carries a second-order jet in
one parameter at a time.  On a joint `(delta,t)` box this leaves the mixed
coefficient unresolved and the interval products become symmetric balls.  The
new `BiJet` stores

```text
c00, c10, c01, c20, c11, c02
```

with the convention

```text
f(d+h,t+k) = c00 + c10 h + c01 k + c20 h^2 + c11 h k + c02 k^2 + O(3).
```

It implements truncated multiplication and scalar composition (including
inverse, square root, exponential, sine and cosine), and applies those
operations to the pointwise raw carrier formulas.  The mixed coefficient is
kept explicitly rather than inferred from two independent univariate runs.

## Verification performed

`tests/test_surface_remainder_bivariate_jet.py` checks the algebra against
70-digit `mpmath` derivatives at `(delta,t,s,alpha)=(0.05,2.9,0.2,0.3)`.
Both the pure and mixed coefficients are required to lie in their Arb balls.
The smoke currently passes (`2 passed`).

## What is still required before promotion

The jet is only a pointwise parameter probe.  A K2 certificate still needs,
for every spatial cell and parameter box:

1. interval enclosures for all third-order parameter derivatives (or a
   validated Taylor remainder equivalent to them);
2. the signed determinant assembled from the Taylor polynomials before any
   spatial absolute-value bound;
3. a separate spatial remainder bound, with the KD positive floor and all
   companion charges accounted for;
4. a fail-closed aggregate manifest and replay validator.

In particular, the passing KD floor union is not used as a substitute for
these obligations.  No gate, manuscript banner, or `[SLOT]` marker was
changed by this work.
