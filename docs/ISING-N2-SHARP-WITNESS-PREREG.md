# Pre-registration: the sharp `N = 2`, `gamma = 0` witness

Status: **PHASE 0 ONLY -- PRE-REGISTERED, NOT YET LEAN-VERIFIED**

Base SHA: `1470b4e91b582b043a225957a112d94b9a6226c0` (the frozen head of
draft PR #44, `codex/spatial-ring-uniformity`).

This record fixes the target before any general spectral, Clifford, or
Jordan--Wigner infrastructure is opened.  In the repository convention the
physical ring size is `L + 1`, so this witness uses `L = 1` and hence `N = 2`.

## Exact repository object

Let

```text
K_beta = symWeighted (spatialWeightRing 0) beta
```

on configurations `Fin 2 -> Fin 2`.  Choose the two global-flip orbit
representatives

```text
rho_0 = (0, 0),    rho_1 = (0, 1).
```

The physical even and odd blocks are the exact orbit folds

```text
E_beta(i,j) = K_beta(rho_i,rho_j) + K_beta(rho_i,flipCfg(rho_j)),
O_beta(i,j) = K_beta(rho_i,rho_j) - K_beta(rho_i,flipCfg(rho_j)).
```

These are the matrices of the restrictions to `IsFlipEven` and `IsFlipOdd`
in the normalized orbit bases.  They must be derived from `K_beta`; their
closed forms may not be assumed as hypotheses.

## Pre-registered targets

For `beta > 0`, finite `2 x 2` algebra must prove

```text
E_beta = [[2 cosh(2 beta), 2], [2, 2 cosh(2 beta)]],
O_beta = [[2 sinh(2 beta), 0], [0, 2 sinh(2 beta)]].
```

With the Mathlib L2 operator norm on matrices, the named headline target is

```text
||O_beta|| / ||E_beta||
  = sinh(2 beta) / (cosh(2 beta) + 1)
  = tanh beta.
```

At `gamma = 0`, the campaign constant is

```text
q = tanh(beta) * exp(2 * 0) = tanh(beta),
```

so this is an equality case of the proposed uniform bound.  A second target
must prove the failure of quadratic-form domination without disguising it as
a spectral statement:

```text
(q * E_beta - O_beta)(0,0) = -2 * tanh(beta) < 0.
```

Finally, a named sharpness theorem must state that every `c < tanh(beta)`
fails already on this witness.  This certifies optimality of the proposed
uniform constant if the general upper bound is proved later; it does not prove
that upper bound.

Planned Lean names:

```text
n2EvenBlock
n2OddBlock
n2EvenBlock_closedForm
n2OddBlock_closedForm
n2_sharp_ratio
n2_form_domination_fails
n2_no_strictly_smaller_constant
```

## Stop rule and prohibited scope

If the matrix operator-norm API requires a general restricted-spectrum
development, Phase 0 stops after the exact orbit-fold identities and the
minimal `2 x 2` algebraic equality.  The unproved bridge to the requested norm
quotient must then be printed as open; it may not be promoted by prose.

Phase 0 does not construct Clifford algebras, Jordan--Wigner strings, NS/R
mode classifications, the uniform theorem, or a paper.  Those remain behind
the external Phase 1 verdict and an explicit owner authorization.
