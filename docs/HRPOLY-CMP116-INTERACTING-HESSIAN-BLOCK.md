# hRpoly hard block: the interacting CMP116 Hessian estimate

Date: 2026-07-15.  Branch: `codex/hrpoly-b3-card-tilt`.

## Strongest compiled checkpoint

The physical constraint-coordinate part of the CMP116 source is closed:

1. `C = I - E Q` is constructed on physical positive-bond one-cochains;
2. `Q E = id`, `Q C = 0`, `C` fixes `ker Q`, and `C^2 = C`;
3. `||E|| = M^(d-1)` and, for `d >= 3`,
   `||C|| <= 1 + M^(d-1)`, independently of the periodic volume;
4. the exact physical/CMP116 isometry transports `C` to a finite matrix;
5. the strongest flat-background Gamma endpoint inserts this matrix and its
   norm internally.  It accepts no arbitrary `C`, `CNorm`, or `hC`.

The terminal compiled endpoint is

```lean
YangMills.RG.CMP116Eq214FiniteGaussianData.
  norm_term_le_cauchyRate_of_physicalConstraintGamma_flatDelta_expCard
```

at commit `e66db9e7` (with the preceding construction and norm checkpoints at
`56ce793e` and `2aba0be8`).

## Source check and correction of the tempting shortcut

CMP116, pp. 15--17, equations (2.14)--(2.26), does **not** replace the complex
contour Hessian by the identity-background operator.  It first replaces all
operators by their values at

```text
sigma(Z) = 0, U = Ubar, J = 0,
```

where `Ubar` remains a generally nontrivial small background.  The changes in
the first quadratic form, the second Gaussian covariance, and the mixed
bilinear form produce `R1`, `R2`, and `R3`.  Their matrix elements obey the
source estimate

```text
|Ri(b,b')| <=
  (O(1) exp(-(delta0/3) M) + O(alpha0 + alpha1))
  exp(-(delta0/2) |b-b'|).
```

Thus `Delta_k(sigma,U,J) = Delta_flat` is not a valid small-field identity.
The explicit `O(alpha0 + alpha1)` term records the nonzero background
dependence.

## Minimal missing Lean construction and theorem

The repository presently has no load-bearing definition of the second
variation of the nonabelian Wilson action at `Ubar`.  Before (2.16) can be
proved, the following construction is required (names are proposed targets,
not existing declarations):

```lean
noncomputable def cmp116PhysicalWilsonHessianMatrix
    (Dict : PhysicalGaugeCMP116Dictionary d (M * N') Nc d L lieDim)
    (rho : SUNAdjointModel Nc)
    (Ubar : PhysicalGaugeField d (M * N') Nc)
    (sigma : Fin nDelta -> Complex) :
    Matrix (CMP116CoordIndex d L lieDim)
      (CMP116CoordIndex d L lieDim) Complex
```

It must be obtained from the literal second derivative of the Wilson action,
not supplied as a matrix parameter.  The first load-bearing estimate must then
have the following content:

```lean
theorem cmp116Eq216_physical_hessian_error_kernel
    (hsmallU : PhysicalCMP116SmallBackground Ubar alpha1)
    (hcontour : PhysicalCMP116ContourSmall sigma alpha0) :
    let DeltaSigma :=
      cmp116PhysicalWilsonHessianMatrix Dict rho Ubar sigma
    let DeltaBase :=
      cmp116PhysicalWilsonHessianMatrix Dict rho Ubar 0
    forall i j,
      norm (DeltaSigma i j - DeltaBase i j) <=
        (c0 * Real.exp (-(delta0 / 3) * M) +
          c1 * (alpha0 + alpha1)) *
        Real.exp (-(delta0 / 2) * physicalCoordDist Dict i j)
```

Here `PhysicalCMP116SmallBackground`, `PhysicalCMP116ContourSmall`, and the
Hessian matrix must themselves be defined from the source fields and Wilson
action.  They cannot be replaced by a hypothesis asserting the displayed
kernel bound.  The constants hidden by the paper's `O(1)` must be extracted
from the generalized random-walk expansion cited before equation (2.16).

A second endpoint must identify the real base matrix
`DeltaBase = Delta_k(0,Ubar,0)`, prove its uniform norm/coercivity estimate,
and feed the three resulting real error kernels into the already compiled
Schur consumers for (2.20)--(2.22).  Only then can the literal `hdom` premise
of equation (2.14) be produced.

## Why existing results do not discharge it

- `BalabanCMP116Eq214FlatDeltaBound` treats only `Ubar = 1`.
- `PhysicalGaugeOperator.physicalKslice` receives a Wilson Hessian as an
  operator parameter; it does not construct it.
- `SmallBackgroundPerturbation` is a named norm hypothesis, not a producer.
- `PhysicalGaugeWilsonHessianSourceDictionary` records an identification
  contract but receives both the Hessian and Green operator as data.
- `BalabanCMP116Eq220PotentialQuadratic` and
  `BalabanCMP116Eq221OperatorForms` consume exponential kernel estimates;
  they do not prove equation (2.16) for physical kernels.
- no other local branch or worktree contains a physical Wilson-Hessian
  construction or the `R1/R2/R3` random-walk expansion.

## Routes investigated

1. **Identify the small-background Hessian with `Delta_flat`.** Rejected:
   contradicted by the replacement step on CMP116 p. 15 and the nonzero
   `O(alpha0 + alpha1)` contribution in (2.16).
2. **Use the existing `SmallBackgroundPerturbation`.** Rejected as a closure:
   it merely renames the missing estimate and would violate the campaign's
   hypothesis discipline.
3. **Use the Wilson-Hessian source dictionary.** Rejected as a producer:
   it packages source-identification fields supplied by the caller.
4. **Apply the existing Schur lemmas directly.** They close the implication
   from (2.16) to (2.21), but cannot manufacture the physical kernels.
5. **Search sibling worktrees and all local modules.** No stronger physical
   Hessian or random-walk-expansion implementation was found.

## Consequence for hRpoly

The chain remains blocked before physical `hdom`:

```text
Wilson Hessian at Ubar
  -> physical random-walk expansion and (2.16)
  -> R1/R2/R3 and potential-kernel estimates
  -> hdom for the literal (2.14) integrand
  -> complete (2.26) ledger
  -> hraw -> hRpoly -> KP.
```

No `hraw`, `hRpoly`, KP, continuum-limit, or Clay conclusion is claimed by
the constraint-coordinate checkpoints.
