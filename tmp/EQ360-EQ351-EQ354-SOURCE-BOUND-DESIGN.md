# CMP99 (3.50)--(3.54): source-facing Eq360 bound gate

Status: design gate only. This note does not discharge a Lean obligation and
does not move `20/41` or the window-15 marker.

## Primary-source anchor

- T. Balaban, *Propagators for Lattice Gauge Field Theories in a Background
  Field III*, CMP 99 (1985), printed pp. 400--401, Eqs. (3.50)--(3.54).
- Private primary artifact: `cmp99/1103942769.pdf`, registered SHA-256
  `39F8033B35838C7BDD14F97C7FB1EDB0B35D4190B8B88F31D19D12A72D542861`.
- Visual read performed from PDF page 12 / printed p. 400 and PDF page 13 /
  printed p. 401. OCR is not authoritative for the constants below.

## Literal source decomposition

For a positively oriented bond `b`, the source uses `A'(b) = A(b)`; for a
negatively oriented bond it uses `A'(b) = R(U_b) A(b)`.  Expanding the
perturbed covariant Laplacian gives

```text
(Delta_{U'U} lambda)(x)
  = (Delta_U lambda)(x)
    - sum_{b est(x)} i ad_{A'(b)} (D_U lambda)(b)
    - i[(D_U^* A)(x), lambda(x)]
    - sum_{b est(x)} F'_{1,k}(i ad_{A'(b)}) lambda(b+).
```

The nonlinear remainder is not a caller-supplied operator:

```text
F'_{1,k}(z)
  = eta^{-2} (exp(eta z) - 1 - eta z)
  = z^2 * integral_0^1 (1-t) exp(eta t z) dt.
```

Thus the literal local perturbation of (3.52) has exactly three source
species:

1. `sum_b i ad_{A'(b)} (D_U lambda)(b)`;
2. `i[(D_U^* A)(x), lambda(x)]`;
3. `sum_b F'_{1,k}(i ad_{A'(b)}) lambda(b+)`.

The exact orientation is `Delta_{U'U} = Delta_U - V'_1(A)` as in (3.53).

## Printed quantitative endpoint

Let `ell = L^j eta`. Under the source domain (3.37), printed Eq. (3.54) is

```text
|(V'_1(A) lambda)(x)|
  <= 4 d alpha1 ell^{-1} |nabla_U lambda|
     + 2 d alpha1 ell^{-2} |lambda|
     + 8 d alpha1^2 ell^{-2} |lambda|.
```

The norms on the right involve only nearest neighbours of `x`.

## Lean acceptance gates

1. Do not triangle-bound the current three raw stencil differences.  First
   prove the literal (3.51)--(3.52) regrouping, including the diagonal
   `D_U^* A` term and the internally constructed exponential remainder.
2. The producer must consume the already named Eq337 physical complex domain
   clauses, not replace them with fresh bounds:
   `CMP99Eq337PhysicalComplexAmplitudeBoundOn` and
   `CMP99Eq337PhysicalComplexCovariantDerivativeBoundOn`.
3. The positive/negative bond dictionary for `A'` is a theorem, not a free
   family.  The negative branch must use the same source transport `R(U_b)`
   as the Laplacian stencil.
4. The constants `4 d`, `2 d`, and `8 d`, together with the powers
   `ell^{-1}` and `ell^{-2}`, remain visible in the theorem statement.
5. A coordinate/matrix norm conversion may expose chart budgets, but it may
   not rename the source bounds.  If both directions are required, define and
   audit both operator-norm budgets explicitly.
6. Only after the pointwise source theorem is proved may it be transported to
   the finite-range/output-fixed or owner-weighted norm consumed by the
   Eq360 precision perturbation and the window-15 chain.

## Current boundary

The existing Eq360 PRE-VALIDATION drafts prove the exact difference of the
two analytic regional Laplacians and the four-term precision algebra.  They do
not yet prove the source decomposition above, the (3.54) pointwise bound, or
its downstream operator-norm transport.

The aggregate proposition
`CMP99Eq337PhysicalComplexPerturbationDomain` is itself still a scratch
PRE-VALIDATION structure even though its two constituent bound predicates are
sealed.  The source-bound gate must therefore promote and audit that structure
as an explicit prerequisite (or seal it in an earlier exact gate); it may not
treat the aggregate domain package as already certified merely because the
amplitude and covariant-derivative predicates exist in the tree.

## Compiler-facing module split

The next implementation is finite and should preserve the following phase
boundaries.  Provisional filenames are descriptive; changing a filename does
not change the gates.

1. `BalabanCMP99Eq351ExponentialAdjointRemainder`: define the nonlinear
   remainder internally as `exp(Y) X exp(-Y) - X - [Y,X]` and prove the exact
   algebraic decomposition.  This leaf has no physical input and does not
   claim the quadratic norm bound; the physical use of that bound remains a
   named obligation of the source-facing pointwise producer.
2. `BalabanCMP99Eq351ExponentialAdjointRemainderBound`: derive the literal
   `8 * ‖Y‖^2 * ‖X‖` bound from the internally constructed remainder under
   `‖Y‖ ≤ 1/4`.  The physical substitution and the Eq. (3.37) amplitude
   clause are not inputs to this generic algebra leaf.
3. `BalabanCMP99Eq351ComplexLaplacianRegrouping`: construct `U1` with
   `cmp99Eq337PhysicalComplexPerturbedBackground U A eta`, expand the literal
   regional stencil, and prove the three-species identity.  The nonlinear
   exponential remainder is the specialization of module 1 at the same
   positive-bond exponential.  This module has no norm hypotheses.
4. `BalabanCMP99Eq354ComplexLaplacianPointwiseBound`: consume one
   `CMP99Eq337PhysicalComplexPerturbationDomain U A eta alpha1`, region
   membership, and the regrouping theorem.  Its endpoint retains the printed
   constants `4*d`, `2*d`, `8*d` and the powers `ell^-1`, `ell^-2`.
5. `BalabanCMP99Eq354ComplexLaplacianOwnerBound`: transport the pointwise
   result to the output-fixed / owner-weighted norm used by the regional
   defect.  Any chart conversion and finite-neighbour count are named here;
   the source clauses are not renamed or replaced.
6. `BalabanCMP99Eq360ComplexSourcePrecisionPerturbation`: combine the
   Eq. (3.59) internally generated forward/starred pair with the Eq. (3.51)--
   (3.54) Laplacian producer.  This is the first module allowed to identify
   the four-term Eq. (3.60) algebra with the physical source perturbation.

The baseline and perturbed Laplacians in the four source-facing modules share
one active carrier and one spacing.  The perturbed background is definitionally the
Eq. (3.37) construction above; no equality between a caller-supplied `U1` and
that background is accepted.  Until modules 1--5 compile and pass their axiom
audits, `cmp99Eq360ComplexLocalLaplacianPerturbation` remains valid auxiliary
algebra but is not a producer of the source bound.
