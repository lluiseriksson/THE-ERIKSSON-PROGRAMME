# P4 physical-operator vertical slice

**Status:** design fixed; the deterministic coercivity/covariance bricks are
implemented in `YangMills/RG/CoerciveCovariance.lean` and
`YangMills/RG/GaugeFixedCovariance.lean`.  The finite physical-operator
interface is now implemented in `YangMills/RG/PhysicalGaugeOperator.lean`,
and the full-periodic physical Hodge form in
`YangMills/RG/PhysicalGaugeCochains.lean` now has right-oriented quadratic
identities matching the coercivity input shape, including named
trivial-background flat specializations.  The flat physical block constraint
also has a named positive-bond support stencil inherited from `linAvgSupport`.
The full-periodic flat Hodge/block-Poincare predicate and source-input
repackaging theorem are isolated in
`YangMills/RG/PhysicalGaugeHodgePoincare.lean`; the active-region API remains a
later branch.
The first finite-combinatorial kernel check is also in place: direction-wise
constant physical one-cochains are sent by `flatBlockConstraintQCLM` to `L`
times the corresponding coarse directional value, so the block constraint is
injective on that constant sector.  Those direction-wise constants are now
also proved to be flat harmonic at the trivial background, by an explicit flat
curl calculation and finite periodic summation by parts for the flat
divergence; the layer also exposes the corresponding flat-Hodge
operator-kernel statement and the exact block-zero test on constants, packaged
as a trivial joint-kernel theorem on the constant sector.  The same flat
cochain layer now also names the flat harmonic condition and proves that the
flat Hodge quadratic form, and the operator equation `K₀ A = 0` itself,
vanish exactly on simultaneous flat-curl and gauge-divergence-zero fields.  It
also exposes the trivial-background curl and gauge constraint as explicit
pointwise formulas, and turns flat harmonicity into pointwise vanishing of the
corresponding plaquette curl and backward-divergence expressions.
The companion module `YangMills/RG/PhysicalGaugeFlatPoincare.lean` now proves
the exact constant-sector norm identities and the sharp block-control ratio
`L^d / L^2` for the current `linAvg` normalization.  It also carries the
conditional bridge `FlatHarmonicKernelClassified`, which reduces a future
reverse flat-harmonic classification theorem to exact constant-sector kernel
statements and triviality of the joint flat-Hodge/block kernel.  From trivial
joint kernel, it now derives a non-uniform fixed-volume flat Hodge/block
Poincare theorem using Mathlib's finite-dimensional anti-Lipschitz theorem.
The reverse harmonic classification and volume-uniform full-periodic estimate
remain frontier obligations.
The source-identification bricks below remain frontier obligations.

## 1. Purpose

The next important jump is not another theorem that assumes a Hessian,
covariance, covariance root, and local activity.  It is a vertical chain of
**definitions** from the Wilson action to the raw activity consumed by the
existing CMP116/Appendix-F layer:

```text
Wilson action + coarse field
        ↓
physical background Ubar(V)
        ↓
gauge-fixed Hessian K[Ubar, Omega]
        ↓  discrete Hodge/Poincare + small-background perturbation
uniform coercivity
        ↓
exact covariance C[Ubar, Omega] = K[Ubar, Omega]⁻¹
        ↓  Combes--Thomas / generalized random walks
exponential kernel decay
        ↓
localized Gaussian root B[Ubar, Omega] = C[Ubar, Omega]^(1/2)
        ↓  W = B X, X distributed by dmu0
physical fluctuation integrand over a product Gaussian
        ↓
localized activities H(Z)
        ↓
‖H(Z)‖ ≤ H0 exp (-kappa dM(Z, mod Omegaᶜ))
        ↓
existing CMP116 → K# → H# → SingleScaleUVDecay
```

The acceptance rule is strict: the final raw-activity theorem must not take an
arbitrary precision operator, covariance, square root, or activity as an
argument.

## 2. Fixed finite-volume model

The opening implementation should use one finite periodic lattice and one RG
step:

* gauge group `SU(N)`;
* tangent fields represented by real coordinates on `su(N)` bonds;
* active region `Omega` with explicit boundary convention;
* a small background `Ubar`, initially supplied together with a smallness proof;
* later, `Ubar = Ubar(V)` constructed from the coarse field by the constrained
  variational problem.

The physical source must determine whether the block constraint is represented
by a soft mass `a Q†Q`, a hard restriction to `ker Q`, or an equivalent Schur
complement.  These alternatives must not be identified by an unproved wrapper.

## 3. Brick P4.0 — exact covariance from coercivity

### New definitions

```lean
continuousLinearEquivOfIsCoerciveCLM
covarianceOfIsCoerciveCLM
```

### New theorems

```lean
isCoerciveCLM_norm_lower_bound
isCoerciveCLM_injective
isCoerciveCLM_surjective
covarianceOfIsCoerciveCLM_apply_precision
precision_apply_covarianceOfIsCoerciveCLM
covarianceOfIsCoerciveCLM_comp_precision
precision_comp_covarianceOfIsCoerciveCLM
norm_covarianceOfIsCoerciveCLM_apply_le
norm_covarianceOfIsCoerciveCLM_le
covarianceOfIsCoerciveCLM_psd
```

### Meaning

For a finite-dimensional real precision operator `A` satisfying

```text
c ‖x‖² ≤ inner x (A x),    c > 0,
```

Lean now constructs its actual inverse `C`, proves `CA = AC = id`, and obtains
`‖C‖ ≤ c⁻¹`.  This is the first point at which the P4 route has an exact
covariance rather than a carried covariance-shaped object.

### Honest boundary

P4.0 does not say that `A` is the Yang--Mills Hessian.  It only ensures that,
once the physical coercivity theorem lands, no additional inverse/covariance
hypothesis is needed.

The companion abstract assembly module
`YangMills/RG/GaugeFixedCovariance.lean` already composes this inverse theorem
with the verified `GaugeFixedPrecision` residual-coercivity theorem.  Thus a
source theorem proving the block-Poincare/Hodge and perturbation-budget
hypotheses for `K0 + a Q†Q - Σ` immediately yields a named exact covariance
for that precision form.  This is still not the physical theorem: the source
must identify `K0`, `Q`, and `Σ`.

## 3a. Brick P4.0a — finite physical gauge-operator interface

### New definitions

```lean
PositiveBond
GaugeZeroCochain
GaugeOneCochain
GaugeTwoCochain
ActiveGaugeRegion
flatD0FullCLM
flatD1FullCLM
flatGaugeConstraintCLM
flatKslice
positiveScaledLinAvgCLM
blockConstraintCLM
physicalKslice
gaugeFixedPhysicalPrecision
physicalPrecisionDefect
SmallBackgroundPerturbation
```

### New theorems

```lean
flatD1FullCLM_comp_flatD0FullCLM
flatKslice_nonnegative
positiveScaledLinAvgCLM_apply
physicalPrecision_eq_flat_sub_defect
```

### Meaning

This brick follows the source-facing recommendation to implement the soft
full-space term `a Q†Q` before any hard constrained covariance.  The gauge
constraint and the RG block constraint are deliberately named separately:
`flatGaugeConstraintCLM` is the gauge condition, while `blockConstraintCLM`
is the positive-bond version of the block derivative `Q`.  The generic
soft-precision shell also permits these two constraints to have different
codomains, as they should: a gauge condition and an RG block average are not
the same observable.

The module avoids using `FineBondHilbert` as the physical tangent model,
because `ConcreteEdge` includes both orientations.  Instead, independent
one-cochains are indexed by positive bonds `FinBox d N × Fin d`, and a
linearized orientation adapter feeds the already verified `linAvg`.

### Honest boundary

This is still a flat, finite, pre-physical interface.  It does not identify
the Wilson Hessian, prove the Balaban/Dimock source formula, prove a physical
Hodge/Poincare inequality, prove the perturbation estimate, or construct the
full physical Green function.  It only gives later source theorems the exact
finite operator slots they must fill.

## 3b. Brick P4.0b — full-periodic flat Hodge/block-Poincare interface

### New definitions

```lean
FlatGaugeHodgePoincare
constantPhysicalGaugeOneCochain
IsFlatHarmonicOneCochain
```

### New theorems

```lean
flatGaugeHodgePoincare
fineLineSum_constant
linAvg_constant
flatBlockConstraintQCLM_constant_apply
flatBlockConstraintQCLM_constant
flatBlockConstraintQCLM_constant_eq_zero_iff
flatBlockConstraintQCLM_injective_on_constants
covariantD1CLM_trivial_apply
gaugeConstraintQCLM_trivial_apply
isFlatHarmonicOneCochain_curl_apply_eq_zero
isFlatHarmonicOneCochain_divergence_apply_eq_zero
covariantD1CLM_trivial_constantPhysicalGaugeOneCochain
inner_constantPhysicalGaugeOneCochain_covariantD0CLM_trivial
gaugeConstraintQCLM_trivial_constantPhysicalGaugeOneCochain
isFlatHarmonicOneCochain_constantPhysicalGaugeOneCochain
flatGaugeHodgeK0CLM_constantPhysicalGaugeOneCochain
isFlatHarmonicOneCochain_iff_flatGaugeHodgeK0_inner_right_eq_zero
isFlatHarmonicOneCochain_iff_flatGaugeHodgeK0_inner_eq_zero
FlatHarmonicKernelClassified
flatHarmonicKernel_eq_constantSector
flatGaugeHodgeKernel_eq_constantSector
flatJointKernel_trivial_of_harmonicClassification
exists_sq_norm_le_sum_three_sq_of_jointKernel_trivial
exists_flatGaugeHodgeBlockPoincare_of_jointKernel_trivial
flatGaugeHodgeBlockPoincare_of_harmonicClassification
flatCurlDivBlockPoincare_of_harmonicClassification
```

### Meaning

This brick keeps the first Poincare target full-periodic and at the trivial
background, with fine side length `N = L * N'`.  The predicate states the
physical-cochain estimate for the unit flat Hodge operator
`flatGaugeHodgeK0CLM` plus the separate line-integral block map
`flatBlockConstraintQCLM`.  The theorem repackages a source-supplied
curl/divergence/block inequality using the already proved
`flatGaugeHodgeK0_inner_right` identity.  The harmonic-kernel test is internal:
it uses the same quadratic identity to turn zero flat Hodge energy into exactly
the two equations `D₁ A = 0` and `div A = 0`, with both inner-product
orientations exposed for later coercivity code.

### Honest boundary

The theorem does not prove the curl/divergence/block estimate, does not assert
volume-uniformity of the supplied constant, and does not identify the unit flat
Hodge operator with the Wilson Hessian.  It is the target shape that a later
source theorem must fill.  The constant-sector calculation is only the finite
kernel bookkeeping showing that the soft block term removes direction-wise
constant harmonic candidates; it is not a uniform Poincare estimate.  The
explicit curl and backward-divergence formulas give the pointwise equations
needed by the reverse classification ladder.  The new constant-sector
flat-harmonic theorem proves
the forward inclusion from direction-wise constants to flat harmonics at the
trivial background.  The new `FlatHarmonicKernelClassified` bridge carries the
reverse inclusion as a named hypothesis and derives exact kernel consequences;
it does not prove that hypothesis.  The fixed-volume Poincare theorem is
non-uniform: its constant is produced by finite-dimensional compactness and may
depend on the volume.  The operator-kernel and block-zero tests are
constant-sector or classification-conditional consequences only.  The
zero-form harmonic test and pointwise curl/divergence equations do not classify
the full harmonic kernel and do not prove that all flat harmonics are
direction-wise constants.

## 4. Brick P4.1 — physical tangent spaces and covariant cochains

Define the finite-dimensional Hilbert spaces used by the operator:

```lean
abbrev LieCoord := Fin (N^2 - 1) → Real
abbrev GaugeZeroCochain := PiLp 2 (fun _ : Site => LieCoord N)
abbrev GaugeOneCochain  := PiLp 2 (fun _ : Bond => LieCoord N)
abbrev GaugeTwoCochain  := PiLp 2 (fun _ : Plaquette => LieCoord N)
```

Then define background-covariant coboundaries:

```lean
covariantD0 Ubar : GaugeZeroCochain →L[Real] GaugeOneCochain
covariantD1 Ubar : GaugeOneCochain  →L[Real] GaugeTwoCochain
covariantDiv Ubar := (covariantD0 Ubar).adjoint
```

Required results:

```lean
covariantD1_comp_covariantD0_at_flat
covariantD0_gaugeCovariant
covariantD1_gaugeCovariant
covariantD0_finiteRange
covariantD1_finiteRange
```

The curvature term in `D1 ∘ D0` must be explicit away from a flat background;
it must not be simplified to zero without the corresponding flatness premise.

## 5. Brick P4.2 — derivative of the nonlinear block map

Connect the already formalized gauge-covariant block map with the Hilbert-space
average:

```lean
noncomputable def covariantBlockDerivative
    (Ubar : BackgroundGaugeField ...) :
    FineTangentField ... →L[Real] CoarseTangentField ...

theorem fderiv_nonlinearBlockMap_eq_covariantBlockDerivative : ...

theorem covariantBlockDerivative_at_trivialBackground :
    covariantBlockDerivative trivialBackground =
      scaledLinAvgCLM physicalScale L N'
```

This theorem certifies that the `Q†Q` mass in the precision operator is the
linearization of the physical blocking condition.

## 6. Brick P4.3 — Wilson Hessian and gauge-fixed precision

Define the second variation in a fixed exponential chart and assemble

```text
K[Ubar, Omega]
  = D² WilsonAction(Ubar)|Omega
    + xi⁻¹ covariantDiv(Ubar)† covariantDiv(Ubar)
    + a covariantBlockDerivative(Ubar)† covariantBlockDerivative(Ubar).
```

Lean-facing objects:

```lean
wilsonSecondVariation Ubar Omega : OneCochain →L[Real] OneCochain
gaugeFixingMass Ubar Omega        : OneCochain →L[Real] OneCochain
physicalBlockMass Ubar Omega      : OneCochain →L[Real] OneCochain
gaugeFixedPrecision Ubar Omega    : OneCochain →L[Real] OneCochain
```

Required results:

```lean
gaugeFixedPrecision_eq_secondVariation
gaugeFixedPrecision_isSelfAdjoint
gaugeFixedPrecision_gaugeCovariant
gaugeFixedPrecision_finiteRange
```

and the perturbative decomposition

```text
gaugeFixedPrecision Ubar Omega
  = flatGaugePrecision Omega + backgroundDefect Ubar Omega,

‖backgroundDefect Ubar Omega‖ ≤ cBackground * epsilon.
```

## 7. Brick P4.4 — Hodge/Poincare and physical coercivity

First prove the flat inequality

```text
‖A‖² ≤ CH (
    ‖flatD1 A‖²
  + ‖flatDiv A‖²
  + ‖Q A‖²).
```

Then compare covariant and flat operators and use
`isCoercive_add_of_opNorm_le` or `isCoercive_sub_of_opNorm_le` to absorb the
background defect.

Headline target:

```lean
theorem physicalGaugeFixedPrecision_coercive
    (hU : AdmissibleSmallBackground Ubar)
    (hOmega : AdmissibleLocalizationRegion Omega) :
    IsCoerciveCLM
      (gaugeFixedPrecision Ubar Omega)
      (physicalCoercivityConstant params)
```

with

```lean
physicalCoercivityConstant_pos :
  0 < physicalCoercivityConstant params
```

and constants uniform in the finite volume and admissible `Omega`.

At that point P4.0 constructs, without a new assumption,

```lean
physicalCovariance Ubar Omega :=
  covarianceOfIsCoerciveCLM
    (gaugeFixedPrecision Ubar Omega)
    physicalCoercivityConstant_pos
    physicalGaugeFixedPrecision_coercive
```

## 8. Brick P4.5 — kernel representation and exponential decay

Choose an orthonormal coordinate basis indexed by `Bond × Fin lieDim` and define

```lean
physicalCovarianceKernel Ubar Omega p q :=
  inner Real (basis p) (physicalCovariance Ubar Omega (basis q))
```

Required exact bridge:

```lean
physicalCovariance_apply_eq_kernelSum
```

The decay proof should use an exact inverse, not merely a majorized formal
series.  A preferred Combes--Thomas interface is exponential conjugation:

```text
Ktheta = Mtheta K Mtheta⁻¹,
‖Ktheta - K‖ < coercivityConstant,
‖Mtheta C Mtheta⁻¹‖ ≤
  (coercivityConstant - conjugationDefect theta)⁻¹.
```

Headline target:

```lean
theorem physicalCovarianceKernel_expDecay :
  ExpDecay bondDistance covarianceAmp covarianceRate
    (physicalCovarianceKernel Ubar Omega)
```

The amplitude and rate must be uniform in volume and compatible with the
modified-metric scale used by Appendix F.

## 9. Brick P4.6 — localized covariance root

Existence of an abstract positive square root is insufficient.  CMP116 needs a
root admitting local approximants or a random-walk decomposition.

Define

```lean
physicalCovarianceRoot Ubar Omega : OneCochain →L[Real] OneCochain
```

and prove

```lean
physicalCovarianceRoot_comp_adjoint :
  B.comp B.adjoint = physicalCovariance Ubar Omega
```

plus one of the following equivalent locality packages:

```text
B = sum_Z B[Z],
‖B[Z]‖ ≤ rootAmp exp(-rootRate * diameter Z),
```

or

```text
‖1_X (B - B^[r]) 1_Y‖ ≤ rootAmp exp(-rootRate * r).
```

A source-compatible construction is

```text
T = I - alpha K,       ‖T‖ < 1,
K^(-1/2) = sqrt(alpha) sum_n b_n T^n.
```

Finite range of `T` turns `T^n` into a path expansion.

## 10. Brick P4.7 — equality with the physical fluctuation integral

With `W = B X` and `X` distributed by the existing product Gaussian `dmu0`,
prove that the pushforward has covariance `C` and rewrite the actual one-step
Yang--Mills integral, including:

* the nonquadratic Wilson-action remainder;
* nonlinear blocking terms;
* the chart Jacobian;
* gauge-fixing/restriction factors;
* small-field cutoffs;
* observable insertions.

The central identity has to be an equality of integrals, not only a norm bound
on an unrelated function.

## 11. Brick P4.8 — localized CMP116 activity

Construct, rather than assume,

```lean
wilsonCMP116LocalizedFamily :
  BalabanCMP116LocalizedActivityFamily
    Bond lieDim SpectatorField PolymerIndex
```

and prove:

```lean
wilsonActivity_spectatorSupport_subset
wilsonActivity_fluctuationSupport_subset
wilsonActivity_stronglyMeasurable
wilsonActivity_integrable
norm_wilsonActivity_le_rawMetricDecay
wilsonFluctuationIntegral_eq_polymerPartition
```

The terminal raw bound should have the exact consumer shape

```text
‖H_k(X, psi, phi)‖
  ≤ H0(k) exp(-kappa * dM(X, mod Omegaᶜ)).
```

## 12. Headline theorem

The first theorem that genuinely changes the status of the programme should
look like

```lean
theorem wilson_rawYMActivityDecay
    (V : CoarseGaugeField ...)
    (hV : SmallCoarseField V)
    (hparams : PhysicalScaleSmallness params) :
    RawYMActivityDecay
      (wilsonCMP116LocalizedFamily params V)
```

It must not receive fields named `K`, `C`, `B`, `activity`, `hCovDecay`,
`hRootLocal`, or `hraw` as arbitrary inputs.

## 13. Verification gates

Every brick must satisfy:

```bash
lake build YangMillsCore
lake env lean oracle_check.lean
python scripts/check_consistency.py
```

and every headline theorem must print only

```text
[propext, Classical.choice, Quot.sound]
```

or a subset.  A green theorem that merely packages the hard analytic input as a
field of a structure does not close a brick.

## 14. Immediate next target after P4.0

The next implementation target is deliberately narrow:

```lean
flatGaugeHodgePoincare
```

for finite periodic one-cochains, with the constant mode controlled by the
existing block average.  Once this theorem exists, the current
`coercive_add_qMassCLM_of_blockPoincare` and the new exact-covariance layer
compose into a complete flat-background precision/covariance pair.  That pair
is the correct test bed for kernel extraction and a first localized square-root
series before introducing a nontrivial background.
