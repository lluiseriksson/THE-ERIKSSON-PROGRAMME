/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.PhysicalGaugeFixedPrecision

/-!
# Source-facing localization API for physical gauge covariance

This module does **not** prove decay of the physical covariance.  It records the
coordinate-level API that a later analytic source theorem must feed:

* single-bond delta cochains;
* pointwise kernel bounds for a covariance operator;
* finite-range and exponential-decay source-facing predicates;
* a certificate bundling exact inverse covariance identities with a supplied
  localization hypothesis.

The endpoint is intentionally honest: localization is an explicit field, not a
consequence of finite-dimensional coercivity.
-/

namespace YangMills.RG

open scoped RealInnerProductSpace

/-- Single-site source cochain on physical positive bonds.

This is the coordinate probe used by kernel estimates: insert a Lie-algebra
coordinate `v` at the source bond `p` and zero elsewhere. -/
noncomputable def singlePhysicalBondCochain
    {d N Nc : ℕ} [NeZero N]
    (p : PhysicalBond d N) (v : SUNLieCoord Nc) :
    PhysicalGaugeOneCochain d N Nc :=
  WithLp.toLp 2 fun q : PhysicalBond d N => if q = p then v else 0

@[simp]
theorem singlePhysicalBondCochain_self
    {d N Nc : ℕ} [NeZero N]
    (p : PhysicalBond d N) (v : SUNLieCoord Nc) :
    singlePhysicalBondCochain (d := d) (N := N) (Nc := Nc) p v p = v := by
  simp [singlePhysicalBondCochain]

@[simp]
theorem singlePhysicalBondCochain_of_ne
    {d N Nc : ℕ} [NeZero N]
    {p q : PhysicalBond d N} (v : SUNLieCoord Nc)
    (hqp : q ≠ p) :
    singlePhysicalBondCochain (d := d) (N := N) (Nc := Nc) p v q = 0 := by
  simp [singlePhysicalBondCochain, hqp]

/-- Source-facing pointwise kernel bound for a physical covariance operator.

The convention is `weight target source`: the covariance is probed at `source`
by `singlePhysicalBondCochain source v`, then evaluated at `target`. -/
def PhysicalCovarianceKernelBound
    {d N Nc : ℕ} [NeZero N]
    (C :
      PhysicalGaugeOneCochain d N Nc →L[ℝ]
        PhysicalGaugeOneCochain d N Nc)
    (weight : PhysicalBond d N → PhysicalBond d N → ℝ) : Prop :=
  ∀ source target (v : SUNLieCoord Nc),
    ‖C (singlePhysicalBondCochain (d := d) (N := N) (Nc := Nc) source v)
        target‖ ≤
      weight target source * ‖v‖

/-- Source-facing finite-range covariance localization.  The distance is kept
as a parameter because the correct Balaban block/modified metric is a source
choice, not a theorem of this file. -/
def PhysicalCovarianceFiniteRange
    {d N Nc : ℕ} [NeZero N]
    (C :
      PhysicalGaugeOneCochain d N Nc →L[ℝ]
        PhysicalGaugeOneCochain d N Nc)
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ)
    (R : ℕ) : Prop :=
  ∀ source target (v : SUNLieCoord Nc),
    R < dist target source →
      C (singlePhysicalBondCochain (d := d) (N := N) (Nc := Nc) source v)
        target = 0

/-- Source-facing exponential covariance kernel bound.  This is the natural
shape expected before turning the covariance or its square root into localized
Gaussian activities. -/
def PhysicalCovarianceExponentialKernelBound
    {d N Nc : ℕ} [NeZero N]
    (C :
      PhysicalGaugeOneCochain d N Nc →L[ℝ]
        PhysicalGaugeOneCochain d N Nc)
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ)
    (A κ : ℝ) : Prop :=
  0 ≤ A ∧ 0 < κ ∧
    ∀ source target (v : SUNLieCoord Nc),
      ‖C (singlePhysicalBondCochain (d := d) (N := N) (Nc := Nc) source v)
          target‖ ≤
        A * Real.exp (-(κ * (dist target source : ℝ))) * ‖v‖

/-- Exponential localization is a kernel bound with the corresponding
exponential weight. -/
theorem physicalCovarianceKernelBound_of_exponential
    {d N Nc : ℕ} [NeZero N]
    (C :
      PhysicalGaugeOneCochain d N Nc →L[ℝ]
        PhysicalGaugeOneCochain d N Nc)
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ)
    {A κ : ℝ}
    (hexp : PhysicalCovarianceExponentialKernelBound C dist A κ) :
    PhysicalCovarianceKernelBound C
      (fun target source =>
        A * Real.exp (-(κ * (dist target source : ℝ)))) := by
  intro source target v
  simpa [PhysicalCovarianceKernelBound] using hexp.2.2 source target v

/-- Exact covariance plus a supplied source-facing localization theorem.

This certificate is deliberately generic in the covariance and precision.  The
flat gauge-fixed theorem below instantiates it with
`flatGaugeFixedPrecisionCLM` and `flatGaugeFixedCovarianceCLM`. -/
structure PhysicalLocalizedCovarianceCertificate
    {d N Nc : ℕ} [NeZero N]
    (precision covariance :
      PhysicalGaugeOneCochain d N Nc →L[ℝ]
        PhysicalGaugeOneCochain d N Nc)
    (normBound : ℝ)
    (weight : PhysicalBond d N → PhysicalBond d N → ℝ) : Prop where
  covariance_comp_precision :
    covariance.comp precision =
      ContinuousLinearMap.id ℝ (PhysicalGaugeOneCochain d N Nc)
  precision_comp_covariance :
    precision.comp covariance =
      ContinuousLinearMap.id ℝ (PhysicalGaugeOneCochain d N Nc)
  covariance_norm_bound :
    ‖covariance‖ ≤ normBound
  covariance_psd :
    ∀ y : PhysicalGaugeOneCochain d N Nc,
      0 ≤ inner ℝ y (covariance y)
  kernel_bound :
    PhysicalCovarianceKernelBound covariance weight

/-- The fixed-volume flat physical covariance becomes a localized covariance
certificate as soon as a source theorem supplies the kernel bound.

All analytic locality remains in `hkernel`; this theorem only bundles it with
the already-verified inverse identities, operator norm bound, and PSD
quadratic form. -/
theorem flatGaugeFixedLocalizedCovarianceCertificate_of_kernelBound
    {ι : Type*}
    {d L N' Nc : ℕ}
    [NeZero d] [NeZero L] [NeZero N'] [NeZero Nc]
    (ρ : SUNAdjointModel Nc)
    (Sigma :
      ι →
        FinePhysicalOneCochain d L N' Nc →L[ℝ]
          FinePhysicalOneCochain d L N' Nc)
    (δ : ι → ℝ)
    {a CP : ℝ}
    (ha : 0 < a)
    (hP : FlatGaugeHodgePoincare d L N' Nc ρ CP)
    (hδ : Summable δ)
    (hSigmaδ :
      ∀ i, ‖Sigma i‖ ≤ δ i)
    (hbudget :
      (∑' i, δ i) < min 1 a / CP)
    (weight :
      PhysicalBond d (L * N') → PhysicalBond d (L * N') → ℝ)
    (hkernel :
      PhysicalCovarianceKernelBound
        (flatGaugeFixedCovarianceCLM
          ρ Sigma δ ha hP hδ hSigmaδ hbudget)
        weight) :
    PhysicalLocalizedCovarianceCertificate
      (flatGaugeFixedPrecisionCLM d L N' Nc ρ a Sigma)
      (flatGaugeFixedCovarianceCLM
        ρ Sigma δ ha hP hδ hSigmaδ hbudget)
      (gaugeFixedResidualCoercivityConstant δ a CP)⁻¹
      weight := by
  refine
    { covariance_comp_precision := ?_
      precision_comp_covariance := ?_
      covariance_norm_bound := ?_
      covariance_psd := ?_
      kernel_bound := hkernel }
  · exact
      flatGaugeFixedCovarianceCLM_comp_precision
        ρ Sigma δ ha hP hδ hSigmaδ hbudget
  · exact
      precision_comp_flatGaugeFixedCovarianceCLM
        ρ Sigma δ ha hP hδ hSigmaδ hbudget
  · exact
      norm_flatGaugeFixedCovarianceCLM_le
        ρ Sigma δ ha hP hδ hSigmaδ hbudget
  · intro y
    exact
      flatGaugeFixedCovarianceCLM_psd
        ρ Sigma δ ha hP hδ hSigmaδ hbudget y

/-- Source-facing covariance-root certificate.

This is the next interface after a localized covariance certificate: a future
source theorem may identify a concrete square root (or Gaussian-coordinate
map) `root` and prove its own norm and kernel bounds.  The square-root
semantics are deliberately fields, not consequences of the covariance
certificate. -/
structure PhysicalLocalizedCovarianceRootCertificate
    {d N Nc : ℕ} [NeZero N]
    (precision covariance root :
      PhysicalGaugeOneCochain d N Nc →L[ℝ]
        PhysicalGaugeOneCochain d N Nc)
    (covNormBound rootNormBound : ℝ)
    (covWeight rootWeight :
      PhysicalBond d N → PhysicalBond d N → ℝ) : Prop where
  covariance_certificate :
    PhysicalLocalizedCovarianceCertificate
      precision covariance covNormBound covWeight
  root_square :
    root.comp root = covariance
  root_norm_bound :
    ‖root‖ ≤ rootNormBound
  root_selfAdjoint_form :
    ∀ x y : PhysicalGaugeOneCochain d N Nc,
      inner ℝ x (root y) = inner ℝ (root x) y
  root_psd :
    ∀ y : PhysicalGaugeOneCochain d N Nc,
      0 ≤ inner ℝ y (root y)
  root_kernel_bound :
    PhysicalCovarianceKernelBound root rootWeight

/-- Assemble a localized covariance-root certificate from explicit source
inputs.

This theorem performs no spectral construction; it only packages a localized
covariance certificate together with source-supplied square-root data. -/
theorem physicalLocalizedCovarianceRootCertificate_of_source
    {d N Nc : ℕ} [NeZero N]
    {precision covariance root :
      PhysicalGaugeOneCochain d N Nc →L[ℝ]
        PhysicalGaugeOneCochain d N Nc}
    {covNormBound rootNormBound : ℝ}
    {covWeight rootWeight :
      PhysicalBond d N → PhysicalBond d N → ℝ}
    (hcov :
      PhysicalLocalizedCovarianceCertificate
        precision covariance covNormBound covWeight)
    (hrootSquare : root.comp root = covariance)
    (hrootNorm : ‖root‖ ≤ rootNormBound)
    (hrootSelfAdjoint :
      ∀ x y : PhysicalGaugeOneCochain d N Nc,
        inner ℝ x (root y) = inner ℝ (root x) y)
    (hrootPsd :
      ∀ y : PhysicalGaugeOneCochain d N Nc,
        0 ≤ inner ℝ y (root y))
    (hrootKernel :
      PhysicalCovarianceKernelBound root rootWeight) :
    PhysicalLocalizedCovarianceRootCertificate
      precision covariance root covNormBound rootNormBound covWeight
      rootWeight := by
  exact
    { covariance_certificate := hcov
      root_square := hrootSquare
      root_norm_bound := hrootNorm
      root_selfAdjoint_form := hrootSelfAdjoint
      root_psd := hrootPsd
      root_kernel_bound := hrootKernel }

/-- The fixed-volume flat physical covariance admits a localized root
certificate as soon as source theorems supply the root identity and root
localization.

The theorem intentionally does not construct `root`.  It keeps the missing
analysis visible as `hrootSquare`, `hrootNorm`, `hrootSelfAdjoint`,
`hrootPsd`, and `hrootKernel`. -/
theorem flatGaugeFixedLocalizedCovarianceRootCertificate_of_source
    {ι : Type*}
    {d L N' Nc : ℕ}
    [NeZero d] [NeZero L] [NeZero N'] [NeZero Nc]
    (ρ : SUNAdjointModel Nc)
    (Sigma :
      ι →
        FinePhysicalOneCochain d L N' Nc →L[ℝ]
          FinePhysicalOneCochain d L N' Nc)
    (δ : ι → ℝ)
    {a CP rootNormBound : ℝ}
    (ha : 0 < a)
    (hP : FlatGaugeHodgePoincare d L N' Nc ρ CP)
    (hδ : Summable δ)
    (hSigmaδ :
      ∀ i, ‖Sigma i‖ ≤ δ i)
    (hbudget :
      (∑' i, δ i) < min 1 a / CP)
    (root :
      FinePhysicalOneCochain d L N' Nc →L[ℝ]
        FinePhysicalOneCochain d L N' Nc)
    (covWeight rootWeight :
      PhysicalBond d (L * N') → PhysicalBond d (L * N') → ℝ)
    (hcovKernel :
      PhysicalCovarianceKernelBound
        (flatGaugeFixedCovarianceCLM
          ρ Sigma δ ha hP hδ hSigmaδ hbudget)
        covWeight)
    (hrootSquare :
      root.comp root =
        flatGaugeFixedCovarianceCLM
          ρ Sigma δ ha hP hδ hSigmaδ hbudget)
    (hrootNorm : ‖root‖ ≤ rootNormBound)
    (hrootSelfAdjoint :
      ∀ x y : FinePhysicalOneCochain d L N' Nc,
        inner ℝ x (root y) = inner ℝ (root x) y)
    (hrootPsd :
      ∀ y : FinePhysicalOneCochain d L N' Nc,
        0 ≤ inner ℝ y (root y))
    (hrootKernel :
      PhysicalCovarianceKernelBound root rootWeight) :
    PhysicalLocalizedCovarianceRootCertificate
      (flatGaugeFixedPrecisionCLM d L N' Nc ρ a Sigma)
      (flatGaugeFixedCovarianceCLM
        ρ Sigma δ ha hP hδ hSigmaδ hbudget)
      root
      (gaugeFixedResidualCoercivityConstant δ a CP)⁻¹
      rootNormBound
      covWeight
      rootWeight := by
  exact
    physicalLocalizedCovarianceRootCertificate_of_source
      (flatGaugeFixedLocalizedCovarianceCertificate_of_kernelBound
        ρ Sigma δ ha hP hδ hSigmaδ hbudget covWeight hcovKernel)
      hrootSquare hrootNorm hrootSelfAdjoint hrootPsd hrootKernel

end YangMills.RG
