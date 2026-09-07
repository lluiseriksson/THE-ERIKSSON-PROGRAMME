/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceEq395CovarianceOnSourceDecay
import YangMills.RG.BalabanCMP99SourceEq395RegionalMiddleCommutatorDecay

/-!
# Ambient decay of the regional covariance in CMP99 equation (3.95)

The generated inverse is first identified with the canonical source-region
covariance and is then extended by zero to the common ambient field.  Its
fixed-rate exponential estimate is therefore inherited without a
volume-dependent loss.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

universe v

variable {M Nc Q j : ℕ} [NeZero M] [NeZero Nc] [NeZero Q]
variable {ScaleSite : Fin (j + 2) → Type v}
variable [∀ r, DecidableEq (ScaleSite r)]
variable {Scaled : CMP99SourceScaledStratification
  (FinBox 4 (2 * Q)) (j + 2) ScaleSite}
variable {dist : FinBox 4 (2 * Q) → FinBox 4 (2 * Q) → ℕ}
variable {gap : Fin (j + 1) → ℕ}

namespace CMP99SourceDependentOmegaGeometry

/-- The regional coordinate realization is definitionally the canonical
source-region transport of the generated covariance. -/
theorem generatedPhysicalCoarseCovarianceCoordinates_eq_onSource
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (s : Fin (j + 2)) (hM : 2 ≤ M) (depth : ℕ)
    {spacing epsilon : ℝ} (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1) :
    D.generatedPhysicalCoarseCovarianceCoordinates hpi5 s hM depth
        hspacing background budget fineSmall hsmall =
      cmp99Eq395GeneratedPhysicalCovarianceOnSource
        (D.operatorCoarseRegion hpi5 s) hM depth hspacing background budget
        fineSmall hsmall := by
  rfl

set_option maxRecDepth 5000 in
set_option maxHeartbeats 2000000 in
/-- The literal regional covariance, extended to the ambient field, inherits
the volume-independent inverse-decay estimate of its source realization. -/
theorem generatedPhysicalCoarseCovarianceAmbient_exponentialKernelBound
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (s : Fin (j + 2)) (hM : 2 ≤ M) (depth : ℕ)
    {spacing epsilon : ℝ} (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1) :
    let C : CMP99Eq395AmbientOperator Q Nc :=
      D.generatedPhysicalCoarseCovarianceAmbient hpi5 s hM depth
        hspacing background budget fineSmall hsmall
    let coercivity := ((cmp99SourceGeneratedPhysicalPrecisionUpperBound
      4 M (depth + 1) spacing epsilon) ^ 2)⁻¹
    FinitePiLpTypedExponentialKernelBound C
      (finBoxDist : FinBox 4 (2 * Q) → FinBox 4 (2 * Q) → ℕ)
      (2 / coercivity)
      (cmp99Eq395GeneratedCovarianceDecayRate M depth spacing epsilon) := by
  dsimp only
  let Omega := D.operatorCoarseRegion hpi5 s
  let C := cmp99Eq395GeneratedPhysicalCovarianceOnSource Omega hM depth
    hspacing background budget fineSmall hsmall
  have hC := cmp99Eq395GeneratedPhysicalCovarianceOnSource_exponentialKernelBound
    Omega hM depth hspacing background budget fineSmall hsmall
  unfold generatedPhysicalCoarseCovarianceAmbient
  rw [D.generatedPhysicalCoarseCovarianceCoordinates_eq_onSource]
  refine ⟨hC.1, hC.2.1, ?_⟩
  intro source target v
  by_cases hsource : source ∈ Omega.sites
  · by_cases htarget : target ∈ Omega.sites
    · let sourceOmega : ActiveGaugeRegion.Site Omega := ⟨source, hsource⟩
      let targetOmega : ActiveGaugeRegion.Site Omega := ⟨target, htarget⟩
      have hrestrict :
          restrictZeroCLM Omega (singleFinitePiLp source v) =
            singleFinitePiLp sourceOmega v := by
        apply PiLp.ext
        intro x
        by_cases hx : x.1 = source
        · have heq : x = sourceOmega := Subtype.ext hx
          subst x
          simp [restrictZeroCLM, sourceOmega]
        · have hne : x ≠ sourceOmega := by
            intro heq
            exact hx (congrArg Subtype.val heq)
          simp [restrictZeroCLM, singleFinitePiLp, hx, hne]
      change ‖extendZeroZeroCLM Omega
          (C (restrictZeroCLM Omega (singleFinitePiLp source v))) target‖ ≤ _
      rw [extendZeroZeroCLM_apply_of_mem Omega _ target htarget, hrestrict]
      change ‖C (singleFinitePiLp sourceOmega v) targetOmega‖ ≤ _
      exact hC.2.2 sourceOmega targetOmega v
    · change ‖extendZeroZeroCLM Omega
          (C (restrictZeroCLM Omega (singleFinitePiLp source v))) target‖ ≤ _
      simp [extendZeroZeroCLM, htarget]
      positivity [cmp99SourceGeneratedPhysicalPrecisionUpperBound_pos
        4 M (depth + 1) (epsilon := epsilon) hspacing]
  · have hrestrict : restrictZeroCLM Omega
        (singleFinitePiLp source v) = 0 := by
      apply PiLp.ext
      intro x
      have hne : x.1 ≠ source := by
        intro heq
        apply hsource
        simpa [heq] using x.2
      simp [restrictZeroCLM, singleFinitePiLp, hne]
    change ‖extendZeroZeroCLM Omega
        (C (restrictZeroCLM Omega (singleFinitePiLp source v))) target‖ ≤ _
    rw [hrestrict]
    simp only [map_zero, PiLp.zero_apply, norm_zero]
    positivity [cmp99SourceGeneratedPhysicalPrecisionUpperBound_pos
      4 M (depth + 1) (epsilon := epsilon) hspacing]

end CMP99SourceDependentOmegaGeometry

end

end YangMills.RG
