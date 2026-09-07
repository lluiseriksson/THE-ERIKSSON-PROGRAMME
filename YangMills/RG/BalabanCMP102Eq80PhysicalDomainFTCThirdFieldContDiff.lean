/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80PhysicalDomainFTCThirdFieldDerivative

/-!
# C³ regularity of the literal CMP102 domain FTC potential

The third physical-field derivative of the affine FTC potential was already
constructed as a Bochner integral.  This file supplies the missing regularity
packaging: continuity of that integrated third derivative, then `ContDiff 3`
for the actual literal domain potential.

No derivative or regularity certificate is supplied by a caller.  All three
derivative levels are the source-defined FTC derivatives.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No placeholders or
local axioms.
-/

open MeasureTheory
open scoped Interval

namespace YangMills.RG

noncomputable section

section GenericAffineJetFTCContDiffThree

variable {H E : Type*}
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]

/- Keep the Bochner integral and the derivative ladder on the same
operator-norm instances used by the third-derivative construction. -/
noncomputable local instance contDiffNestedTwoNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] (E →L[ℝ] ℝ)) :=
  ContinuousLinearMap.toNormedAddCommGroup
    (𝕜 := ℝ) (𝕜₂ := ℝ) (E := E) (F := E →L[ℝ] ℝ)
    (σ₁₂ := RingHom.id ℝ)

noncomputable local instance contDiffNestedThreeNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) :=
  ContinuousLinearMap.toNormedAddCommGroup
    (𝕜 := ℝ) (𝕜₂ := ℝ) (E := E)
    (F := E →L[ℝ] (E →L[ℝ] ℝ)) (σ₁₂ := RingHom.id ℝ)

noncomputable local instance contDiffNestedThreeNormedSpace :
    NormedSpace ℝ (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) :=
  ContinuousLinearMap.toNormedSpace
    (𝕜 := ℝ) (𝕜₂ := ℝ) (E := E)
    (F := E →L[ℝ] (E →L[ℝ] ℝ)) (σ₁₂ := RingHom.id ℝ)
    (𝕜' := ℝ)

/-- The integrated third physical-field derivative is continuous. -/
theorem continuous_cmp102AffinePropagatorJetFTCThirdFieldDerivative
    (F : H × E → ℝ) (hF : ContDiff ℝ ⊤ F)
    (n : ℕ) (P T : H) (v : Fin n → H) :
    Continuous
      (cmp102AffinePropagatorJetFTCThirdFieldDerivative
        F n P T v) := by
  apply
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (a₀ := (0 : ℝ)) (b₀ := 1)
  exact
    continuous_cmp102PartialPropagatorJetThirdFieldDerivativeNested_comp
      F hF n
      (fun p : E × ℝ => P + p.2 • T) v
      (fun p : E × ℝ => p.1)
      (by fun_prop) (by fun_prop)

/-- The literal affine propagator-jet FTC contribution is three times
continuously differentiable in the physical field. -/
theorem contDiff_three_cmp102AffinePropagatorJetFTC
    (F : H × E → ℝ) (hF : ContDiff ℝ ⊤ F)
    (n : ℕ) (P T : H) (v : Fin n → H) :
    ContDiff ℝ 3 (cmp102AffinePropagatorJetFTC F n P T v) := by
  have hsecond :
      ContDiff ℝ 1
        (cmp102AffinePropagatorJetFTCSecondFieldDerivative
          F n P T v) :=
    contDiff_one_iff_hasFDerivAt.mpr
      ⟨cmp102AffinePropagatorJetFTCThirdFieldDerivative F n P T v,
        continuous_cmp102AffinePropagatorJetFTCThirdFieldDerivative
          F hF n P T v,
        fun x =>
          cmp102AffinePropagatorJetFTCSecondFieldDerivative_hasFDerivAt
            F hF n P T v x⟩
  have hfirst :
      ContDiff ℝ (1 + 1)
        (cmp102AffinePropagatorJetFTCFirstFieldDerivative
          F n P T v) :=
    contDiff_succ_iff_hasFDerivAt.mpr
      ⟨cmp102AffinePropagatorJetFTCSecondFieldDerivative F n P T v,
        hsecond,
        fun x =>
          cmp102AffinePropagatorJetFTCFirstFieldDerivative_hasFDerivAt
            F hF n P T v x⟩
  have hthird :
      ContDiff ℝ ((1 + 1) + 1)
        (cmp102AffinePropagatorJetFTC F n P T v) :=
    contDiff_succ_iff_hasFDerivAt.mpr
      ⟨cmp102AffinePropagatorJetFTCFirstFieldDerivative F n P T v,
        hfirst,
        fun x =>
          cmp102AffinePropagatorJetFTC_hasFDerivAt
            F hF n P T v x⟩
  simpa using hthird

end GenericAffineJetFTCContDiffThree

private abbrev FineField (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))] :=
  FinePhysicalOneCochain 4 M (2 * Q) Nc

private abbrev CoarseField (Q Nc : ℕ) [NeZero (2 * Q)] :=
  CoarsePhysicalOneCochain 4 (2 * Q) Nc

private abbrev RectangularFieldMap (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))] :=
  CoarseField Q Nc →L[ℝ] FineField M Q Nc

/-- The literal complete-domain equation-(80) FTC contribution is `C³` in
the fine physical field. -/
theorem
    contDiff_three_cmp102Eq80PhysicalFineHeadTailDomainFTCContribution
    {M Q Nc R Δ n : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (anchor : FinBox 4 Q)
    (K : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (baseCoarseCovariance :
      CoarseField Q Nc →L[ℝ] CoarseField Q Nc)
    {Ahead rho rate Rweak : ℝ}
    (hAhead : 0 ≤ Ahead) (hrho : 0 ≤ rho) (hrate : 0 < rate)
    (hgeom : ((2 ^ 4 : ℕ) : ℝ) * Real.exp (-rate) < 1)
    (Cert : CMP99PhysicalPatchWeightedCertificate
      (cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q))
      K cmp99SourcePi4ChartEnlarged
      (cmp99SourcePi4ChartCore (M := M))
      hc hmass hK physicalBondDist Ahead rho rate)
    (hrange : R + 1 ≤ 4 * M)
    (hΔ : ∀ x, (cmp116CoarseFaceAdj 4 Q).degree x ≤ Δ)
    (hΔ1 : 1 ≤ Δ)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (hRweak : 1 ≤ Rweak)
    (hcap : ∀ d, ‖sigma d‖ ≤ Rweak)
    (hsmall :
      ‖cmp116SourcePi4ComplexContourRatio Δ rho Rweak‖ < 1)
    (layerWord : Fin n → ℕ)
    (choice : CMP99SourcePi4CoarseFineWalkChoice M Q R layerWord)
    (D D₃ : FineField M Q Nc → CoarseField Q Nc)
    (V₀ : FineField M Q Nc → ℝ)
    (P T : RectangularFieldMap M Q Nc)
    (Δπ : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    (J : FineField M Q Nc)
    (Y : Finset (FinBox 4 (2 * Q)))
    (hD : ContDiff ℝ ⊤ D) (hD₃ : ContDiff ℝ ⊤ D₃)
    (hV₀ : ContDiff ℝ ⊤ V₀) :
    ContDiff ℝ 3
      (fun A =>
        cmp102Eq80PhysicalFineHeadTailDomainFTCContribution
          anchor K hc hmass hK baseCoarseCovariance
          sigma layerWord choice D D₃ V₀ P T Δπ J A Y) := by
  let Φ :
      RectangularFieldMap M Q Nc × FineField M Q Nc → ℝ := fun p =>
    cmp102Eq80GlobalPotential D D₃ V₀ p.1 Δπ J p.2
  let Kdomain :=
    cmp99PhysicalRectangularOfComplexMatrix
      (cmp102Eq80PhysicalFineHeadTailDomainMatrixCoefficient
        anchor K hc hmass hK baseCoarseCovariance
        sigma layerWord choice Y)
  have hΦ : ContDiff ℝ ⊤ Φ :=
    contDiff_cmp102Eq80JointPotential_rectangular
      D D₃ V₀ Δπ J hD hD₃ hV₀
  have hfun :
      (fun A =>
        cmp102Eq80PhysicalFineHeadTailDomainFTCContribution
          anchor K hc hmass hK baseCoarseCovariance
          sigma layerWord choice D D₃ V₀ P T Δπ J A Y) =
        cmp102AffinePropagatorJetFTC
          Φ 1 P T (fun _ => Kdomain) := by
    funext A
    simpa [Φ, Kdomain] using
      cmp102Eq80PhysicalFineHeadTailDomainFTCContribution_eq_affinePropagatorJetFTC
        anchor K hc hmass hK baseCoarseCovariance
        hAhead hrho hrate hgeom Cert hrange hΔ hΔ1
        sigma hRweak hcap hsmall layerWord choice
        D D₃ V₀ P T Δπ J A Y hD hD₃ hV₀
  rw [hfun]
  exact contDiff_three_cmp102AffinePropagatorJetFTC
    Φ hΦ 1 P T (fun _ => Kdomain)

end

end YangMills.RG
