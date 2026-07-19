/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceDirichletProblem
import YangMills.RG.BalabanCMP99OneScalePhysicalGreenCovariance

/-!
# Typed transitions between consecutive CMP99 source regions

The source regions are nested but their Dirichlet field spaces are genuinely
different types.  This module constructs the literal restriction and zero
extension maps between consecutive spaces and proves the rectangular second
resolvent identity without transporting operators through an equality of
carriers.
-/

namespace YangMills.RG

open scoped RealInnerProductSpace

noncomputable section

variable {Q M j : ℕ} [NeZero Q] [NeZero M]
variable {cell : FinBox 4 Q}

/-- Restriction from `Omega_r` to the smaller consecutive region
`Omega_{r+1}`, implemented through the common ambient lattice. -/
noncomputable def cmp99OmegaTransitionRestriction
    {g : Type*} [NormedAddCommGroup g] [InnerProductSpace ℝ g]
    [FiniteDimensional ℝ g]
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 1)) :
    CMP99OmegaDirichletZeroField (M := M) Seq
        (cmp99OmegaTransitionIndex r) g →L[ℝ]
      CMP99OmegaDirichletZeroField (M := M) Seq
        (cmp99OmegaTransitionNextIndex r) g :=
  (restrictZeroCLM
      (cmp99OmegaActiveGaugeRegion (M := M) Seq
        (cmp99OmegaTransitionNextIndex r))).comp
    (extendZeroZeroCLM
      (cmp99OmegaActiveGaugeRegion (M := M) Seq
        (cmp99OmegaTransitionIndex r)))

/-- Dirichlet zero extension from `Omega_{r+1}` to the larger consecutive
region `Omega_r`. -/
noncomputable def cmp99OmegaTransitionExtension
    {g : Type*} [NormedAddCommGroup g] [InnerProductSpace ℝ g]
    [FiniteDimensional ℝ g]
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 1)) :
    CMP99OmegaDirichletZeroField (M := M) Seq
        (cmp99OmegaTransitionNextIndex r) g →L[ℝ]
      CMP99OmegaDirichletZeroField (M := M) Seq
        (cmp99OmegaTransitionIndex r) g :=
  (restrictZeroCLM
      (cmp99OmegaActiveGaugeRegion (M := M) Seq
        (cmp99OmegaTransitionIndex r))).comp
    (extendZeroZeroCLM
      (cmp99OmegaActiveGaugeRegion (M := M) Seq
        (cmp99OmegaTransitionNextIndex r)))

/-- The smaller region is contained in its consecutive predecessor. -/
theorem cmp99OmegaTransition_region_subset
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 1)) :
    Seq.regions (cmp99OmegaTransitionNextIndex r) ⊆
      Seq.regions (cmp99OmegaTransitionIndex r) := by
  exact Seq.nested (by
    change r.val ≤ r.val + 1
    omega)

/-- Restricting a consecutive zero extension is exactly the identity on the
smaller Dirichlet field space. -/
theorem cmp99OmegaTransitionRestriction_comp_extension
    {g : Type*} [NormedAddCommGroup g] [InnerProductSpace ℝ g]
    [FiniteDimensional ℝ g]
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 1)) :
    (cmp99OmegaTransitionRestriction (M := M) Seq r (g := g)).comp
        (cmp99OmegaTransitionExtension (M := M) Seq r) =
      ContinuousLinearMap.id ℝ
        (CMP99OmegaDirichletZeroField (M := M) Seq
          (cmp99OmegaTransitionNextIndex r) g) := by
  apply ContinuousLinearMap.ext
  intro phi
  ext x
  have hxSmall : blockSite M (2 * Q) x.1 ∈
      Seq.regions (cmp99OmegaTransitionNextIndex r) :=
    (mem_cmp99OmegaActiveGaugeRegion_sites_iff
      (M := M) Seq (cmp99OmegaTransitionNextIndex r) x.1).mp x.2
  have hxLarge : blockSite M (2 * Q) x.1 ∈
      Seq.regions (cmp99OmegaTransitionIndex r) :=
    cmp99OmegaTransition_region_subset Seq r hxSmall
  simp [cmp99OmegaTransitionRestriction, cmp99OmegaTransitionExtension,
    restrictZeroCLM, extendZeroZeroCLM, hxSmall, hxLarge]

/-- Consecutive zero extension preserves the counting Hilbert norm. -/
theorem norm_cmp99OmegaTransitionExtension
    {g : Type*} [NormedAddCommGroup g] [InnerProductSpace ℝ g]
    [FiniteDimensional ℝ g]
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 1))
    (phi : CMP99OmegaDirichletZeroField (M := M) Seq
      (cmp99OmegaTransitionNextIndex r) g) :
    ‖cmp99OmegaTransitionExtension (M := M) Seq r phi‖ = ‖phi‖ := by
  let OmegaLarge := cmp99OmegaActiveGaugeRegion (M := M) Seq
    (cmp99OmegaTransitionIndex r)
  let OmegaSmall := cmp99OmegaActiveGaugeRegion (M := M) Seq
    (cmp99OmegaTransitionNextIndex r)
  let psi := cmp99OmegaTransitionExtension (M := M) Seq r phi
  have hext : extendZeroZeroCLM OmegaLarge psi =
      extendZeroZeroCLM OmegaSmall phi := by
    ext x
    by_cases hxSmall : x ∈ OmegaSmall.sites
    · have hxSmallBlock : blockSite M (2 * Q) x ∈
          Seq.regions (cmp99OmegaTransitionNextIndex r) :=
        (mem_cmp99OmegaActiveGaugeRegion_sites_iff
          (M := M) Seq (cmp99OmegaTransitionNextIndex r) x).mp hxSmall
      have hxLargeBlock : blockSite M (2 * Q) x ∈
          Seq.regions (cmp99OmegaTransitionIndex r) :=
        cmp99OmegaTransition_region_subset Seq r hxSmallBlock
      have hxLarge : x ∈ OmegaLarge.sites :=
        (mem_cmp99OmegaActiveGaugeRegion_sites_iff
          (M := M) Seq (cmp99OmegaTransitionIndex r) x).mpr
          hxLargeBlock
      simp [OmegaLarge, OmegaSmall, psi, cmp99OmegaTransitionExtension,
        restrictZeroCLM, extendZeroZeroCLM, hxSmallBlock, hxLargeBlock]
    · by_cases hxLarge : x ∈ OmegaLarge.sites
      · have hxSmallBlock : blockSite M (2 * Q) x ∉
            Seq.regions (cmp99OmegaTransitionNextIndex r) := by
          intro h
          exact hxSmall ((mem_cmp99OmegaActiveGaugeRegion_sites_iff
            (M := M) Seq (cmp99OmegaTransitionNextIndex r) x).mpr h)
        have hxLargeBlock : blockSite M (2 * Q) x ∈
            Seq.regions (cmp99OmegaTransitionIndex r) :=
          (mem_cmp99OmegaActiveGaugeRegion_sites_iff
            (M := M) Seq (cmp99OmegaTransitionIndex r) x).mp hxLarge
        simp [OmegaLarge, OmegaSmall, psi, cmp99OmegaTransitionExtension,
          restrictZeroCLM, extendZeroZeroCLM, hxSmallBlock, hxLargeBlock]
      · have hxSmallBlock : blockSite M (2 * Q) x ∉
            Seq.regions (cmp99OmegaTransitionNextIndex r) := by
          intro h
          exact hxSmall ((mem_cmp99OmegaActiveGaugeRegion_sites_iff
            (M := M) Seq (cmp99OmegaTransitionNextIndex r) x).mpr h)
        have hxLargeBlock : blockSite M (2 * Q) x ∉
            Seq.regions (cmp99OmegaTransitionIndex r) := by
          intro h
          exact hxLarge ((mem_cmp99OmegaActiveGaugeRegion_sites_iff
            (M := M) Seq (cmp99OmegaTransitionIndex r) x).mpr h)
        simp [OmegaLarge, OmegaSmall, psi, cmp99OmegaTransitionExtension,
          restrictZeroCLM, extendZeroZeroCLM, hxSmallBlock, hxLargeBlock]
  calc
    ‖psi‖ = ‖extendZeroZeroCLM OmegaLarge psi‖ :=
      (norm_cmp99Omega_extendZeroZeroCLM
        (M := M) Seq (cmp99OmegaTransitionIndex r) psi).symm
    _ = ‖extendZeroZeroCLM OmegaSmall phi‖ := congrArg norm hext
    _ = ‖phi‖ := norm_cmp99Omega_extendZeroZeroCLM
      (M := M) Seq (cmp99OmegaTransitionNextIndex r) phi

/-- Rectangular precision defect for two operators acting on different
Dirichlet spaces. -/
noncomputable def cmp99TypedPrecisionDefect
    {Eₗ Eₛ : Type*}
    [NormedAddCommGroup Eₗ] [InnerProductSpace ℝ Eₗ]
    [NormedAddCommGroup Eₛ] [InnerProductSpace ℝ Eₛ]
    (Kₗ : Eₗ →L[ℝ] Eₗ) (Kₛ : Eₛ →L[ℝ] Eₛ)
    (R : Eₗ →L[ℝ] Eₛ) : Eₗ →L[ℝ] Eₛ :=
  R.comp Kₗ - Kₛ.comp R

/-- Exact second-resolvent identity across different Hilbert spaces.  Only
the two-sided inverse equations are used. -/
theorem typedGreen_transition_resolvent
    {Eₗ Eₛ : Type*}
    [NormedAddCommGroup Eₗ] [InnerProductSpace ℝ Eₗ]
    [NormedAddCommGroup Eₛ] [InnerProductSpace ℝ Eₛ]
    (Kₗ : Eₗ →L[ℝ] Eₗ) (Kₛ : Eₛ →L[ℝ] Eₛ)
    (Gₗ : Eₗ →L[ℝ] Eₗ) (Gₛ : Eₛ →L[ℝ] Eₛ)
    (R : Eₗ →L[ℝ] Eₛ)
    (hKₗGₗ : Kₗ.comp Gₗ = ContinuousLinearMap.id ℝ Eₗ)
    (hGₛKₛ : Gₛ.comp Kₛ = ContinuousLinearMap.id ℝ Eₛ) :
    Gₛ.comp R - R.comp Gₗ =
      Gₛ.comp ((cmp99TypedPrecisionDefect Kₗ Kₛ R).comp Gₗ) := by
  apply ContinuousLinearMap.ext
  intro x
  have hlarge : Kₗ (Gₗ x) = x := by
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply]
      using congrArg (fun f => f x) hKₗGₗ
  have hsmall : ∀ y, Gₛ (Kₛ y) = y := by
    intro y
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply]
      using congrArg (fun f => f y) hGₛKₛ
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
    cmp99TypedPrecisionDefect, map_sub]
  rw [hlarge, hsmall]

/-- C2 for the literal one-step CMP99 physical precisions and Greens on two
consecutive source regions.  Every operator is typed on its own Dirichlet
space and the inter-region map is the physical restriction above. -/
theorem cmp99OmegaSourcePhysicalOneStepGreen_transition_resolvent
    {Nc : ℕ} [NeZero Nc]
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 1))
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc)
    {spacing a : ℝ} (hspacing : 0 < spacing) (ha : 0 < a) :
    (cmp99OmegaSourcePhysicalOneStepGreen Seq
        (cmp99OmegaTransitionNextIndex r) rho U hspacing ha).comp
        (cmp99OmegaTransitionRestriction (M := M) Seq r) -
      (cmp99OmegaTransitionRestriction (M := M) Seq r).comp
        (cmp99OmegaSourcePhysicalOneStepGreen Seq
          (cmp99OmegaTransitionIndex r) rho U hspacing ha) =
      (cmp99OmegaSourcePhysicalOneStepGreen Seq
        (cmp99OmegaTransitionNextIndex r) rho U hspacing ha).comp
        ((cmp99TypedPrecisionDefect
          (cmp99OmegaSourcePhysicalOneStepGaugePrecision Seq
            (cmp99OmegaTransitionIndex r) rho U spacing a)
          (cmp99OmegaSourcePhysicalOneStepGaugePrecision Seq
            (cmp99OmegaTransitionNextIndex r) rho U spacing a)
          (cmp99OmegaTransitionRestriction (M := M) Seq r)).comp
            (cmp99OmegaSourcePhysicalOneStepGreen Seq
              (cmp99OmegaTransitionIndex r) rho U hspacing ha)) := by
  exact typedGreen_transition_resolvent
    (cmp99OmegaSourcePhysicalOneStepGaugePrecision Seq
      (cmp99OmegaTransitionIndex r) rho U spacing a)
    (cmp99OmegaSourcePhysicalOneStepGaugePrecision Seq
      (cmp99OmegaTransitionNextIndex r) rho U spacing a)
    (cmp99OmegaSourcePhysicalOneStepGreen Seq
      (cmp99OmegaTransitionIndex r) rho U hspacing ha)
    (cmp99OmegaSourcePhysicalOneStepGreen Seq
      (cmp99OmegaTransitionNextIndex r) rho U hspacing ha)
    (cmp99OmegaTransitionRestriction (M := M) Seq r)
    (cmp99OmegaSourcePhysicalOneStepPrecision_comp_green Seq
      (cmp99OmegaTransitionIndex r) rho U hspacing ha)
    (cmp99OmegaSourcePhysicalOneStepGreen_comp_precision Seq
      (cmp99OmegaTransitionNextIndex r) rho U hspacing ha)

end

end YangMills.RG
