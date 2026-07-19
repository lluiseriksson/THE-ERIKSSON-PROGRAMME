/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceRegionTransition
import YangMills.RG.BalabanCMP116GaugeFixingMassDefect

/-!
# Boundary support of consecutive CMP99 source Laplacians

The exact mass cancellation leaves a rectangular defect of regional
covariant Laplacians.  This file identifies every regional Laplacian with a
Dirichlet compression of one ambient nearest-neighbour operator and records
its explicit stencil.  The resulting support theorem uses the inner collar
of the smaller region; the removed shell itself is not a valid output type.
-/

namespace YangMills.RG

open YangMills
open scoped RealInnerProductSpace

noncomputable section

variable {Q M j Nc : ℕ} [NeZero Q] [NeZero M] [NeZero Nc]
variable {cell : FinBox 4 Q}

/-- Restriction is exactly the counting-Hilbert adjoint of source-region
zero extension. -/
theorem cmp99Omega_restrictZero_eq_extendZero_adjoint
    {g : Type*} [NormedAddCommGroup g] [InnerProductSpace ℝ g]
    [FiniteDimensional ℝ g]
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 2)) :
    restrictZeroCLM (𝔤 := g)
        (cmp99OmegaActiveGaugeRegion (M := M) Seq r) =
      (extendZeroZeroCLM
        (𝔤 := g) (cmp99OmegaActiveGaugeRegion (M := M) Seq r)).adjoint := by
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro f phi
  calc
    inner ℝ
        (restrictZeroCLM
          (cmp99OmegaActiveGaugeRegion (M := M) Seq r) f) phi =
      inner ℝ phi
        (restrictZeroCLM
          (cmp99OmegaActiveGaugeRegion (M := M) Seq r) f) :=
        real_inner_comm _ _
    _ = inner ℝ
        (extendZeroZeroCLM
          (cmp99OmegaActiveGaugeRegion (M := M) Seq r) phi) f :=
      inner_cmp99Omega_restrictZero_eq_extendZero
        (M := M) Seq r phi f
    _ = inner ℝ f
        (extendZeroZeroCLM
          (cmp99OmegaActiveGaugeRegion (M := M) Seq r) phi) :=
      real_inner_comm _ _

/-- The scaled covariant Laplacian before imposing a regional Dirichlet
boundary. -/
noncomputable def cmp99AmbientScaledCovariantLaplacian
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc)
    (spacing : ℝ) :
    PhysicalGaugeZeroCochain 4 (M * (2 * Q)) Nc →L[ℝ]
      PhysicalGaugeZeroCochain 4 (M * (2 * Q)) Nc :=
  (spacing⁻¹ • covariantD0CLM rho U).adjoint.comp
    (spacing⁻¹ • covariantD0CLM rho U)

/-- The source regional Laplacian is pointwise the Dirichlet compression of
the single ambient scaled covariant Laplacian. -/
theorem cmp99OmegaSourceCovariantLaplacian_apply_eq_dirichletCompression
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 2))
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc)
    (spacing : ℝ)
    (phi : CMP99OmegaDirichletZeroField
      (M := M) Seq r (SUNLieCoord Nc)) :
    cmp99OmegaSourceCovariantLaplacian Seq r rho U spacing phi =
      restrictZeroCLM (cmp99OmegaActiveGaugeRegion (M := M) Seq r)
        (cmp99AmbientScaledCovariantLaplacian rho U spacing
          (extendZeroZeroCLM
            (cmp99OmegaActiveGaugeRegion (M := M) Seq r) phi)) := by
  let E : CMP99OmegaDirichletZeroField
      (M := M) Seq r (SUNLieCoord Nc) →L[ℝ]
        PhysicalGaugeZeroCochain 4 (M * (2 * Q)) Nc :=
    extendZeroZeroCLM (cmp99OmegaActiveGaugeRegion (M := M) Seq r)
  let R : PhysicalGaugeZeroCochain 4 (M * (2 * Q)) Nc →L[ℝ]
      CMP99OmegaDirichletZeroField (M := M) Seq r (SUNLieCoord Nc) :=
    restrictZeroCLM (cmp99OmegaActiveGaugeRegion (M := M) Seq r)
  let D : PhysicalGaugeZeroCochain 4 (M * (2 * Q)) Nc →L[ℝ]
      PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc :=
    spacing⁻¹ • covariantD0CLM rho U
  have hR : R = E.adjoint :=
    cmp99Omega_restrictZero_eq_extendZero_adjoint (M := M) Seq r
  change (D.comp E).adjoint (D.comp E phi) =
    R ((D.adjoint.comp D) (E phi))
  rw [ContinuousLinearMap.adjoint_comp, hR]
  rfl

/-- Explicit nearest-neighbour stencil of the ambient scaled covariant
Laplacian. -/
theorem cmp99AmbientScaledCovariantLaplacian_apply
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc)
    (spacing : ℝ)
    (phi : PhysicalGaugeZeroCochain 4 (M * (2 * Q)) Nc)
    (x : FinBox 4 (M * (2 * Q))) :
    cmp99AmbientScaledCovariantLaplacian rho U spacing phi x =
      spacing⁻¹ •
        ∑ i : Fin 4,
          ((spacing⁻¹ • covariantD0CLM rho U phi) (x, i) -
            rho.adCLM
              (U (positiveEdgeOfPhysicalBond
                ((FinBox.shiftBack x i, i) :
                  PhysicalBond 4 (M * (2 * Q)))))⁻¹
              ((spacing⁻¹ • covariantD0CLM rho U phi)
                (FinBox.shiftBack x i, i))) := by
  rw [cmp99AmbientScaledCovariantLaplacian]
  rw [map_smul]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply]
  change (spacing⁻¹ • (covariantD0CLM rho U).adjoint)
      (spacing⁻¹ • covariantD0CLM rho U phi) x = _
  rw [ContinuousLinearMap.smul_apply]
  exact congrArg (fun z => spacing⁻¹ • z)
    (gaugeConstraintQCLM_apply_background rho U
      (spacing⁻¹ • covariantD0CLM rho U phi) x)

/-- A nearest-neighbour field which vanishes at a site and all of its forward
and backward neighbours has zero ambient Laplacian at that site. -/
theorem cmp99AmbientScaledCovariantLaplacian_apply_eq_zero
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc)
    (spacing : ℝ)
    (phi : PhysicalGaugeZeroCochain 4 (M * (2 * Q)) Nc)
    (x : FinBox 4 (M * (2 * Q)))
    (hzero : phi x = 0)
    (hforward : ∀ i : Fin 4, phi (x.shift i) = 0)
    (hback : ∀ i : Fin 4, phi (x.shiftBack i) = 0) :
    cmp99AmbientScaledCovariantLaplacian rho U spacing phi x = 0 := by
  rw [cmp99AmbientScaledCovariantLaplacian_apply]
  apply smul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro i _hi
  have hbackShift : phi ((x.shiftBack i).shift i) = 0 := by
    rw [FinBox.shift_shiftBack]
    exact hzero
  simp [covariantD0CLM_apply, hzero, hforward i, hback i, hbackShift]

/-- Inner one-link collar of the smaller member of a consecutive source
transition. -/
noncomputable def cmp99OmegaTransitionInnerCollar
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 1)) :
    Finset (FinBox 4 (M * (2 * Q))) :=
  (cmp99OmegaActiveGaugeRegion (M := M) Seq
    (cmp99OmegaTransitionNextIndex r)).sites.filter fun x =>
      ∃ i : Fin 4,
        x.shift i ∉
            (cmp99OmegaActiveGaugeRegion (M := M) Seq
              (cmp99OmegaTransitionNextIndex r)).sites ∨
          x.shiftBack i ∉
            (cmp99OmegaActiveGaugeRegion (M := M) Seq
              (cmp99OmegaTransitionNextIndex r)).sites

@[simp] theorem mem_cmp99OmegaTransitionInnerCollar_iff
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 1))
    (x : FinBox 4 (M * (2 * Q))) :
    x ∈ cmp99OmegaTransitionInnerCollar (M := M) Seq r ↔
      x ∈ (cmp99OmegaActiveGaugeRegion (M := M) Seq
          (cmp99OmegaTransitionNextIndex r)).sites ∧
        ∃ i : Fin 4,
          x.shift i ∉
              (cmp99OmegaActiveGaugeRegion (M := M) Seq
                (cmp99OmegaTransitionNextIndex r)).sites ∨
            x.shiftBack i ∉
              (cmp99OmegaActiveGaugeRegion (M := M) Seq
                (cmp99OmegaTransitionNextIndex r)).sites := by
  simp [cmp99OmegaTransitionInnerCollar]

/-- On every site of the smaller region, extending after restriction agrees
pointwise with the original extension from the larger region. -/
theorem cmp99OmegaTransition_extend_restrict_apply
    {g : Type*} [NormedAddCommGroup g] [InnerProductSpace ℝ g]
    [FiniteDimensional ℝ g]
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 1))
    (phi : CMP99OmegaDirichletZeroField (M := M) Seq
      (cmp99OmegaTransitionIndex r) g)
    (x : FinBox 4 (M * (2 * Q)))
    (hx : x ∈ (cmp99OmegaActiveGaugeRegion (M := M) Seq
      (cmp99OmegaTransitionNextIndex r)).sites) :
    extendZeroZeroCLM
        (cmp99OmegaActiveGaugeRegion (M := M) Seq
          (cmp99OmegaTransitionIndex r)) phi x =
      extendZeroZeroCLM
        (cmp99OmegaActiveGaugeRegion (M := M) Seq
          (cmp99OmegaTransitionNextIndex r))
        (cmp99OmegaTransitionRestriction (M := M) Seq r phi) x := by
  have hxSmallRegion : blockSite M (2 * Q) x ∈
      Seq.regions (cmp99OmegaTransitionNextIndex r) :=
    (mem_cmp99OmegaActiveGaugeRegion_sites_iff
      (M := M) Seq (cmp99OmegaTransitionNextIndex r) x).mp hx
  have hxLargeRegion : blockSite M (2 * Q) x ∈
      Seq.regions (cmp99OmegaTransitionIndex r) :=
    cmp99OmegaTransition_region_subset Seq r hxSmallRegion
  simp [cmp99OmegaTransitionRestriction, restrictZeroCLM,
    extendZeroZeroCLM, hxSmallRegion, hxLargeRegion]

/-- Away from the inner one-link collar, the literal one-step precision
defect vanishes pointwise.  The averaging mass has already cancelled, so the
proof uses only the nearest-neighbour covariant-Laplacian stencil. -/
theorem cmp99OmegaSourcePhysicalOneStepPrecisionDefect_apply_eq_zero
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 1))
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc)
    (spacing a : ℝ)
    (phi : CMP99OmegaDirichletZeroField (M := M) Seq
      (cmp99OmegaTransitionIndex r) (SUNLieCoord Nc))
    (x : ActiveGaugeRegion.Site
      (cmp99OmegaActiveGaugeRegion (M := M) Seq
        (cmp99OmegaTransitionNextIndex r)))
    (hx : x.1 ∉ cmp99OmegaTransitionInnerCollar (M := M) Seq r) :
    cmp99TypedPrecisionDefect
        (cmp99OmegaSourcePhysicalOneStepGaugePrecision Seq
          (cmp99OmegaTransitionIndex r) rho U spacing a)
        (cmp99OmegaSourcePhysicalOneStepGaugePrecision Seq
          (cmp99OmegaTransitionNextIndex r) rho U spacing a)
        (cmp99OmegaTransitionRestriction (M := M) Seq r) phi x = 0 := by
  have hneighbors : ∀ i : Fin 4,
      x.1.shift i ∈
          (cmp99OmegaActiveGaugeRegion (M := M) Seq
            (cmp99OmegaTransitionNextIndex r)).sites ∧
        x.1.shiftBack i ∈
          (cmp99OmegaActiveGaugeRegion (M := M) Seq
            (cmp99OmegaTransitionNextIndex r)).sites := by
    intro i
    constructor <;> by_contra h
    · apply hx
      rw [mem_cmp99OmegaTransitionInnerCollar_iff]
      exact ⟨x.2, ⟨i, Or.inl h⟩⟩
    · apply hx
      rw [mem_cmp99OmegaTransitionInnerCollar_iff]
      exact ⟨x.2, ⟨i, Or.inr h⟩⟩
  let extLarge := extendZeroZeroCLM
    (cmp99OmegaActiveGaugeRegion (M := M) Seq
      (cmp99OmegaTransitionIndex r)) phi
  let restricted := cmp99OmegaTransitionRestriction (M := M) Seq r phi
  let extSmall := extendZeroZeroCLM
    (cmp99OmegaActiveGaugeRegion (M := M) Seq
      (cmp99OmegaTransitionNextIndex r)) restricted
  let defectField := extLarge - extSmall
  have hzero : defectField x.1 = 0 := by
    change extLarge x.1 - extSmall x.1 = 0
    rw [cmp99OmegaTransition_extend_restrict_apply
      (M := M) Seq r phi x.1 x.2]
    exact sub_self _
  have hforward : ∀ i : Fin 4, defectField (x.1.shift i) = 0 := by
    intro i
    change extLarge (x.1.shift i) - extSmall (x.1.shift i) = 0
    rw [cmp99OmegaTransition_extend_restrict_apply
      (M := M) Seq r phi (x.1.shift i) (hneighbors i).1]
    exact sub_self _
  have hback : ∀ i : Fin 4, defectField (x.1.shiftBack i) = 0 := by
    intro i
    change extLarge (x.1.shiftBack i) - extSmall (x.1.shiftBack i) = 0
    rw [cmp99OmegaTransition_extend_restrict_apply
      (M := M) Seq r phi (x.1.shiftBack i) (hneighbors i).2]
    exact sub_self _
  have hambient := cmp99AmbientScaledCovariantLaplacian_apply_eq_zero
    rho U spacing defectField x.1 hzero hforward hback
  rw [cmp99OmegaSourcePhysicalOneStepPrecisionDefect_eq_laplacianDefect]
  change cmp99OmegaTransitionRestriction (M := M) Seq r
        (cmp99OmegaSourceCovariantLaplacian Seq
          (cmp99OmegaTransitionIndex r) rho U spacing phi) x -
      cmp99OmegaSourceCovariantLaplacian Seq
        (cmp99OmegaTransitionNextIndex r) rho U spacing restricted x = 0
  have hxLargeRegion : blockSite M (2 * Q) x.1 ∈
      Seq.regions (cmp99OmegaTransitionIndex r) :=
    cmp99OmegaTransition_region_subset Seq r
      ((mem_cmp99OmegaActiveGaugeRegion_sites_iff
        (M := M) Seq (cmp99OmegaTransitionNextIndex r) x.1).mp x.2)
  have hxLarge : x.1 ∈
      (cmp99OmegaActiveGaugeRegion (M := M) Seq
        (cmp99OmegaTransitionIndex r)).sites :=
    (mem_cmp99OmegaActiveGaugeRegion_sites_iff
      (M := M) Seq (cmp99OmegaTransitionIndex r) x.1).mpr hxLargeRegion
  let xLarge : ActiveGaugeRegion.Site
      (cmp99OmegaActiveGaugeRegion (M := M) Seq
        (cmp99OmegaTransitionIndex r)) := ⟨x.1, hxLarge⟩
  have hrestrict :
      cmp99OmegaTransitionRestriction (M := M) Seq r
          (cmp99OmegaSourceCovariantLaplacian Seq
            (cmp99OmegaTransitionIndex r) rho U spacing phi) x =
        cmp99OmegaSourceCovariantLaplacian Seq
          (cmp99OmegaTransitionIndex r) rho U spacing phi xLarge := by
    change (if h : x.1 ∈
        (cmp99OmegaActiveGaugeRegion (M := M) Seq
          (cmp99OmegaTransitionIndex r)).sites then
        cmp99OmegaSourceCovariantLaplacian Seq
          (cmp99OmegaTransitionIndex r) rho U spacing phi ⟨x.1, h⟩
      else 0) = _
    rw [dif_pos hxLarge]
  rw [hrestrict,
    cmp99OmegaSourceCovariantLaplacian_apply_eq_dirichletCompression,
    cmp99OmegaSourceCovariantLaplacian_apply_eq_dirichletCompression]
  change cmp99AmbientScaledCovariantLaplacian rho U spacing extLarge x.1 -
      cmp99AmbientScaledCovariantLaplacian rho U spacing extSmall x.1 = 0
  calc
    cmp99AmbientScaledCovariantLaplacian rho U spacing extLarge x.1 -
        cmp99AmbientScaledCovariantLaplacian rho U spacing extSmall x.1 =
      cmp99AmbientScaledCovariantLaplacian rho U spacing
        (extLarge - extSmall) x.1 := by
          rw [map_sub]
          rfl
    _ = cmp99AmbientScaledCovariantLaplacian rho U spacing
        defectField x.1 := rfl
    _ = 0 := hambient

/-- The inner collar as an active region on the same fine lattice. -/
noncomputable def cmp99OmegaTransitionInnerCollarRegion
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 1)) :
    ActiveGaugeRegion 4 (M * (2 * Q)) where
  sites := cmp99OmegaTransitionInnerCollar (M := M) Seq r

/-- Orthogonal coordinate projection of the smaller regional field onto its
inner transition collar. -/
noncomputable def cmp99OmegaTransitionInnerCollarProjection
    {g : Type*} [NormedAddCommGroup g] [InnerProductSpace ℝ g]
    [FiniteDimensional ℝ g]
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 1)) :
    CMP99OmegaDirichletZeroField (M := M) Seq
        (cmp99OmegaTransitionNextIndex r) g →L[ℝ]
      CMP99OmegaDirichletZeroField (M := M) Seq
        (cmp99OmegaTransitionNextIndex r) g :=
  (restrictZeroCLM
      (cmp99OmegaActiveGaugeRegion (M := M) Seq
        (cmp99OmegaTransitionNextIndex r))).comp
    ((extendZeroZeroCLM
      (cmp99OmegaTransitionInnerCollarRegion (M := M) Seq r)).comp
      ((restrictZeroCLM
        (cmp99OmegaTransitionInnerCollarRegion (M := M) Seq r)).comp
        (extendZeroZeroCLM
          (cmp99OmegaActiveGaugeRegion (M := M) Seq
            (cmp99OmegaTransitionNextIndex r)))))

theorem cmp99OmegaTransitionInnerCollarProjection_apply
    {g : Type*} [NormedAddCommGroup g] [InnerProductSpace ℝ g]
    [FiniteDimensional ℝ g]
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 1))
    (psi : CMP99OmegaDirichletZeroField (M := M) Seq
      (cmp99OmegaTransitionNextIndex r) g)
    (x : ActiveGaugeRegion.Site
      (cmp99OmegaActiveGaugeRegion (M := M) Seq
        (cmp99OmegaTransitionNextIndex r))) :
    cmp99OmegaTransitionInnerCollarProjection (M := M) Seq r psi x =
      if _h : x.1 ∈ cmp99OmegaTransitionInnerCollar (M := M) Seq r then
        psi x else 0 := by
  change (if h : x.1 ∈ cmp99OmegaTransitionInnerCollar (M := M) Seq r then
      (if hs : x.1 ∈
          (cmp99OmegaActiveGaugeRegion (M := M) Seq
            (cmp99OmegaTransitionNextIndex r)).sites then
        psi ⟨x.1, hs⟩ else 0) else 0) = _
  by_cases h : x.1 ∈ cmp99OmegaTransitionInnerCollar (M := M) Seq r
  · rw [dif_pos h, dif_pos x.2, dif_pos h]
  · rw [dif_neg h, dif_neg h]

/-- Exact range factorization of the physical precision defect through the
inner collar projection. -/
theorem cmp99OmegaTransitionInnerCollarProjection_comp_precisionDefect
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 1))
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc)
    (spacing a : ℝ) :
    (cmp99OmegaTransitionInnerCollarProjection
      (M := M) Seq r (g := SUNLieCoord Nc)).comp
        (cmp99TypedPrecisionDefect
          (cmp99OmegaSourcePhysicalOneStepGaugePrecision Seq
            (cmp99OmegaTransitionIndex r) rho U spacing a)
          (cmp99OmegaSourcePhysicalOneStepGaugePrecision Seq
            (cmp99OmegaTransitionNextIndex r) rho U spacing a)
          (cmp99OmegaTransitionRestriction (M := M) Seq r)) =
      cmp99TypedPrecisionDefect
        (cmp99OmegaSourcePhysicalOneStepGaugePrecision Seq
          (cmp99OmegaTransitionIndex r) rho U spacing a)
        (cmp99OmegaSourcePhysicalOneStepGaugePrecision Seq
          (cmp99OmegaTransitionNextIndex r) rho U spacing a)
        (cmp99OmegaTransitionRestriction (M := M) Seq r) := by
  apply ContinuousLinearMap.ext
  intro phi
  apply PiLp.ext
  intro x
  by_cases hx : x.1 ∈ cmp99OmegaTransitionInnerCollar (M := M) Seq r
  · rw [ContinuousLinearMap.comp_apply,
      cmp99OmegaTransitionInnerCollarProjection_apply, dif_pos hx]
  · have hzero :=
      cmp99OmegaSourcePhysicalOneStepPrecisionDefect_apply_eq_zero
        Seq r rho U spacing a phi x hx
    rw [ContinuousLinearMap.comp_apply,
      cmp99OmegaTransitionInnerCollarProjection_apply, dif_neg hx, hzero]

/-- The exact consecutive Green resolvent identity with its defect already
reduced to the physical covariant-Laplacian boundary defect. -/
theorem cmp99OmegaSourcePhysicalOneStepGreen_transition_resolvent_laplacian
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
          (cmp99OmegaSourceCovariantLaplacian Seq
            (cmp99OmegaTransitionIndex r) rho U spacing)
          (cmp99OmegaSourceCovariantLaplacian Seq
            (cmp99OmegaTransitionNextIndex r) rho U spacing)
          (cmp99OmegaTransitionRestriction (M := M) Seq r)).comp
            (cmp99OmegaSourcePhysicalOneStepGreen Seq
              (cmp99OmegaTransitionIndex r) rho U hspacing ha)) := by
  rw [← cmp99OmegaSourcePhysicalOneStepPrecisionDefect_eq_laplacianDefect
    Seq r rho U spacing a]
  exact cmp99OmegaSourcePhysicalOneStepGreen_transition_resolvent
    Seq r rho U hspacing ha

/-- Volume-independent norm bound for the complete consecutive precision
defect.  The estimate is independent of the averaging mass because that term
cancels exactly. -/
theorem norm_cmp99OmegaSourcePhysicalOneStepPrecisionDefect_le
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 1))
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc)
    {spacing : ℝ} (hspacing : 0 < spacing) (a : ℝ) :
    ‖cmp99TypedPrecisionDefect
        (cmp99OmegaSourcePhysicalOneStepGaugePrecision Seq
          (cmp99OmegaTransitionIndex r) rho U spacing a)
        (cmp99OmegaSourcePhysicalOneStepGaugePrecision Seq
          (cmp99OmegaTransitionNextIndex r) rho U spacing a)
        (cmp99OmegaTransitionRestriction (M := M) Seq r)‖ ≤
      32 / spacing ^ 2 := by
  rw [cmp99OmegaSourcePhysicalOneStepPrecisionDefect_eq_laplacianDefect]
  let R := cmp99OmegaTransitionRestriction
    (M := M) Seq r (g := SUNLieCoord Nc)
  let Llarge := cmp99OmegaSourceCovariantLaplacian Seq
    (cmp99OmegaTransitionIndex r) rho U spacing
  let Lsmall := cmp99OmegaSourceCovariantLaplacian Seq
    (cmp99OmegaTransitionNextIndex r) rho U spacing
  have hR : ‖R‖ ≤ 1 :=
    norm_cmp99OmegaTransitionRestriction_le_one (M := M) Seq r
  have hlarge : ‖Llarge‖ ≤ 16 / spacing ^ 2 :=
    norm_cmp99OmegaSourceCovariantLaplacian_le Seq
      (cmp99OmegaTransitionIndex r) rho U hspacing
  have hsmall : ‖Lsmall‖ ≤ 16 / spacing ^ 2 :=
    norm_cmp99OmegaSourceCovariantLaplacian_le Seq
      (cmp99OmegaTransitionNextIndex r) rho U hspacing
  have hbound : 0 ≤ 16 / spacing ^ 2 := by positivity
  change ‖R.comp Llarge - Lsmall.comp R‖ ≤ 32 / spacing ^ 2
  calc
    ‖R.comp Llarge - Lsmall.comp R‖ ≤
        ‖R.comp Llarge‖ + ‖Lsmall.comp R‖ := norm_sub_le _ _
    _ ≤ ‖R‖ * ‖Llarge‖ + ‖Lsmall‖ * ‖R‖ :=
      add_le_add (ContinuousLinearMap.opNorm_comp_le _ _)
        (ContinuousLinearMap.opNorm_comp_le _ _)
    _ ≤ 1 * (16 / spacing ^ 2) + (16 / spacing ^ 2) * 1 :=
      add_le_add
        (mul_le_mul hR hlarge (norm_nonneg _) zero_le_one)
        (mul_le_mul hsmall hR (norm_nonneg _) hbound)
    _ = 32 / spacing ^ 2 := by ring

/-- The consecutive physical Green mismatch is uniformly controlled by two
inverse-coercivity factors and the explicit precision-defect budget.  This is
the norm-level C3 consequence of the typed second-resolvent identity. -/
theorem norm_cmp99OmegaSourcePhysicalOneStepGreen_transition_le
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 1))
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc)
    {spacing a : ℝ} (hspacing : 0 < spacing) (ha : 0 < a) :
    ‖(cmp99OmegaSourcePhysicalOneStepGreen Seq
          (cmp99OmegaTransitionNextIndex r) rho U hspacing ha).comp
          (cmp99OmegaTransitionRestriction (M := M) Seq r) -
        (cmp99OmegaTransitionRestriction (M := M) Seq r).comp
          (cmp99OmegaSourcePhysicalOneStepGreen Seq
            (cmp99OmegaTransitionIndex r) rho U hspacing ha)‖ ≤
      (cmp99OmegaSourcePhysicalOneStepCoercivityConstant M spacing a)⁻¹ *
        ((32 / spacing ^ 2) *
          (cmp99OmegaSourcePhysicalOneStepCoercivityConstant
            M spacing a)⁻¹) := by
  let c := cmp99OmegaSourcePhysicalOneStepCoercivityConstant M spacing a
  let Glarge := cmp99OmegaSourcePhysicalOneStepGreen Seq
    (cmp99OmegaTransitionIndex r) rho U hspacing ha
  let Gsmall := cmp99OmegaSourcePhysicalOneStepGreen Seq
    (cmp99OmegaTransitionNextIndex r) rho U hspacing ha
  let D := cmp99TypedPrecisionDefect
    (cmp99OmegaSourcePhysicalOneStepGaugePrecision Seq
      (cmp99OmegaTransitionIndex r) rho U spacing a)
    (cmp99OmegaSourcePhysicalOneStepGaugePrecision Seq
      (cmp99OmegaTransitionNextIndex r) rho U spacing a)
    (cmp99OmegaTransitionRestriction (M := M) Seq r)
  have hc : 0 < c :=
    cmp99OmegaSourcePhysicalOneStepCoercivityConstant_pos ha
  have hGlarge : ‖Glarge‖ ≤ c⁻¹ :=
    norm_cmp99OmegaSourcePhysicalOneStepGreen_le Seq
      (cmp99OmegaTransitionIndex r) rho U hspacing ha
  have hGsmall : ‖Gsmall‖ ≤ c⁻¹ :=
    norm_cmp99OmegaSourcePhysicalOneStepGreen_le Seq
      (cmp99OmegaTransitionNextIndex r) rho U hspacing ha
  have hD : ‖D‖ ≤ 32 / spacing ^ 2 :=
    norm_cmp99OmegaSourcePhysicalOneStepPrecisionDefect_le
      Seq r rho U hspacing a
  have hDbound : 0 ≤ 32 / spacing ^ 2 := by positivity
  have hcinv : 0 ≤ c⁻¹ := inv_nonneg.mpr hc.le
  rw [cmp99OmegaSourcePhysicalOneStepGreen_transition_resolvent]
  change ‖Gsmall.comp (D.comp Glarge)‖ ≤ c⁻¹ * ((32 / spacing ^ 2) * c⁻¹)
  calc
    ‖Gsmall.comp (D.comp Glarge)‖ ≤ ‖Gsmall‖ * ‖D.comp Glarge‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖Gsmall‖ * (‖D‖ * ‖Glarge‖) :=
      mul_le_mul_of_nonneg_left
        (ContinuousLinearMap.opNorm_comp_le D Glarge) (norm_nonneg _)
    _ ≤ c⁻¹ * ((32 / spacing ^ 2) * c⁻¹) :=
      mul_le_mul hGsmall
        (mul_le_mul hD hGlarge (norm_nonneg _) hDbound)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hcinv

end

end YangMills.RG
