/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceGeneratedMassTransition
import YangMills.RG.BalabanCMP99SourceLaplacianTransitionSupport

/-!
# Exact collar support of generated CMP99 regional defects

The generated multiscale mass has cancelled exactly.  This file identifies
the remaining rectangular defect with the nearest-neighbour Dirichlet
Laplacian mismatch and proves that its range is contained in the literal
inner one-link collar of the smaller generated region.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

variable {d N Nc : ℕ} [NeZero d] [NeZero N] [NeZero Nc]

omit [NeZero d] in
/-- Restriction to an arbitrary active region is the counting-Hilbert
adjoint of zero extension. -/
theorem cmp99ActiveRegion_restrictZero_eq_extendZero_adjoint
    {g : Type*} [NormedAddCommGroup g] [InnerProductSpace ℝ g]
    [FiniteDimensional ℝ g]
    (Omega : ActiveGaugeRegion d N) :
    restrictZeroCLM (𝔤 := g) Omega = (extendZeroZeroCLM (𝔤 := g) Omega).adjoint := by
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro f phi
  let extPhi := extendZeroZeroCLM Omega phi
  have hinter : inner ℝ phi (restrictZeroCLM Omega f) =
      inner ℝ extPhi f := by
    rw [PiLp.inner_apply, PiLp.inner_apply]
    have hsupport :
        (∑ x ∈ Omega.sites, inner ℝ (extPhi x) (f x)) =
          ∑ x : FinBox d N, inner ℝ (extPhi x) (f x) := by
      apply Finset.sum_subset (Finset.subset_univ Omega.sites)
      intro x _hx hxOmega
      simp [extPhi, extendZeroZeroCLM, hxOmega]
    calc
      (∑ x : ActiveGaugeRegion.Site Omega,
          inner ℝ (phi x) ((restrictZeroCLM Omega f) x)) =
          ∑ x : ActiveGaugeRegion.Site Omega,
            inner ℝ (extPhi x.1) (f x.1) := by
        apply Finset.sum_congr rfl
        intro x _hx
        simp [restrictZeroCLM, extPhi, extendZeroZeroCLM, x.2]
      _ = ∑ x ∈ Omega.sites, inner ℝ (extPhi x) (f x) := by
        exact (Finset.sum_subtype Omega.sites (fun x => Iff.rfl)
          (fun x => inner ℝ (extPhi x) (f x))).symm
      _ = ∑ x : FinBox d N, inner ℝ (extPhi x) (f x) := hsupport
  calc
    inner ℝ (restrictZeroCLM Omega f) phi =
        inner ℝ phi (restrictZeroCLM Omega f) := real_inner_comm _ _
    _ = inner ℝ (extendZeroZeroCLM Omega phi) f := hinter
    _ = inner ℝ f (extendZeroZeroCLM Omega phi) := real_inner_comm _ _

/-- Ambient scaled covariant Laplacian before imposing a generated regional
Dirichlet boundary. -/
noncomputable def cmp99GeneratedAmbientScaledCovariantLaplacian
    (rho : SUNAdjointModel Nc) (U : PhysicalGaugeBackground d N Nc)
    (spacing : ℝ) :
    PhysicalGaugeZeroCochain d N Nc →L[ℝ]
      PhysicalGaugeZeroCochain d N Nc :=
  (spacing⁻¹ • covariantD0CLM rho U).adjoint.comp
    (spacing⁻¹ • covariantD0CLM rho U)

/-- Every arbitrary-region source Laplacian is the Dirichlet compression of
the same ambient nearest-neighbour operator. -/
theorem cmp99ActiveRegionSourceCovariantLaplacian_apply_eq_compression
    (Omega : ActiveGaugeRegion d N) (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d N Nc) (spacing : ℝ)
    (phi : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc)) :
    cmp99ActiveRegionSourceCovariantLaplacian Omega rho U spacing phi =
      restrictZeroCLM Omega
        (cmp99GeneratedAmbientScaledCovariantLaplacian rho U spacing
          (extendZeroZeroCLM Omega phi)) := by
  let E : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc) →L[ℝ]
      PhysicalGaugeZeroCochain d N Nc := extendZeroZeroCLM Omega
  let R : PhysicalGaugeZeroCochain d N Nc →L[ℝ]
      ActiveGaugeZeroCochain Omega (SUNLieCoord Nc) := restrictZeroCLM Omega
  let D : PhysicalGaugeZeroCochain d N Nc →L[ℝ]
      PhysicalGaugeOneCochain d N Nc := spacing⁻¹ • covariantD0CLM rho U
  have hR : R = E.adjoint :=
    cmp99ActiveRegion_restrictZero_eq_extendZero_adjoint Omega
  change (D.comp E).adjoint (D.comp E phi) = R ((D.adjoint.comp D) (E phi))
  rw [ContinuousLinearMap.adjoint_comp, hR]
  rfl

/-- Explicit nearest-neighbour stencil of the generated ambient Laplacian. -/
theorem cmp99GeneratedAmbientScaledCovariantLaplacian_apply
    (rho : SUNAdjointModel Nc) (U : PhysicalGaugeBackground d N Nc)
    (spacing : ℝ) (phi : PhysicalGaugeZeroCochain d N Nc)
    (x : FinBox d N) :
    cmp99GeneratedAmbientScaledCovariantLaplacian rho U spacing phi x =
      spacing⁻¹ •
        ∑ i : Fin d,
          ((spacing⁻¹ • covariantD0CLM rho U phi) (x, i) -
            rho.adCLM
              (U (positiveEdgeOfPhysicalBond
                ((FinBox.shiftBack x i, i) : PhysicalBond d N)))⁻¹
              ((spacing⁻¹ • covariantD0CLM rho U phi)
                (FinBox.shiftBack x i, i))) := by
  rw [cmp99GeneratedAmbientScaledCovariantLaplacian]
  rw [map_smul]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply]
  change (spacing⁻¹ • (covariantD0CLM rho U).adjoint)
      (spacing⁻¹ • covariantD0CLM rho U phi) x = _
  rw [ContinuousLinearMap.smul_apply]
  exact congrArg (fun z => spacing⁻¹ • z)
    (gaugeConstraintQCLM_apply_background rho U
      (spacing⁻¹ • covariantD0CLM rho U phi) x)

/-- Vanishing on a site and all nearest neighbours forces the ambient
generated Laplacian to vanish at that site. -/
theorem cmp99GeneratedAmbientScaledCovariantLaplacian_apply_eq_zero
    (rho : SUNAdjointModel Nc) (U : PhysicalGaugeBackground d N Nc)
    (spacing : ℝ) (phi : PhysicalGaugeZeroCochain d N Nc)
    (x : FinBox d N) (hzero : phi x = 0)
    (hforward : ∀ i : Fin d, phi (x.shift i) = 0)
    (hback : ∀ i : Fin d, phi (x.shiftBack i) = 0) :
    cmp99GeneratedAmbientScaledCovariantLaplacian rho U spacing phi x = 0 := by
  rw [cmp99GeneratedAmbientScaledCovariantLaplacian_apply]
  apply smul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro i _hi
  have hbackShift : phi ((x.shiftBack i).shift i) = 0 := by
    rw [FinBox.shift_shiftBack]
    exact hzero
  simp [covariantD0CLM_apply, hzero, hforward i, hback i, hbackShift]

/-- Inner one-link collar of an arbitrary smaller generated region. -/
noncomputable def cmp99NestedTransitionInnerCollar
    (OmegaSmall : ActiveGaugeRegion d N) : Finset (FinBox d N) :=
  OmegaSmall.sites.filter fun x =>
    ∃ i : Fin d, x.shift i ∉ OmegaSmall.sites ∨
      x.shiftBack i ∉ OmegaSmall.sites

omit [NeZero d] in
@[simp] theorem mem_cmp99NestedTransitionInnerCollar_iff
    (OmegaSmall : ActiveGaugeRegion d N) (x : FinBox d N) :
    x ∈ cmp99NestedTransitionInnerCollar OmegaSmall ↔
      x ∈ OmegaSmall.sites ∧
        ∃ i : Fin d, x.shift i ∉ OmegaSmall.sites ∨
          x.shiftBack i ∉ OmegaSmall.sites := by
  simp [cmp99NestedTransitionInnerCollar]

omit [NeZero d] in
/-- On the smaller region, extending after nested restriction agrees
pointwise with the original extension from the larger region. -/
theorem cmp99NestedTransition_extend_restrict_apply
    {g : Type*} [NormedAddCommGroup g] [InnerProductSpace ℝ g]
    [FiniteDimensional ℝ g]
    (OmegaSmall OmegaLarge : ActiveGaugeRegion d N)
    (hsub : OmegaSmall.sites ⊆ OmegaLarge.sites)
    (phi : ActiveGaugeZeroCochain OmegaLarge g) (x : FinBox d N)
    (hx : x ∈ OmegaSmall.sites) :
    extendZeroZeroCLM OmegaLarge phi x =
      extendZeroZeroCLM OmegaSmall
        (cmp99NestedActiveRegionRestriction OmegaSmall OmegaLarge phi) x := by
  have hxLarge : x ∈ OmegaLarge.sites := hsub hx
  simp [cmp99NestedActiveRegionRestriction, restrictZeroCLM,
    extendZeroZeroCLM, hx, hxLarge]

/-- Away from the smaller region's inner one-link collar, the rectangular
defect of two nested Dirichlet covariant Laplacians vanishes pointwise. -/
theorem cmp99NestedLaplacianPrecisionDefect_apply_eq_zero
    (OmegaSmall OmegaLarge : ActiveGaugeRegion d N)
    (hsub : OmegaSmall.sites ⊆ OmegaLarge.sites)
    (rho : SUNAdjointModel Nc) (U : PhysicalGaugeBackground d N Nc)
    (spacing : ℝ) (phi : ActiveGaugeZeroCochain OmegaLarge (SUNLieCoord Nc))
    (x : ActiveGaugeRegion.Site OmegaSmall)
    (hx : x.1 ∉ cmp99NestedTransitionInnerCollar OmegaSmall) :
    cmp99TypedPrecisionDefect
        (cmp99ActiveRegionSourceCovariantLaplacian OmegaLarge rho U spacing)
        (cmp99ActiveRegionSourceCovariantLaplacian OmegaSmall rho U spacing)
        (cmp99NestedActiveRegionRestriction OmegaSmall OmegaLarge) phi x = 0 := by
  have hneighbors : ∀ i : Fin d,
      x.1.shift i ∈ OmegaSmall.sites ∧ x.1.shiftBack i ∈ OmegaSmall.sites := by
    intro i
    constructor <;> by_contra h
    · apply hx
      rw [mem_cmp99NestedTransitionInnerCollar_iff]
      exact ⟨x.2, ⟨i, Or.inl h⟩⟩
    · apply hx
      rw [mem_cmp99NestedTransitionInnerCollar_iff]
      exact ⟨x.2, ⟨i, Or.inr h⟩⟩
  let extLarge := extendZeroZeroCLM OmegaLarge phi
  let restricted := cmp99NestedActiveRegionRestriction OmegaSmall OmegaLarge phi
  let extSmall := extendZeroZeroCLM OmegaSmall restricted
  let defectField := extLarge - extSmall
  have hzero : defectField x.1 = 0 := by
    change extLarge x.1 - extSmall x.1 = 0
    rw [cmp99NestedTransition_extend_restrict_apply
      OmegaSmall OmegaLarge hsub phi x.1 x.2]
    exact sub_self _
  have hforward : ∀ i : Fin d, defectField (x.1.shift i) = 0 := by
    intro i
    change extLarge (x.1.shift i) - extSmall (x.1.shift i) = 0
    rw [cmp99NestedTransition_extend_restrict_apply
      OmegaSmall OmegaLarge hsub phi (x.1.shift i) (hneighbors i).1]
    exact sub_self _
  have hback : ∀ i : Fin d, defectField (x.1.shiftBack i) = 0 := by
    intro i
    change extLarge (x.1.shiftBack i) - extSmall (x.1.shiftBack i) = 0
    rw [cmp99NestedTransition_extend_restrict_apply
      OmegaSmall OmegaLarge hsub phi (x.1.shiftBack i) (hneighbors i).2]
    exact sub_self _
  have hambient := cmp99GeneratedAmbientScaledCovariantLaplacian_apply_eq_zero
    rho U spacing defectField x.1 hzero hforward hback
  change cmp99NestedActiveRegionRestriction OmegaSmall OmegaLarge
        (cmp99ActiveRegionSourceCovariantLaplacian OmegaLarge rho U spacing phi) x -
      cmp99ActiveRegionSourceCovariantLaplacian OmegaSmall rho U spacing
        restricted x = 0
  have hxLarge : x.1 ∈ OmegaLarge.sites := hsub x.2
  let xLarge : ActiveGaugeRegion.Site OmegaLarge := ⟨x.1, hxLarge⟩
  have hrestrict :
      cmp99NestedActiveRegionRestriction OmegaSmall OmegaLarge
          (cmp99ActiveRegionSourceCovariantLaplacian OmegaLarge rho U spacing phi) x =
        cmp99ActiveRegionSourceCovariantLaplacian OmegaLarge rho U spacing phi xLarge := by
    change (if h : x.1 ∈ OmegaLarge.sites then
        cmp99ActiveRegionSourceCovariantLaplacian OmegaLarge rho U spacing phi
          ⟨x.1, h⟩ else 0) = _
    rw [dif_pos hxLarge]
  rw [hrestrict,
    cmp99ActiveRegionSourceCovariantLaplacian_apply_eq_compression,
    cmp99ActiveRegionSourceCovariantLaplacian_apply_eq_compression]
  change cmp99GeneratedAmbientScaledCovariantLaplacian rho U spacing extLarge x.1 -
      cmp99GeneratedAmbientScaledCovariantLaplacian rho U spacing extSmall x.1 = 0
  calc
    cmp99GeneratedAmbientScaledCovariantLaplacian rho U spacing extLarge x.1 -
        cmp99GeneratedAmbientScaledCovariantLaplacian rho U spacing extSmall x.1 =
      cmp99GeneratedAmbientScaledCovariantLaplacian rho U spacing
        (extLarge - extSmall) x.1 := by rw [map_sub]; rfl
    _ = cmp99GeneratedAmbientScaledCovariantLaplacian rho U spacing
        defectField x.1 := rfl
    _ = 0 := hambient

/-- The generic nested inner collar as an active region. -/
noncomputable def cmp99NestedTransitionInnerCollarRegion
    (OmegaSmall : ActiveGaugeRegion d N) : ActiveGaugeRegion d N where
  sites := cmp99NestedTransitionInnerCollar OmegaSmall

/-- Orthogonal coordinate projection of the smaller field onto its literal
inner one-link collar. -/
noncomputable def cmp99NestedTransitionInnerCollarProjection
    {g : Type*} [NormedAddCommGroup g] [InnerProductSpace ℝ g]
    [FiniteDimensional ℝ g]
    (OmegaSmall : ActiveGaugeRegion d N) :
    ActiveGaugeZeroCochain OmegaSmall g →L[ℝ]
      ActiveGaugeZeroCochain OmegaSmall g :=
  (restrictZeroCLM OmegaSmall).comp
    ((extendZeroZeroCLM (cmp99NestedTransitionInnerCollarRegion OmegaSmall)).comp
      ((restrictZeroCLM
        (cmp99NestedTransitionInnerCollarRegion OmegaSmall)).comp
        (extendZeroZeroCLM OmegaSmall)))

omit [NeZero d] in
/-- Pointwise action of the generic inner-collar projection. -/
theorem cmp99NestedTransitionInnerCollarProjection_apply
    {g : Type*} [NormedAddCommGroup g] [InnerProductSpace ℝ g]
    [FiniteDimensional ℝ g]
    (OmegaSmall : ActiveGaugeRegion d N)
    (psi : ActiveGaugeZeroCochain OmegaSmall g)
    (x : ActiveGaugeRegion.Site OmegaSmall) :
    cmp99NestedTransitionInnerCollarProjection OmegaSmall psi x =
      if _h : x.1 ∈ cmp99NestedTransitionInnerCollar OmegaSmall then psi x else 0 := by
  change (if h : x.1 ∈ cmp99NestedTransitionInnerCollar OmegaSmall then
      (if hs : x.1 ∈ OmegaSmall.sites then psi ⟨x.1, hs⟩ else 0) else 0) = _
  by_cases h : x.1 ∈ cmp99NestedTransitionInnerCollar OmegaSmall
  · rw [dif_pos h, dif_pos x.2, dif_pos h]
  · rw [dif_neg h, dif_neg h]

/-- Exact range factorization of every nested Laplacian defect through the
smaller region's inner collar. -/
theorem cmp99NestedTransitionInnerCollarProjection_comp_laplacianDefect
    (OmegaSmall OmegaLarge : ActiveGaugeRegion d N)
    (hsub : OmegaSmall.sites ⊆ OmegaLarge.sites)
    (rho : SUNAdjointModel Nc) (U : PhysicalGaugeBackground d N Nc)
    (spacing : ℝ) :
    (cmp99NestedTransitionInnerCollarProjection
      (g := SUNLieCoord Nc) OmegaSmall).comp
        (cmp99TypedPrecisionDefect
          (cmp99ActiveRegionSourceCovariantLaplacian OmegaLarge rho U spacing)
          (cmp99ActiveRegionSourceCovariantLaplacian OmegaSmall rho U spacing)
          (cmp99NestedActiveRegionRestriction OmegaSmall OmegaLarge)) =
      cmp99TypedPrecisionDefect
        (cmp99ActiveRegionSourceCovariantLaplacian OmegaLarge rho U spacing)
        (cmp99ActiveRegionSourceCovariantLaplacian OmegaSmall rho U spacing)
        (cmp99NestedActiveRegionRestriction OmegaSmall OmegaLarge) := by
  apply ContinuousLinearMap.ext
  intro phi
  apply PiLp.ext
  intro x
  by_cases hx : x.1 ∈ cmp99NestedTransitionInnerCollar OmegaSmall
  · rw [ContinuousLinearMap.comp_apply,
      cmp99NestedTransitionInnerCollarProjection_apply, dif_pos hx]
  · have hzero := cmp99NestedLaplacianPrecisionDefect_apply_eq_zero
      OmegaSmall OmegaLarge hsub rho U spacing phi x hx
    rw [ContinuousLinearMap.comp_apply,
      cmp99NestedTransitionInnerCollarProjection_apply, dif_neg hx, hzero]

namespace CMP99SourceDependentOmegaGeometry

variable {Q M j : ℕ} [NeZero Q] [NeZero M]
variable {cell : FinBox 4 Q}
variable {ScaleSite : Fin (j + 2) → Type*}
variable [∀ r, DecidableEq (ScaleSite r)]
variable {Scaled : CMP99SourceScaledStratification
  (FinBox 4 (2 * Q)) (j + 2) ScaleSite}
variable {dist : FinBox 4 (2 * Q) → FinBox 4 (2 * Q) → ℕ}
variable {gap : Fin (j + 1) → ℕ}

/-- Literal inner one-link collar of the smaller generated physical region. -/
noncomputable def generatedTransitionInnerCollar
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (r : Fin (j + 1)) (depth : ℕ) :
    Finset (FinBox 4 (cmp99RegionalLatticeSize M (2 * Q) depth)) :=
  cmp99NestedTransitionInnerCollar
    (D.operatorRegion (M := M) hpi5 (cmp99OmegaTransitionNextIndex r) depth)

/-- Projection onto the generated transition's literal inner collar. -/
noncomputable def generatedTransitionInnerCollarProjection
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (r : Fin (j + 1)) (depth : ℕ) :
    ActiveGaugeZeroCochain
        (D.operatorRegion (M := M) hpi5
          (cmp99OmegaTransitionNextIndex r) depth) (SUNLieCoord Nc) →L[ℝ]
      ActiveGaugeZeroCochain
        (D.operatorRegion (M := M) hpi5
          (cmp99OmegaTransitionNextIndex r) depth) (SUNLieCoord Nc) :=
  cmp99NestedTransitionInnerCollarProjection
    (D.operatorRegion (M := M) hpi5 (cmp99OmegaTransitionNextIndex r) depth)

/-- C4 pointwise support: the full generated physical precision defect
vanishes away from the smaller region's literal one-link collar. -/
theorem generatedPhysicalPrecisionDefect_apply_eq_zero
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (r : Fin (j + 1)) (hM : 2 ≤ M) (depth : ℕ)
    (spacing epsilon : ℝ)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (phi : ActiveGaugeZeroCochain
      (D.operatorRegion (M := M) hpi5
        (cmp99OmegaTransitionIndex r) (depth + 1)) (SUNLieCoord Nc))
    (x : ActiveGaugeRegion.Site
      (D.operatorRegion (M := M) hpi5
        (cmp99OmegaTransitionNextIndex r) (depth + 1)))
    (hx : x.1 ∉ D.generatedTransitionInnerCollar
      (M := M) hpi5 r (depth + 1)) :
    cmp99TypedPrecisionDefect
        (cmp99SourceGeneratedPhysicalPrecision (by norm_num) hM
          (D.operatorCoarseRegion hpi5 (cmp99OmegaTransitionIndex r))
          depth spacing epsilon background budget fineSmall)
        (cmp99SourceGeneratedPhysicalPrecision (by norm_num) hM
          (D.operatorCoarseRegion hpi5 (cmp99OmegaTransitionNextIndex r))
          depth spacing epsilon background budget fineSmall)
        (D.generatedTransitionRestriction (M := M) (Nc := Nc) hpi5 r
          (depth + 1)) phi x = 0 := by
  rw [D.generatedPhysicalPrecisionDefect_eq_laplacianDefect hpi5 r hM depth
    spacing epsilon background budget fineSmall]
  exact cmp99NestedLaplacianPrecisionDefect_apply_eq_zero
    (D.operatorRegion (M := M) hpi5
      (cmp99OmegaTransitionNextIndex r) (depth + 1))
    (D.operatorRegion (M := M) hpi5
      (cmp99OmegaTransitionIndex r) (depth + 1))
    (D.operatorRegion_transition_subset hpi5 r (depth + 1))
    (matrixSUNAdjointModel Nc) background spacing phi x hx

/-- C4 terminal range factorization of the full generated precision defect
through the literal inner collar projection. -/
theorem generatedTransitionInnerCollarProjection_comp_precisionDefect
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (r : Fin (j + 1)) (hM : 2 ≤ M) (depth : ℕ)
    (spacing epsilon : ℝ)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) :
    (D.generatedTransitionInnerCollarProjection
      (M := M) (Nc := Nc) hpi5 r (depth + 1)).comp
        (cmp99TypedPrecisionDefect
          (cmp99SourceGeneratedPhysicalPrecision (by norm_num) hM
            (D.operatorCoarseRegion hpi5 (cmp99OmegaTransitionIndex r))
            depth spacing epsilon background budget fineSmall)
          (cmp99SourceGeneratedPhysicalPrecision (by norm_num) hM
            (D.operatorCoarseRegion hpi5 (cmp99OmegaTransitionNextIndex r))
            depth spacing epsilon background budget fineSmall)
          (D.generatedTransitionRestriction (M := M) (Nc := Nc) hpi5 r
            (depth + 1))) =
      cmp99TypedPrecisionDefect
        (cmp99SourceGeneratedPhysicalPrecision (by norm_num) hM
          (D.operatorCoarseRegion hpi5 (cmp99OmegaTransitionIndex r))
          depth spacing epsilon background budget fineSmall)
        (cmp99SourceGeneratedPhysicalPrecision (by norm_num) hM
          (D.operatorCoarseRegion hpi5 (cmp99OmegaTransitionNextIndex r))
          depth spacing epsilon background budget fineSmall)
        (D.generatedTransitionRestriction (M := M) (Nc := Nc) hpi5 r
          (depth + 1)) := by
  let P := D.generatedTransitionInnerCollarProjection
    (M := M) (Nc := Nc) hpi5 r (depth + 1)
  let Klarge := cmp99SourceGeneratedPhysicalPrecision (by norm_num) hM
    (D.operatorCoarseRegion hpi5 (cmp99OmegaTransitionIndex r))
    depth spacing epsilon background budget fineSmall
  let Ksmall := cmp99SourceGeneratedPhysicalPrecision (by norm_num) hM
    (D.operatorCoarseRegion hpi5 (cmp99OmegaTransitionNextIndex r))
    depth spacing epsilon background budget fineSmall
  let R := D.generatedTransitionRestriction (M := M) (Nc := Nc) hpi5 r
    (depth + 1)
  let Llarge := cmp99ActiveRegionSourceCovariantLaplacian
    (D.operatorRegion (M := M) hpi5
      (cmp99OmegaTransitionIndex r) (depth + 1))
    (matrixSUNAdjointModel Nc) background spacing
  let Lsmall := cmp99ActiveRegionSourceCovariantLaplacian
    (D.operatorRegion (M := M) hpi5
      (cmp99OmegaTransitionNextIndex r) (depth + 1))
    (matrixSUNAdjointModel Nc) background spacing
  have hdef : cmp99TypedPrecisionDefect Klarge Ksmall R =
      cmp99TypedPrecisionDefect Llarge Lsmall R := by
    exact D.generatedPhysicalPrecisionDefect_eq_laplacianDefect hpi5 r hM depth
      spacing epsilon background budget fineSmall
  have hcollar : P.comp (cmp99TypedPrecisionDefect Llarge Lsmall R) =
      cmp99TypedPrecisionDefect Llarge Lsmall R := by
    simpa [P, Llarge, Lsmall, R, generatedTransitionInnerCollarProjection,
      generatedTransitionRestriction, cmp99NestedActiveRegionRestriction,
      operatorRegion] using
      (cmp99NestedTransitionInnerCollarProjection_comp_laplacianDefect
        (D.operatorRegion (M := M) hpi5
          (cmp99OmegaTransitionNextIndex r) (depth + 1))
        (D.operatorRegion (M := M) hpi5
          (cmp99OmegaTransitionIndex r) (depth + 1))
        (D.operatorRegion_transition_subset hpi5 r (depth + 1))
        (matrixSUNAdjointModel Nc) background spacing)
  change P.comp (cmp99TypedPrecisionDefect Klarge Ksmall R) =
    cmp99TypedPrecisionDefect Klarge Ksmall R
  have hleft : P.comp (cmp99TypedPrecisionDefect Klarge Ksmall R) =
      P.comp (cmp99TypedPrecisionDefect Llarge Lsmall R) :=
    congrArg (fun K => P.comp K) hdef
  exact hleft.trans (hcollar.trans hdef.symm)

end CMP99SourceDependentOmegaGeometry

end

end YangMills.RG
