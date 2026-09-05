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

/-- Exact Hilbert pairing between consecutive restriction and zero
extension. -/
theorem inner_cmp99OmegaTransitionRestriction_eq_extension
    {g : Type*} [NormedAddCommGroup g] [InnerProductSpace ℝ g]
    [FiniteDimensional ℝ g]
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 1))
    (psi : CMP99OmegaDirichletZeroField (M := M) Seq
      (cmp99OmegaTransitionIndex r) g)
    (phi : CMP99OmegaDirichletZeroField (M := M) Seq
      (cmp99OmegaTransitionNextIndex r) g) :
    inner ℝ (cmp99OmegaTransitionRestriction (M := M) Seq r psi) phi =
      inner ℝ psi (cmp99OmegaTransitionExtension (M := M) Seq r phi) := by
  let OmegaLarge := cmp99OmegaActiveGaugeRegion (M := M) Seq
    (cmp99OmegaTransitionIndex r)
  let OmegaSmall := cmp99OmegaActiveGaugeRegion (M := M) Seq
    (cmp99OmegaTransitionNextIndex r)
  let extPsi := extendZeroZeroCLM OmegaLarge psi
  let extPhi := extendZeroZeroCLM OmegaSmall phi
  have hsmall := inner_cmp99Omega_restrictZero_eq_extendZero
    (M := M) Seq (cmp99OmegaTransitionNextIndex r) phi extPsi
  have hlarge := inner_cmp99Omega_restrictZero_eq_extendZero
    (M := M) Seq (cmp99OmegaTransitionIndex r) psi extPhi
  change inner ℝ (restrictZeroCLM OmegaSmall extPsi) phi =
    inner ℝ psi (restrictZeroCLM OmegaLarge extPhi)
  calc
    inner ℝ (restrictZeroCLM OmegaSmall extPsi) phi =
        inner ℝ phi (restrictZeroCLM OmegaSmall extPsi) := real_inner_comm _ _
    _ = inner ℝ extPhi extPsi := hsmall
    _ = inner ℝ extPsi extPhi := real_inner_comm _ _
    _ = inner ℝ psi (restrictZeroCLM OmegaLarge extPhi) := hlarge.symm

/-- Consecutive zero extension is exactly the counting-Hilbert adjoint of
restriction. -/
theorem cmp99OmegaTransitionExtension_eq_adjoint
    {g : Type*} [NormedAddCommGroup g] [InnerProductSpace ℝ g]
    [FiniteDimensional ℝ g]
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 1)) :
    cmp99OmegaTransitionExtension (M := M) Seq r (g := g) =
      (cmp99OmegaTransitionRestriction (M := M) Seq r).adjoint := by
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro phi psi
  calc
    inner ℝ (cmp99OmegaTransitionExtension (M := M) Seq r phi) psi =
        inner ℝ psi
          (cmp99OmegaTransitionExtension (M := M) Seq r phi) :=
      real_inner_comm _ _
    _ = inner ℝ
          (cmp99OmegaTransitionRestriction (M := M) Seq r psi) phi :=
      (inner_cmp99OmegaTransitionRestriction_eq_extension
        (M := M) Seq r psi phi).symm
    _ = inner ℝ phi
          (cmp99OmegaTransitionRestriction (M := M) Seq r psi) :=
      real_inner_comm _ _

/-- A norm-preserving continuous linear map is contractive. -/
theorem opNorm_le_one_of_norm_map_eq
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (T : E →L[ℝ] F) (hT : ∀ x, ‖T x‖ = ‖x‖) : ‖T‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound T zero_le_one
  intro x
  rw [hT]
  simp

/-- Consecutive regional restriction is contractive in the counting Hilbert
norm. -/
theorem norm_cmp99OmegaTransitionRestriction_le_one
    {g : Type*} [NormedAddCommGroup g] [InnerProductSpace ℝ g]
    [FiniteDimensional ℝ g]
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 1)) :
    ‖cmp99OmegaTransitionRestriction (M := M) Seq r (g := g)‖ ≤ 1 := by
  have hE : ‖cmp99OmegaTransitionExtension (M := M) Seq r (g := g)‖ ≤ 1 := by
    exact opNorm_le_one_of_norm_map_eq _
      (norm_cmp99OmegaTransitionExtension (M := M) Seq r)
  rw [cmp99OmegaTransitionExtension_eq_adjoint] at hE
  have hnorm := ContinuousLinearMap.adjoint.norm_map
    (cmp99OmegaTransitionRestriction (M := M) Seq r (g := g))
  rw [hnorm] at hE
  exact hE

/-- Restriction between the regional coarse targets associated with two
consecutive source regions. -/
noncomputable def cmp99OmegaCoarseTransitionRestriction
    {g : Type*} [NormedAddCommGroup g] [InnerProductSpace ℝ g]
    [FiniteDimensional ℝ g]
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 1)) :
    CMP99OmegaRegionalCoarseField (M := M) Seq
        (cmp99OmegaTransitionIndex r) g →L[ℝ]
      CMP99OmegaRegionalCoarseField (M := M) Seq
        (cmp99OmegaTransitionNextIndex r) g :=
  (restrictZeroCLM
      (cmp99ActiveCoarseRegion (M := M) (N' := 2 * Q)
        (cmp99OmegaActiveGaugeRegion (M := M) Seq
          (cmp99OmegaTransitionNextIndex r)))).comp
    (extendZeroZeroCLM
      (cmp99ActiveCoarseRegion (M := M) (N' := 2 * Q)
        (cmp99OmegaActiveGaugeRegion (M := M) Seq
          (cmp99OmegaTransitionIndex r))))

/-- The literal one-step regional average commutes with restriction to a
consecutive source region.  This is an exact identity of the two dependent
regional field spaces, not a norm estimate. -/
theorem cmp99SourceTransportedBlockAverage_transition
    {g : Type*} [NormedAddCommGroup g] [InnerProductSpace ℝ g]
    [FiniteDimensional ℝ g]
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 1))
    (transport : FinBox 4 (2 * Q) →
      FinBox 4 (M * (2 * Q)) → (g ≃ₗᵢ[ℝ] g)) :
    (cmp99SourceTransportedBlockAverageCLM
      (cmp99OmegaActiveGaugeRegion (M := M) Seq
        (cmp99OmegaTransitionNextIndex r)) transport).comp
        (cmp99OmegaTransitionRestriction (M := M) Seq r) =
      (cmp99OmegaCoarseTransitionRestriction (M := M) Seq r).comp
        (cmp99SourceTransportedBlockAverageCLM
          (cmp99OmegaActiveGaugeRegion (M := M) Seq
            (cmp99OmegaTransitionIndex r)) transport) := by
  apply ContinuousLinearMap.ext
  intro phi
  ext y
  have hySmall : y.1 ∈
      (cmp99ActiveCoarseRegion (M := M) (N' := 2 * Q)
        (cmp99OmegaActiveGaugeRegion (M := M) Seq
          (cmp99OmegaTransitionNextIndex r))).sites := y.2
  have hySmallRegion : y.1 ∈
      Seq.regions (cmp99OmegaTransitionNextIndex r) := by
    rw [← cmp99OmegaActiveCoarseRegion_sites_eq
      (M := M) Seq (cmp99OmegaTransitionNextIndex r)]
    exact hySmall
  have hyLargeRegion : y.1 ∈
      Seq.regions (cmp99OmegaTransitionIndex r) :=
    cmp99OmegaTransition_region_subset Seq r hySmallRegion
  have hyLarge : y.1 ∈
      (cmp99ActiveCoarseRegion (M := M) (N' := 2 * Q)
        (cmp99OmegaActiveGaugeRegion (M := M) Seq
          (cmp99OmegaTransitionIndex r))).sites := by
    rw [cmp99OmegaActiveCoarseRegion_sites_eq
      (M := M) Seq (cmp99OmegaTransitionIndex r)]
    exact hyLargeRegion
  let yLarge : ActiveGaugeRegion.Site
      (cmp99ActiveCoarseRegion (M := M) (N' := 2 * Q)
        (cmp99OmegaActiveGaugeRegion (M := M) Seq
          (cmp99OmegaTransitionIndex r))) := ⟨y.1, hyLarge⟩
  have hcoarse :
      cmp99OmegaCoarseTransitionRestriction (M := M) Seq r
          (cmp99SourceTransportedBlockAverageCLM
            (cmp99OmegaActiveGaugeRegion (M := M) Seq
              (cmp99OmegaTransitionIndex r)) transport phi) y =
        cmp99SourceTransportedBlockAverageCLM
          (cmp99OmegaActiveGaugeRegion (M := M) Seq
            (cmp99OmegaTransitionIndex r)) transport phi yLarge := by
    change (if h : y.1 ∈
        (cmp99ActiveCoarseRegion (M := M) (N' := 2 * Q)
          (cmp99OmegaActiveGaugeRegion (M := M) Seq
            (cmp99OmegaTransitionIndex r))).sites then
          cmp99SourceTransportedBlockAverageCLM
            (cmp99OmegaActiveGaugeRegion (M := M) Seq
              (cmp99OmegaTransitionIndex r)) transport phi ⟨y.1, h⟩
        else 0) = _
    rw [dif_pos hyLarge]
  simp only [ContinuousLinearMap.comp_apply]
  rw [hcoarse]
  simp only [cmp99SourceTransportedBlockAverageCLM,
    cmp99TransportedBlockAverageCLM_apply]
  apply congrArg (fun z : g => cmp99SourceBlockAverageWeight M 4 • z)
  apply Finset.sum_congr rfl
  intro x _hx
  apply congrArg (transport y.1 x.1)
  have hxLarge : x.1 ∈
      (cmp99OmegaActiveGaugeRegion (M := M) Seq
        (cmp99OmegaTransitionIndex r)).sites := by
    rw [mem_cmp99OmegaActiveGaugeRegion_sites_iff]
    have hxy : blockSite M (2 * Q) x.1 = y.1 :=
      (mem_blockOf M (2 * Q) y.1 x.1).mp x.2
    rw [hxy]
    exact hyLargeRegion
  change (if h : x.1 ∈
      (cmp99OmegaActiveGaugeRegion (M := M) Seq
        (cmp99OmegaTransitionIndex r)).sites then phi ⟨x.1, h⟩ else 0) =
    phi (cmp99ActiveFineSiteOfBlock
      (cmp99OmegaActiveGaugeRegion (M := M) Seq
        (cmp99OmegaTransitionIndex r)) yLarge x)
  rw [dif_pos hxLarge]
  rfl

/-- The counting-Hilbert adjoints of the literal block averages commute with
the same consecutive restrictions.  This is the local statement needed to
remove the `Q^* Q` mass from the rectangular precision defect. -/
theorem cmp99SourceTransportedBlockAverage_adjoint_transition
    {g : Type*} [NormedAddCommGroup g] [InnerProductSpace ℝ g]
    [FiniteDimensional ℝ g]
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 1))
    (transport : FinBox 4 (2 * Q) →
      FinBox 4 (M * (2 * Q)) → (g ≃ₗᵢ[ℝ] g)) :
    (cmp99OmegaTransitionRestriction (M := M) Seq r).comp
        (cmp99SourceTransportedBlockAverageCLM
          (cmp99OmegaActiveGaugeRegion (M := M) Seq
            (cmp99OmegaTransitionIndex r)) transport).adjoint =
      (cmp99SourceTransportedBlockAverageCLM
        (cmp99OmegaActiveGaugeRegion (M := M) Seq
          (cmp99OmegaTransitionNextIndex r)) transport).adjoint.comp
        (cmp99OmegaCoarseTransitionRestriction (M := M) Seq r) := by
  rw [cmp99SourceTransportedBlockAverageCLM,
    cmp99SourceTransportedBlockAverageCLM,
    ← cmp99TransportedBlockSynthesisCLM_eq_adjoint
      (cmp99OmegaActiveGaugeRegion (M := M) Seq
        (cmp99OmegaTransitionIndex r))
      (cmp99OmegaActiveGaugeRegion_blockSaturated
        (M := M) Seq (cmp99OmegaTransitionIndex r))
      (cmp99SourceBlockAverageWeight M 4) transport,
    ← cmp99TransportedBlockSynthesisCLM_eq_adjoint
      (cmp99OmegaActiveGaugeRegion (M := M) Seq
        (cmp99OmegaTransitionNextIndex r))
      (cmp99OmegaActiveGaugeRegion_blockSaturated
        (M := M) Seq (cmp99OmegaTransitionNextIndex r))
      (cmp99SourceBlockAverageWeight M 4) transport]
  apply ContinuousLinearMap.ext
  intro eta
  ext x
  have hxSmallRegion : blockSite M (2 * Q) x.1 ∈
      Seq.regions (cmp99OmegaTransitionNextIndex r) :=
    (mem_cmp99OmegaActiveGaugeRegion_sites_iff
      (M := M) Seq (cmp99OmegaTransitionNextIndex r) x.1).mp x.2
  have hxLargeRegion : blockSite M (2 * Q) x.1 ∈
      Seq.regions (cmp99OmegaTransitionIndex r) :=
    cmp99OmegaTransition_region_subset Seq r hxSmallRegion
  have hxLarge : x.1 ∈
      (cmp99OmegaActiveGaugeRegion (M := M) Seq
        (cmp99OmegaTransitionIndex r)).sites :=
    (mem_cmp99OmegaActiveGaugeRegion_sites_iff
      (M := M) Seq (cmp99OmegaTransitionIndex r) x.1).mpr hxLargeRegion
  have hySmall : blockSite M (2 * Q) x.1 ∈
      (cmp99ActiveCoarseRegion (M := M) (N' := 2 * Q)
        (cmp99OmegaActiveGaugeRegion (M := M) Seq
          (cmp99OmegaTransitionNextIndex r))).sites := by
    rw [cmp99OmegaActiveCoarseRegion_sites_eq]
    exact hxSmallRegion
  have hyLarge : blockSite M (2 * Q) x.1 ∈
      (cmp99ActiveCoarseRegion (M := M) (N' := 2 * Q)
        (cmp99OmegaActiveGaugeRegion (M := M) Seq
          (cmp99OmegaTransitionIndex r))).sites := by
    rw [cmp99OmegaActiveCoarseRegion_sites_eq]
    exact hxLargeRegion
  let xLarge : ActiveGaugeRegion.Site
      (cmp99OmegaActiveGaugeRegion (M := M) Seq
        (cmp99OmegaTransitionIndex r)) := ⟨x.1, hxLarge⟩
  have hfine :
      cmp99OmegaTransitionRestriction (M := M) Seq r
          (cmp99TransportedBlockSynthesisCLM
            (cmp99OmegaActiveGaugeRegion (M := M) Seq
              (cmp99OmegaTransitionIndex r))
            (cmp99OmegaActiveGaugeRegion_blockSaturated
              (M := M) Seq (cmp99OmegaTransitionIndex r))
            (cmp99SourceBlockAverageWeight M 4) transport eta) x =
        cmp99TransportedBlockSynthesisCLM
          (cmp99OmegaActiveGaugeRegion (M := M) Seq
            (cmp99OmegaTransitionIndex r))
          (cmp99OmegaActiveGaugeRegion_blockSaturated
            (M := M) Seq (cmp99OmegaTransitionIndex r))
          (cmp99SourceBlockAverageWeight M 4) transport eta xLarge := by
    change (if h : x.1 ∈
        (cmp99OmegaActiveGaugeRegion (M := M) Seq
          (cmp99OmegaTransitionIndex r)).sites then
        cmp99TransportedBlockSynthesisCLM
          (cmp99OmegaActiveGaugeRegion (M := M) Seq
            (cmp99OmegaTransitionIndex r))
          (cmp99OmegaActiveGaugeRegion_blockSaturated
            (M := M) Seq (cmp99OmegaTransitionIndex r))
          (cmp99SourceBlockAverageWeight M 4) transport eta ⟨x.1, h⟩
      else 0) = _
    rw [dif_pos hxLarge]
  let ySmall : ActiveGaugeRegion.Site
      (cmp99ActiveCoarseRegion (M := M) (N' := 2 * Q)
        (cmp99OmegaActiveGaugeRegion (M := M) Seq
          (cmp99OmegaTransitionNextIndex r))) :=
    ⟨blockSite M (2 * Q) x.1, hySmall⟩
  let yLarge : ActiveGaugeRegion.Site
      (cmp99ActiveCoarseRegion (M := M) (N' := 2 * Q)
        (cmp99OmegaActiveGaugeRegion (M := M) Seq
          (cmp99OmegaTransitionIndex r))) :=
    ⟨blockSite M (2 * Q) x.1, hyLarge⟩
  have hcoarse :
      cmp99OmegaCoarseTransitionRestriction (M := M) Seq r eta ySmall =
        eta yLarge := by
    change (if h : blockSite M (2 * Q) x.1 ∈
        (cmp99ActiveCoarseRegion (M := M) (N' := 2 * Q)
          (cmp99OmegaActiveGaugeRegion (M := M) Seq
            (cmp99OmegaTransitionIndex r))).sites then
          eta ⟨blockSite M (2 * Q) x.1, h⟩ else 0) = _
    rw [dif_pos hyLarge]
  simp only [ContinuousLinearMap.comp_apply]
  rw [hfine]
  rw [cmp99TransportedBlockSynthesisCLM_apply,
    cmp99TransportedBlockSynthesisCLM_apply]
  change cmp99SourceBlockAverageWeight M 4 •
      (transport (blockSite M (2 * Q) xLarge.1) xLarge.1).symm
        (eta yLarge) =
      cmp99SourceBlockAverageWeight M 4 •
        (transport (blockSite M (2 * Q) x.1) x.1).symm
          (cmp99OmegaCoarseTransitionRestriction (M := M) Seq r eta ySmall)
  rw [hcoarse]

/-- Consequently the complete counting-Hilbert mass `Q^* Q` commutes with
consecutive regional restriction. -/
theorem cmp99SourceTransportedBlockMass_transition
    {g : Type*} [NormedAddCommGroup g] [InnerProductSpace ℝ g]
    [FiniteDimensional ℝ g]
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 1))
    (transport : FinBox 4 (2 * Q) →
      FinBox 4 (M * (2 * Q)) → (g ≃ₗᵢ[ℝ] g)) :
    (cmp99OmegaTransitionRestriction (M := M) Seq r).comp
        ((cmp99SourceTransportedBlockAverageCLM
          (cmp99OmegaActiveGaugeRegion (M := M) Seq
            (cmp99OmegaTransitionIndex r)) transport).adjoint.comp
          (cmp99SourceTransportedBlockAverageCLM
            (cmp99OmegaActiveGaugeRegion (M := M) Seq
              (cmp99OmegaTransitionIndex r)) transport)) =
      ((cmp99SourceTransportedBlockAverageCLM
        (cmp99OmegaActiveGaugeRegion (M := M) Seq
          (cmp99OmegaTransitionNextIndex r)) transport).adjoint.comp
        (cmp99SourceTransportedBlockAverageCLM
          (cmp99OmegaActiveGaugeRegion (M := M) Seq
            (cmp99OmegaTransitionNextIndex r)) transport)).comp
          (cmp99OmegaTransitionRestriction (M := M) Seq r) := by
  let Qlarge := cmp99SourceTransportedBlockAverageCLM
    (cmp99OmegaActiveGaugeRegion (M := M) Seq
      (cmp99OmegaTransitionIndex r)) transport
  let Qsmall := cmp99SourceTransportedBlockAverageCLM
    (cmp99OmegaActiveGaugeRegion (M := M) Seq
      (cmp99OmegaTransitionNextIndex r)) transport
  let Rfine := cmp99OmegaTransitionRestriction (M := M) Seq r (g := g)
  let Rcoarse := cmp99OmegaCoarseTransitionRestriction
    (M := M) Seq r (g := g)
  have hQ : Qsmall.comp Rfine = Rcoarse.comp Qlarge :=
    cmp99SourceTransportedBlockAverage_transition Seq r transport
  have hQstar : Rfine.comp Qlarge.adjoint =
      Qsmall.adjoint.comp Rcoarse :=
    cmp99SourceTransportedBlockAverage_adjoint_transition Seq r transport
  change Rfine.comp (Qlarge.adjoint.comp Qlarge) =
    (Qsmall.adjoint.comp Qsmall).comp Rfine
  calc
    Rfine.comp (Qlarge.adjoint.comp Qlarge) =
        (Rfine.comp Qlarge.adjoint).comp Qlarge := by
      rw [ContinuousLinearMap.comp_assoc]
    _ = (Qsmall.adjoint.comp Rcoarse).comp Qlarge := by rw [hQstar]
    _ = Qsmall.adjoint.comp (Rcoarse.comp Qlarge) := by
      rw [ContinuousLinearMap.comp_assoc]
    _ = Qsmall.adjoint.comp (Qsmall.comp Rfine) := by rw [hQ]
    _ = (Qsmall.adjoint.comp Qsmall).comp Rfine := by
      rw [ContinuousLinearMap.comp_assoc]

/-- Physical one-step specialization of exact regional averaging. -/
theorem cmp99OmegaSourcePhysicalOneStepQ_transition
    {Nc : ℕ} [NeZero Nc]
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 1))
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc) :
    (cmp99OmegaSourcePhysicalOneStepQ Seq
      (cmp99OmegaTransitionNextIndex r) rho U).comp
        (cmp99OmegaTransitionRestriction (M := M) Seq r) =
      (cmp99OmegaCoarseTransitionRestriction (M := M) Seq r).comp
        (cmp99OmegaSourcePhysicalOneStepQ Seq
          (cmp99OmegaTransitionIndex r) rho U) := by
  exact cmp99SourceTransportedBlockAverage_transition Seq r
    (cmp99SourceWeightedPhysicalTransport rho U)

/-- Physical one-step specialization of the exact regional mass identity. -/
theorem cmp99OmegaSourcePhysicalOneStepMass_transition
    {Nc : ℕ} [NeZero Nc]
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 1))
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc) :
    (cmp99OmegaTransitionRestriction (M := M) Seq r).comp
        ((cmp99OmegaSourcePhysicalOneStepQ Seq
          (cmp99OmegaTransitionIndex r) rho U).adjoint.comp
          (cmp99OmegaSourcePhysicalOneStepQ Seq
            (cmp99OmegaTransitionIndex r) rho U)) =
      ((cmp99OmegaSourcePhysicalOneStepQ Seq
        (cmp99OmegaTransitionNextIndex r) rho U).adjoint.comp
        (cmp99OmegaSourcePhysicalOneStepQ Seq
          (cmp99OmegaTransitionNextIndex r) rho U)).comp
          (cmp99OmegaTransitionRestriction (M := M) Seq r) := by
  exact cmp99SourceTransportedBlockMass_transition Seq r
    (cmp99SourceWeightedPhysicalTransport rho U)

/-- Rectangular precision defect for two operators acting on different
Dirichlet spaces. -/
noncomputable def cmp99TypedPrecisionDefect
    {Eₗ Eₛ : Type*}
    [NormedAddCommGroup Eₗ] [InnerProductSpace ℝ Eₗ]
    [NormedAddCommGroup Eₛ] [InnerProductSpace ℝ Eₛ]
    (Kₗ : Eₗ →L[ℝ] Eₗ) (Kₛ : Eₛ →L[ℝ] Eₛ)
    (R : Eₗ →L[ℝ] Eₛ) : Eₗ →L[ℝ] Eₛ :=
  R.comp Kₗ - Kₛ.comp R

/-- If a regional mass commutes with restriction, it cancels identically
from the rectangular precision defect. -/
theorem cmp99TypedPrecisionDefect_add_mass_eq
    {Eₗ Eₛ : Type*}
    [NormedAddCommGroup Eₗ] [InnerProductSpace ℝ Eₗ]
    [NormedAddCommGroup Eₛ] [InnerProductSpace ℝ Eₛ]
    (Kₗ Mₗ : Eₗ →L[ℝ] Eₗ) (Kₛ Mₛ : Eₛ →L[ℝ] Eₛ)
    (R : Eₗ →L[ℝ] Eₛ) (a : ℝ)
    (hmass : R.comp Mₗ = Mₛ.comp R) :
    cmp99TypedPrecisionDefect (Kₗ + a • Mₗ) (Kₛ + a • Mₛ) R =
      cmp99TypedPrecisionDefect Kₗ Kₛ R := by
  apply ContinuousLinearMap.ext
  intro x
  have hx := congrArg (fun T : Eₗ →L[ℝ] Eₛ => T x) hmass
  simp only [ContinuousLinearMap.comp_apply] at hx
  simp only [cmp99TypedPrecisionDefect, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, map_add, map_smul]
  rw [hx]
  module

/-- For the literal one-step CMP99 precision, the complete adjoint mass
cancels from the consecutive rectangular defect.  What remains is exactly
the Dirichlet covariant-Laplacian boundary defect. -/
theorem cmp99OmegaSourcePhysicalOneStepPrecisionDefect_eq_laplacianDefect
    {Nc : ℕ} [NeZero Nc]
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 1))
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc)
    (spacing a : ℝ) :
    cmp99TypedPrecisionDefect
        (cmp99OmegaSourcePhysicalOneStepGaugePrecision Seq
          (cmp99OmegaTransitionIndex r) rho U spacing a)
        (cmp99OmegaSourcePhysicalOneStepGaugePrecision Seq
          (cmp99OmegaTransitionNextIndex r) rho U spacing a)
        (cmp99OmegaTransitionRestriction (M := M) Seq r) =
      cmp99TypedPrecisionDefect
        (cmp99OmegaSourceCovariantLaplacian Seq
          (cmp99OmegaTransitionIndex r) rho U spacing)
        (cmp99OmegaSourceCovariantLaplacian Seq
          (cmp99OmegaTransitionNextIndex r) rho U spacing)
        (cmp99OmegaTransitionRestriction (M := M) Seq r) := by
  rw [cmp99OmegaSourcePhysicalOneStepGaugePrecision,
    cmp99OmegaSourcePhysicalOneStepGaugePrecision,
    cmp99SourceGaugePrecision, cmp99SourceGaugePrecision]
  exact cmp99TypedPrecisionDefect_add_mass_eq _ _ _ _ _ _
    (cmp99OmegaSourcePhysicalOneStepMass_transition Seq r rho U)

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
