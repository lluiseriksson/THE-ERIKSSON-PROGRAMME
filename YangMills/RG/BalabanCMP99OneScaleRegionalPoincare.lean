/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99OneScaleBlockPoincare
import YangMills.RG.BalabanCMP99SourceWeightedPhysicalTower
import YangMills.RG.BalabanCMP99SourcePhysicalGaugePrecision

/-!
# Regional Dirichlet form of the one-scale CMP99 Poincare estimate

The full-periodic one-scale estimate is transported here to every
block-saturated active region by literal zero extension.  The full block
average of the extended field is proved equal to the zero extension of the
regional source average; no boundary or volume constant is introduced.
-/

namespace YangMills.RG

open YangMills
open scoped BigOperators RealInnerProductSpace

noncomputable section

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

@[simp] theorem extendZeroZeroCLM_apply_of_mem
    {d N : ℕ} [NeZero N]
    {g : Type*} [NormedAddCommGroup g] [InnerProductSpace ℝ g]
    [FiniteDimensional ℝ g]
    (Omega : ActiveGaugeRegion d N)
    (phi : ActiveGaugeZeroCochain Omega g)
    (x : FinBox d N) (hx : x ∈ Omega.sites) :
    extendZeroZeroCLM Omega phi x = phi ⟨x, hx⟩ := by
  simp [extendZeroZeroCLM, hx]

@[simp] theorem extendZeroZeroCLM_apply_of_not_mem
    {d N : ℕ} [NeZero N]
    {g : Type*} [NormedAddCommGroup g] [InnerProductSpace ℝ g]
    [FiniteDimensional ℝ g]
    (Omega : ActiveGaugeRegion d N)
    (phi : ActiveGaugeZeroCochain Omega g)
    (x : FinBox d N) (hx : x ∉ Omega.sites) :
    extendZeroZeroCLM Omega phi x = 0 := by
  simp [extendZeroZeroCLM, hx]

/-- Dirichlet zero extension is an isometry for every finite active region. -/
theorem norm_extendZeroZeroCLM_eq
    {d N : ℕ} [NeZero N]
    {g : Type*} [NormedAddCommGroup g] [InnerProductSpace ℝ g]
    [FiniteDimensional ℝ g]
    (Omega : ActiveGaugeRegion d N)
    (phi : ActiveGaugeZeroCochain Omega g) :
    ‖extendZeroZeroCLM Omega phi‖ = ‖phi‖ := by
  have hsq : ‖extendZeroZeroCLM Omega phi‖ ^ 2 = ‖phi‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
    calc
      ∑ x : FinBox d N,
          ‖extendZeroZeroCLM Omega phi x‖ ^ 2 =
        ∑ x ∈ Omega.sites, ‖extendZeroZeroCLM Omega phi x‖ ^ 2 := by
          symm
          apply Finset.sum_subset (Finset.subset_univ Omega.sites)
          intro x _hx hxOmega
          simp [extendZeroZeroCLM, hxOmega]
      _ = ∑ x : ActiveGaugeRegion.Site Omega,
          ‖extendZeroZeroCLM Omega phi x.1‖ ^ 2 := by
            exact Finset.sum_subtype Omega.sites (fun x => Iff.rfl)
              (fun x => ‖extendZeroZeroCLM Omega phi x‖ ^ 2)
      _ = ∑ x : ActiveGaugeRegion.Site Omega, ‖phi x‖ ^ 2 := by
            apply Finset.sum_congr rfl
            intro x _hx
            simp [extendZeroZeroCLM, x.2]
  nlinarith [norm_nonneg (extendZeroZeroCLM Omega phi), norm_nonneg phi]

/-- The full source average of a zero-extended regional field is exactly the
zero extension of the regional source average. -/
theorem cmp99FullSourceBlockAverage_extendZero_eq
    (Omega : ActiveGaugeRegion d (M * N'))
    (hOmega : Omega.BlockSaturated)
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (phi : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc)) :
    cmp99FullSourceBlockAverage rho U (extendZeroZeroCLM Omega phi) =
      extendZeroZeroCLM
        (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega)
        (cmp99SourceTransportedBlockAverageCLM Omega
          (cmp99SourceWeightedPhysicalTransport rho U) phi) := by
  apply PiLp.ext
  intro y
  by_cases hy : y ∈
      (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega).sites
  · let ya : ActiveGaugeRegion.Site
        (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega) := ⟨y, hy⟩
    rw [cmp99FullSourceBlockAverage_apply]
    rw [extendZeroZeroCLM_apply_of_mem _ _ _ hy]
    change cmp99FullSourceBlockAverageValue rho U
        (extendZeroZeroCLM Omega phi) y =
      cmp99SourceTransportedBlockAverageCLM Omega
        (cmp99SourceWeightedPhysicalTransport rho U) phi ya
    unfold cmp99SourceTransportedBlockAverageCLM
    rw [cmp99TransportedBlockAverageCLM_apply]
    unfold cmp99FullSourceBlockAverageValue
    congr 1
    apply Finset.sum_congr rfl
    intro x _hx
    have hxActive : x.1 ∈ Omega.sites :=
      (mem_cmp99ActiveCoarseRegion_sites_iff
        (M := M) (N' := N') Omega y).mp hy x.2
    simp only [cmp99SourceWeightedPhysicalTransport,
      cmp99AdjointBlockTransport_apply]
    simp [extendZeroZeroCLM, hxActive]
    congr 2
  · rw [cmp99FullSourceBlockAverage_apply]
    rw [extendZeroZeroCLM_apply_of_not_mem _ _ _ hy]
    change cmp99FullSourceBlockAverageValue rho U
        (extendZeroZeroCLM Omega phi) y = 0
    unfold cmp99FullSourceBlockAverageValue
    have hzero : ∀ x : {x : FinBox d (M * N') // x ∈ blockOf M N' y},
        extendZeroZeroCLM Omega phi x.1 = 0 := by
      intro x
      have hxNot : x.1 ∉ Omega.sites := by
        intro hxActive
        apply hy
        rw [mem_cmp99ActiveCoarseRegion_sites_iff]
        have howner : blockSite M N' x.1 = y :=
          (mem_blockOf M N' y x.1).mp x.2
        simpa [howner] using hOmega x.1 hxActive
      simp [extendZeroZeroCLM, hxNot]
    simp_rw [hzero]
    simp

/-- Regional one-scale Poincare estimate with the literal physical source
average and Dirichlet derivative. -/
theorem norm_sq_le_cmp99OneScaleRegionalPoincare
    (Omega : ActiveGaugeRegion d (M * N'))
    (hOmega : Omega.BlockSaturated)
    (rho : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (phi : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc)) :
    ‖phi‖ ^ 2 ≤
      cmp99OneScaleBlockPoincareConstant d M *
        (‖covariantD0CLM rho U (extendZeroZeroCLM Omega phi)‖ ^ 2 +
          ‖cmp99SourceTransportedBlockAverageCLM Omega
            (cmp99SourceWeightedPhysicalTransport rho U) phi‖ ^ 2) := by
  have hfull := norm_sq_le_cmp99OneScaleBlockPoincare rho U
    (extendZeroZeroCLM Omega phi)
  rw [norm_extendZeroZeroCLM_eq Omega phi] at hfull
  rw [cmp99FullSourceBlockAverage_extendZero_eq
    Omega hOmega rho U phi] at hfull
  have hnorm := norm_extendZeroZeroCLM_eq
      (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega)
      (cmp99SourceTransportedBlockAverageCLM Omega
        (cmp99SourceWeightedPhysicalTransport rho U) phi)
  rw [hnorm] at hfull
  exact hfull

end

end YangMills.RG
