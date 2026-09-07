/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceRegionalCoarseAverage

/-!
# Reindexing a saturated source region by its active blocks

A block-saturated active region is the disjoint union of the complete fine
blocks indexed by its active coarse region.  This is the exact reindexing
needed to expose the cancellation
`M^d * cmp99SourceBlockAverageWeight M d = 1`; it introduces neither an
ambient-volume cardinality nor a second overlap constant.
-/

namespace YangMills.RG

open scoped BigOperators

noncomputable section

variable {d M N' : ℕ} [NeZero M] [NeZero N']

/-- A fine active site is canonically its active owner block together with
the same fine site regarded as a member of that complete block. -/
noncomputable def cmp99ActiveFineBlockSigmaEquiv
    (Omega : ActiveGaugeRegion d (M * N'))
    (hOmega : Omega.BlockSaturated) :
    ActiveGaugeRegion.Site Omega ≃
      Σ y : ActiveGaugeRegion.Site
          (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega),
        {x : FinBox d (M * N') // x ∈ blockOf M N' y.1} where
  toFun x :=
    let y : ActiveGaugeRegion.Site
        (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega) :=
      ⟨blockSite M N' x.1,
        (mem_cmp99ActiveCoarseRegion_sites_iff Omega _).2
          (hOmega x.1 x.2)⟩
    ⟨y, ⟨x.1, (mem_blockOf M N' y.1 x.1).2 rfl⟩⟩
  invFun z := cmp99ActiveFineSiteOfBlock Omega z.1 z.2
  left_inv x := by
    apply Subtype.ext
    rfl
  right_inv z := by
    rcases z with ⟨y, x⟩
    let y' : ActiveGaugeRegion.Site
        (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega) :=
      ⟨blockSite M N' x.1,
        (mem_cmp99ActiveCoarseRegion_sites_iff Omega _).2
          (hOmega x.1
            (cmp99ActiveFineSiteOfBlock Omega y x).2)⟩
    have hy' : y' = y := by
      apply Subtype.ext
      exact (mem_blockOf M N' y.1 x.1).1 x.2
    change (⟨y', ⟨x.1, _⟩⟩ :
      Σ y : ActiveGaugeRegion.Site
          (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega),
        {x : FinBox d (M * N') // x ∈ blockOf M N' y.1}) = ⟨y, x⟩
    apply Sigma.ext
    · exact hy'
    · apply (Subtype.heq_iff_coe_eq (fun z => by
          rw [congrArg (fun block => block.1) hy'])).2
      rfl

/-- Reindex a sum over a saturated fine region as the iterated sum over its
active coarse blocks and the complete fine sites of each block. -/
theorem sum_activeGaugeRegion_eq_sum_activeBlocks
    {A : Type*} [AddCommMonoid A]
    (Omega : ActiveGaugeRegion d (M * N'))
    (hOmega : Omega.BlockSaturated)
    (f : ActiveGaugeRegion.Site Omega → A) :
    (∑ x, f x) =
      ∑ y : ActiveGaugeRegion.Site
          (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega),
        ∑ x : {x : FinBox d (M * N') // x ∈ blockOf M N' y.1},
          f (cmp99ActiveFineSiteOfBlock Omega y x) := by
  classical
  let e := cmp99ActiveFineBlockSigmaEquiv Omega hOmega
  have h := e.sum_comp (fun z => f (e.symm z))
  calc
    (∑ x, f x) = ∑ z, f (e.symm z) := by simpa using h
    _ = ∑ y, ∑ x, f (e.symm ⟨y, x⟩) := Fintype.sum_sigma _
    _ = ∑ y : ActiveGaugeRegion.Site
          (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega),
        ∑ x : {x : FinBox d (M * N') // x ∈ blockOf M N' y.1},
          f (cmp99ActiveFineSiteOfBlock Omega y x) := by
      apply Fintype.sum_congr
      intro y
      apply Fintype.sum_congr
      intro x
      rfl

end

end YangMills.RG
