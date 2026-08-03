/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP95RescaledPeriodicSquarePartition
import YangMills.RG.BalabanCMP99SourceRegionalGreenNeumann

/-!
# The literal fine partition for the CMP99 regional Green construction

PRE-VALIDATION: this source is present, but its `.olean` has not yet been
materialized and its result is not compiler-verified.

The regional Neumann algebra must use the smooth cutoff on the actual fine
lattice.  Pulling the coarse partition back through `blockSite` is
piecewise constant and loses the `M₀⁻¹` slope in CMP99 (3.89).  This file
installs the already generated fine CMP95 partition instead.

It also gives a canonical support thickening by the physical finite range.
The resulting margin is proved from the definition; identifying this
thickening with the printed `Pi^4` region remains a separate geometric
dictionary rather than a hidden equality.
-/

namespace YangMills.RG

open scoped BigOperators

noncomputable section

variable {M Q depth : ℕ} [NeZero M] [NeZero Q]

/-- Transport the factored fine side `M^(depth+1) * (2Q)` to the recursively
generated lattice side used by the source partition. -/
def cmp99RegionalFactoredToGeneratedFineSite
    (x : FinBox 4 (M ^ (depth + 1) * (2 * Q))) :
    FinBox 4 (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) :=
  fun i => Fin.cast
    (cmp99RegionalLatticeSize_eq_pow_mul M (2 * Q) (depth + 1)).symm (x i)

/-- Literal CMP95 fine partition, expressed on the factored carrier used by
the regional Dirichlet algebra. -/
noncomputable def cmp99SourceGeneratedRegionalFineSquarePartition
    (P : CMP95SourceSmoothPartitionProfile) :
    CMP99RegionalFineSquarePartition (M ^ (depth + 1)) Q where
  value cell x := cmp99SourceGeneratedFineCellCutoff P M Q depth cell
    (cmp99RegionalFactoredToGeneratedFineSite x)
  square_sum x :=
    sum_cmp99SourceGeneratedFineCellCutoff_sq P M Q depth
      (cmp99RegionalFactoredToGeneratedFineSite x)

/-- Public normalization theorem for the physical fine partition. -/
theorem cmp99SourceGeneratedRegionalFineSquarePartition_square_sum
    (P : CMP95SourceSmoothPartitionProfile)
    (x : FinBox 4 (M ^ (depth + 1) * (2 * Q))) :
    ∑ cell : FinBox 4 Q,
      (cmp99SourceGeneratedRegionalFineSquarePartition
        (M := M) (Q := Q) (depth := depth) P).value cell x ^ 2 = 1 :=
  (cmp99SourceGeneratedRegionalFineSquarePartition
    (M := M) (Q := Q) (depth := depth) P).square_sum x

/-- The radius-`finiteRange` neighborhood of the literal nonzero cutoff
support.  This is an active Dirichlet region on the same fine carrier. -/
noncomputable def cmp99RegionalFineSupportThickening
    (P : CMP99RegionalFineSquarePartition M Q) (finiteRange : ℕ)
    (cell : FinBox 4 Q) : ActiveGaugeRegion 4 (M * (2 * Q)) :=
  ActiveGaugeRegion.mk <| Finset.univ.filter fun y =>
    ∃ x, P.value cell x ≠ 0 ∧ finBoxDist x y ≤ finiteRange

/-- The canonical support thickening has exactly the finite-range margin
required by the regional Green algebra. -/
theorem cmp99RegionalFineSupportThickening_hasFiniteRangeMargin
    (P : CMP99RegionalFineSquarePartition M Q) (finiteRange : ℕ) :
    CMP99RegionalSquarePartitionHasFiniteRangeMargin P
      (cmp99RegionalFineSupportThickening P finiteRange) finiteRange := by
  intro cell x y hx hy
  by_contra hnot
  have hxy : finBoxDist x y ≤ finiteRange := Nat.le_of_not_gt hnot
  apply hy
  change y ∈ Finset.univ.filter fun z =>
    ∃ w, P.value cell w ≠ 0 ∧ finBoxDist w z ≤ finiteRange
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨x, hx, hxy⟩

/-- Hence the fine cutoff is supported inside its canonical Dirichlet
region, with no independent support premise. -/
theorem cmp99RegionalFineSupportThickening_supported
    (P : CMP99RegionalFineSquarePartition M Q) (finiteRange : ℕ) :
    CMP99RegionalSquarePartitionSupported P
      (cmp99RegionalFineSupportThickening P finiteRange) :=
  cmp99RegionalSquarePartitionSupported_of_finiteRangeMargin
    P (cmp99RegionalFineSupportThickening P finiteRange) finiteRange
      (cmp99RegionalFineSupportThickening_hasFiniteRangeMargin P finiteRange)

end

end YangMills.RG
