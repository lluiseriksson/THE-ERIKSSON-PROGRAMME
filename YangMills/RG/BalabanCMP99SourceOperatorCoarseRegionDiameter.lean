/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceDependentRegionalTower
import YangMills.RG.BalabanCMP99SourceConcentricLargeBlockDiameter

/-!
# Uniform diameter of literal CMP99 operator regions

The source hypothesis places the zeroth dependent region in `tilde Pi^5` and
the regions are nested.  Hence every physical site used by every generated
operator region lies in the same volume-independent cube.
-/

namespace YangMills.RG

noncomputable section

/-- The literal Chebyshev distance on sites of a finite active gauge region. -/
def activeGaugeRegionSiteFinBoxDist {d N : ℕ}
    (Omega : ActiveGaugeRegion d N)
    (left right : ActiveGaugeRegion.Site Omega) : ℕ :=
  finBoxDist left.1 right.1

universe v

variable {Q j : ℕ} [NeZero Q]
variable {cell : FinBox 4 Q}
variable {ScaleSite : Fin (j + 2) → Type v}
variable [∀ r, DecidableEq (ScaleSite r)]
variable {Scaled : CMP99SourceScaledStratification
  (FinBox 4 (2 * Q)) (j + 2) ScaleSite}
variable {dist : FinBox 4 (2 * Q) → FinBox 4 (2 * Q) → ℕ}
variable {gap : Fin (j + 1) → ℕ}

namespace CMP99SourceDependentOmegaGeometry

set_option maxRecDepth 2000 in
set_option maxHeartbeats 1000000 in
/-- Every pair of physical sites in every generated coarse operator region
has the uniform `tilde Pi^5` diameter bound. -/
theorem operatorCoarseRegion_siteFinBoxDist_le_pi5
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (r : Fin (j + 2))
    (left right : ActiveGaugeRegion.Site (D.operatorCoarseRegion hpi5 r)) :
    activeGaugeRegionSiteFinBoxDist (D.operatorCoarseRegion hpi5 r)
      left right ≤ 1 + 2 * 5 := by
  have hzero_le : cmp99OmegaZeroIndex j ≤ r := by
    change 0 ≤ r.val
    omega
  have hleftRegion : left.1 ∈ D.fineRegion r := by
    exact left.2
  have hrightRegion : right.1 ∈ D.fineRegion r := by
    exact right.2
  have hleftPi5 : left.1 ∈ cmp99SourceTildePiLargeBlocks cell 5 :=
    hpi5 (D.fineRegion_subset_of_le hzero_le hleftRegion)
  have hrightPi5 : right.1 ∈ cmp99SourceTildePiLargeBlocks cell 5 :=
    hpi5 (D.fineRegion_subset_of_le hzero_le hrightRegion)
  exact finBoxDist_le_of_mem_cmp99SourceTildePiLargeBlocks cell 5
    hleftPi5 hrightPi5

set_option maxRecDepth 2000 in
set_option maxHeartbeats 1000000 in
/-- Every generated operator carrier has at most the literal number of large
blocks in `tilde Pi^5`.  The bound is uniform in the ambient torus and in the
regional scale. -/
theorem operatorCoarseRegion_site_card_le_pi5
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (r : Fin (j + 2)) :
    Fintype.card (ActiveGaugeRegion.Site (D.operatorCoarseRegion hpi5 r)) ≤
      20736 := by
  have hzero_le : cmp99OmegaZeroIndex j ≤ r := by
    change 0 ≤ r.val
    omega
  have hsubset : D.fineRegion r ⊆
      cmp99SourceTildePiLargeBlocks cell 5 :=
    fun _ hx => hpi5 (D.fineRegion_subset_of_le hzero_le hx)
  rw [Fintype.card_coe, D.operatorCoarseRegion_sites]
  exact (Finset.card_le_card hsubset).trans
    (card_cmp99SourceTildePi5LargeBlocks_le cell)

end CMP99SourceDependentOmegaGeometry

end

end YangMills.RG
