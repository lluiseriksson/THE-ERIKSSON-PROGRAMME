/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP96SourceRegionAdmissibility
import YangMills.RG.BalabanCMP99SourceOmegaTerminalRegion
import YangMills.RG.BalabanCMP99SourceScaledStratification

/-!
# Scale-faithful local Omega geometry for CMP99 p. 408

CMP96 (2.2) keeps every physical domain on the fine carrier and writes

`Omega_r = B^r(Omega_r^(r))`.

The coarse index type therefore depends on `r`, while the lifted region does
not.  This is essential on CMP99 p. 408: the successive gap
`2 R0 M0 L^r eta` can be strictly smaller than one of the large blocks used
at level `j`, and is invisible in a family stored only on that coarse lattice.

This file records the correct dependent geometry.  The coarse regions are
physical boundary data because CMP96 permits many admissible sequences; the
fine regions, their block realization, the terminal intersection and the gap
statements are fixed by the type.  A projection to the older single-lattice
geometry is provided only when its additional `Omega_0 subset tilde Pi^5`
envelope has been proved.
-/

namespace YangMills.RG

noncomputable section

/-- The literal p. 408 gap in units of the original fine lattice spacing. -/
def cmp99SourceLocalOmegaGap (R0 M0 L : ℕ) (r : ℕ) : ℕ :=
  2 * R0 * M0 * L ^ r

theorem cmp99SourceLocalOmegaGap_pos
    {R0 M0 L r : ℕ} (hR0 : 0 < R0) (hM0 : 0 < M0) (hL : 0 < L) :
    0 < cmp99SourceLocalOmegaGap R0 M0 L r := by
  unfold cmp99SourceLocalOmegaGap
  positivity

/-- Pointwise lattice form of the local p. 408 separation
`dist(Omega_r^c, Omega_{r+1}) >= 2 R0 M0 L^r eta`. -/
def CMP99SourceLocalOmegaSeparated
    {FineSite : Type*} [DecidableEq FineSite]
    (dist : FineSite → FineSite → ℕ) (gap : ℕ)
    (outer inner : Finset FineSite) : Prop :=
  ∀ x, x ∉ outer → ∀ y, y ∈ inner → gap ≤ dist x y

universe u v

/-- Source-faithful local sequence over scale-dependent block lattices.

`coarseRegions r` is `Omega_r^(r)`, and `fineRegion r` below is therefore
definitionally the printed `B^r(Omega_r^(r))`. -/
structure CMP99SourceDependentOmegaGeometry
    (FineSite : Type u) [DecidableEq FineSite]
    (j : ℕ) (ScaleSite : Fin (j + 2) → Type v)
    [∀ r, DecidableEq (ScaleSite r)]
    (Scaled : CMP99SourceScaledStratification FineSite (j + 2) ScaleSite)
    (pi3 pi4 : Finset FineSite)
    (dist : FineSite → FineSite → ℕ) (gap : Fin (j + 1) → ℕ) where
  coarseRegions : ∀ r : Fin (j + 2), Finset (ScaleSite r)
  nested : Antitone (fun r =>
    (coarseRegions r).biUnion (Scaled.fineBlock r))
  omega_j_eq_pi4 :
    (coarseRegions (cmp99OmegaPi4Index j)).biUnion
        (Scaled.fineBlock (cmp99OmegaPi4Index j)) = pi4
  omega_last_eq_pi3_inter_globalStratum :
    (coarseRegions (cmp99OmegaLastIndex j)).biUnion
        (Scaled.fineBlock (cmp99OmegaLastIndex j)) =
      pi3 ∩ Scaled.global.stratum
        (cmp99OmegaTerminalGlobalStratumIndex j)
  separated : ∀ r : Fin (j + 1),
    CMP99SourceLocalOmegaSeparated dist (gap r)
      ((coarseRegions (cmp99OmegaTransitionIndex r)).biUnion
        (Scaled.fineBlock (cmp99OmegaTransitionIndex r)))
      ((coarseRegions (cmp99OmegaTransitionNextIndex r)).biUnion
        (Scaled.fineBlock (cmp99OmegaTransitionNextIndex r)))

namespace CMP99SourceDependentOmegaGeometry

variable {FineSite : Type u} [DecidableEq FineSite]
variable {j : ℕ} {ScaleSite : Fin (j + 2) → Type v}
variable [∀ r, DecidableEq (ScaleSite r)]
variable {Scaled : CMP99SourceScaledStratification FineSite (j + 2) ScaleSite}
variable {pi3 pi4 : Finset FineSite}
variable {dist : FineSite → FineSite → ℕ} {gap : Fin (j + 1) → ℕ}

/-- The literal physical fine region `B^r(Omega_r^(r))`. -/
noncomputable def fineRegion
    (D : CMP99SourceDependentOmegaGeometry
      FineSite j ScaleSite Scaled pi3 pi4 dist gap)
    (r : Fin (j + 2)) : Finset FineSite :=
  (D.coarseRegions r).biUnion (Scaled.fineBlock r)

@[simp] theorem fineRegion_eq_biUnion
    (D : CMP99SourceDependentOmegaGeometry
      FineSite j ScaleSite Scaled pi3 pi4 dist gap)
    (r : Fin (j + 2)) :
    D.fineRegion r =
      (D.coarseRegions r).biUnion (Scaled.fineBlock r) := rfl

/-- Later physical domains lie in earlier physical domains. -/
theorem fineRegion_subset_of_le
    (D : CMP99SourceDependentOmegaGeometry
      FineSite j ScaleSite Scaled pi3 pi4 dist gap)
    {r s : Fin (j + 2)} (hrs : r ≤ s) :
    D.fineRegion s ⊆ D.fineRegion r :=
  D.nested hrs

@[simp] theorem fineRegion_pi4Index
    (D : CMP99SourceDependentOmegaGeometry
      FineSite j ScaleSite Scaled pi3 pi4 dist gap) :
    D.fineRegion (cmp99OmegaPi4Index j) = pi4 :=
  D.omega_j_eq_pi4

@[simp] theorem fineRegion_lastIndex
    (D : CMP99SourceDependentOmegaGeometry
      FineSite j ScaleSite Scaled pi3 pi4 dist gap) :
    D.fineRegion (cmp99OmegaLastIndex j) =
      pi3 ∩ Scaled.global.stratum
        (cmp99OmegaTerminalGlobalStratumIndex j) :=
  D.omega_last_eq_pi3_inter_globalStratum

/-- The terminal domain is contained in the source `tilde Pi^3`. -/
theorem fineRegion_last_subset_pi3
    (D : CMP99SourceDependentOmegaGeometry
      FineSite j ScaleSite Scaled pi3 pi4 dist gap) :
    D.fineRegion (cmp99OmegaLastIndex j) ⊆ pi3 := by
  rw [D.fineRegion_lastIndex]
  exact Finset.inter_subset_left

/-- The exact local source gap is available on the physical fine carrier;
it has not been rounded to the level-`j` large-block lattice. -/
theorem transition_separated
    (D : CMP99SourceDependentOmegaGeometry
      FineSite j ScaleSite Scaled pi3 pi4 dist gap)
    (r : Fin (j + 1)) :
    CMP99SourceLocalOmegaSeparated dist (gap r)
      (D.fineRegion (cmp99OmegaTransitionIndex r))
      (D.fineRegion (cmp99OmegaTransitionNextIndex r)) :=
  D.separated r

/-- Forget the dependent scale indices after proving the p. 408 envelope.
This is the bridge to the already-developed single-carrier Green comparison
modules; the regions themselves remain the derived fine lifts. -/
noncomputable def toLargeBlockGeometry
    {Q : ℕ} [NeZero Q] {cell : FinBox 4 Q}
    {ScaleSite : Fin (j + 2) → Type v}
    [∀ r, DecidableEq (ScaleSite r)]
    {Scaled : CMP99SourceScaledStratification
      (FinBox 4 (2 * Q)) (j + 2) ScaleSite}
    {dist : FinBox 4 (2 * Q) → FinBox 4 (2 * Q) → ℕ}
    {gap : Fin (j + 1) → ℕ}
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (omega_zero_subset_pi5 :
      D.fineRegion (cmp99OmegaZeroIndex j) ⊆
        cmp99SourceTildePiLargeBlocks cell 5) :
    CMP99SourceOmegaGeometry cell j where
  regions := D.fineRegion
  nested := fun hrs => D.fineRegion_subset_of_le hrs
  omega_j_eq_pi4 := D.fineRegion_pi4Index
  omega_zero_subset_pi5 := omega_zero_subset_pi5

@[simp] theorem toLargeBlockGeometry_regions
    {Q : ℕ} [NeZero Q] {cell : FinBox 4 Q}
    {ScaleSite : Fin (j + 2) → Type v}
    [∀ r, DecidableEq (ScaleSite r)]
    {Scaled : CMP99SourceScaledStratification
      (FinBox 4 (2 * Q)) (j + 2) ScaleSite}
    {dist : FinBox 4 (2 * Q) → FinBox 4 (2 * Q) → ℕ}
    {gap : Fin (j + 1) → ℕ}
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5)
    (r : Fin (j + 2)) :
    (D.toLargeBlockGeometry hpi5).regions r = D.fineRegion r := rfl

/-- The projected terminal member is still the exact p. 408 intersection,
not an arbitrary subset of `tilde Pi^4`. -/
theorem toLargeBlockGeometry_last_region
    {Q : ℕ} [NeZero Q] {cell : FinBox 4 Q}
    {ScaleSite : Fin (j + 2) → Type v}
    [∀ r, DecidableEq (ScaleSite r)]
    {Scaled : CMP99SourceScaledStratification
      (FinBox 4 (2 * Q)) (j + 2) ScaleSite}
    {dist : FinBox 4 (2 * Q) → FinBox 4 (2 * Q) → ℕ}
    {gap : Fin (j + 1) → ℕ}
    (D : CMP99SourceDependentOmegaGeometry
      (FinBox 4 (2 * Q)) j ScaleSite Scaled
      (cmp99SourceTildePiLargeBlocks cell 3)
      (cmp99SourceTildePiLargeBlocks cell 4) dist gap)
    (hpi5 : D.fineRegion (cmp99OmegaZeroIndex j) ⊆
      cmp99SourceTildePiLargeBlocks cell 5) :
    (D.toLargeBlockGeometry hpi5).regions (cmp99OmegaLastIndex j) =
      cmp99SourceTildePiLargeBlocks cell 3 ∩
        Scaled.global.stratum
          (cmp99OmegaTerminalGlobalStratumIndex j) := by
  rw [toLargeBlockGeometry_regions, D.fineRegion_lastIndex]

end CMP99SourceDependentOmegaGeometry

end

end YangMills.RG
