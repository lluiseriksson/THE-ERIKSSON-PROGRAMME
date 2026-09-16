/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116SourcePi4ShiftedComplexContour
import YangMills.RG.BalabanCMP116SourceSigmaZeroActiveCarrier
import YangMills.RG.ComplexWeakeningMonomialDifference

/-!
# A source-localized CMP116 complex weakening contour

The global source coupling `cmp116SourcePi4ShiftedCoupling` identifies the
Cauchy coordinates with every weakening cube in the periodic volume.  A
single localized equation-(2.14) term instead varies only its finite physical
carrier and leaves every other weakening variable at full coupling.

This file makes that distinction structural.  The coordinate equivalence has
codomain the carrier subtype, so its dimension is definitionally tied to the
localized carrier rather than to the ambient volume.  The first lemmas prove
the exact support and monomial identities needed before any determinant or
`R₁` estimate is attempted.
-/

namespace YangMills.RG

noncomputable section

open scoped BigOperators

/-- Translate zero-based Cauchy coordinates to source weakening coordinates
on one finite carrier.  Outside the carrier the coupling is exactly one. -/
def cmp116SourceRestrictedShiftedCoupling
    {n : ℕ} {Δ : Type*} [DecidableEq Δ]
    (carrier : Finset Δ) (e : Fin n ≃ ↥carrier)
    (z : Fin n → ℂ) : Δ → ℂ :=
  fun d => if h : d ∈ carrier then 1 + z (e.symm ⟨d, h⟩) else 1

/-- The number of Cauchy coordinates is forced by the localized carrier,
not by the cardinality of the ambient periodic volume. -/
theorem cmp116SourceRestrictedShiftedCoupling_card
    {n : ℕ} {Δ : Type*} [DecidableEq Δ]
    (carrier : Finset Δ) (e : Fin n ≃ ↥carrier) :
    n = carrier.card := by
  simpa using Fintype.card_congr e

@[simp]
theorem cmp116SourceRestrictedShiftedCoupling_zero
    {n : ℕ} {Δ : Type*} [DecidableEq Δ]
    (carrier : Finset Δ) (e : Fin n ≃ ↥carrier) :
    cmp116SourceRestrictedShiftedCoupling carrier e 0 = fun _ => 1 := by
  funext d
  simp [cmp116SourceRestrictedShiftedCoupling]

@[simp]
theorem cmp116SourceRestrictedShiftedCoupling_eq_one_of_not_mem
    {n : ℕ} {Δ : Type*} [DecidableEq Δ]
    (carrier : Finset Δ) (e : Fin n ≃ ↥carrier)
    (z : Fin n → ℂ) {d : Δ} (hd : d ∉ carrier) :
    cmp116SourceRestrictedShiftedCoupling carrier e z d = 1 := by
  simp [cmp116SourceRestrictedShiftedCoupling, hd]

@[simp]
theorem norm_cmp116SourceRestrictedShiftedCoupling_sub_one_of_mem
    {n : ℕ} {Δ : Type*} [DecidableEq Δ]
    (carrier : Finset Δ) (e : Fin n ≃ ↥carrier)
    (z : Fin n → ℂ) {d : Δ} (hd : d ∈ carrier) :
    ‖cmp116SourceRestrictedShiftedCoupling carrier e z d - 1‖ =
      ‖z (e.symm ⟨d, hd⟩)‖ := by
  simp [cmp116SourceRestrictedShiftedCoupling, hd]

@[simp]
theorem norm_cmp116SourceRestrictedShiftedCoupling_sub_one_of_not_mem
    {n : ℕ} {Δ : Type*} [DecidableEq Δ]
    (carrier : Finset Δ) (e : Fin n ≃ ↥carrier)
    (z : Fin n → ℂ) {d : Δ} (hd : d ∉ carrier) :
    ‖cmp116SourceRestrictedShiftedCoupling carrier e z d - 1‖ = 0 := by
  simp [cmp116SourceRestrictedShiftedCoupling, hd]

/-- A shifted Cauchy-polydisc certificate gives the source deviation bound on
the carrier.  No ambient coordinate is introduced. -/
theorem norm_cmp116SourceRestrictedShiftedCoupling_sub_one_le
    {n : ℕ} {Δ : Type*} [DecidableEq Δ]
    (carrier : Finset Δ) (e : Fin n ≃ ↥carrier)
    (radius : Fin n → ℝ) (z : Fin n → ℂ)
    (hz : CMP116Eq214ShiftedPolydisc n radius z)
    {d : Δ} (hd : d ∈ carrier) :
    ‖cmp116SourceRestrictedShiftedCoupling carrier e z d - 1‖ ≤
      1 + radius (e.symm ⟨d, hd⟩) := by
  rw [norm_cmp116SourceRestrictedShiftedCoupling_sub_one_of_mem
    carrier e z hd]
  exact hz (e.symm ⟨d, hd⟩)

/-- A single global radius dominating all shifted coordinate radii controls
the source weakening uniformly on the ambient cube.  Outside the contour
carrier the deviation is exactly zero. -/
theorem norm_cmp116SourceRestrictedShiftedCoupling_sub_one_le_global
    {n : ℕ} {Δ : Type*} [DecidableEq Δ]
    (carrier : Finset Δ) (e : Fin n ≃ ↥carrier)
    (radius : Fin n → ℝ) (z : Fin n → ℂ)
    (hz : CMP116Eq214ShiftedPolydisc n radius z)
    {globalRadius : ℝ} (hglobal : 0 ≤ globalRadius)
    (hcap : ∀ i, 1 + radius i ≤ globalRadius) (d : Δ) :
    ‖cmp116SourceRestrictedShiftedCoupling carrier e z d - 1‖ ≤
      globalRadius := by
  by_cases hd : d ∈ carrier
  · exact
      (norm_cmp116SourceRestrictedShiftedCoupling_sub_one_le
        carrier e radius z hz hd).trans
        (hcap (e.symm ⟨d, hd⟩))
  · rw [norm_cmp116SourceRestrictedShiftedCoupling_sub_one_of_not_mem
      carrier e z hd]
    exact hglobal

/-- Uniform norm control for the restricted source weakening.  This is the
`Rweak = 1 + globalRadius` cap consumed by the physical random-walk
estimates. -/
theorem norm_cmp116SourceRestrictedShiftedCoupling_le_one_add_global
    {n : ℕ} {Δ : Type*} [DecidableEq Δ]
    (carrier : Finset Δ) (e : Fin n ≃ ↥carrier)
    (radius : Fin n → ℝ) (z : Fin n → ℂ)
    (hz : CMP116Eq214ShiftedPolydisc n radius z)
    {globalRadius : ℝ} (hglobal : 0 ≤ globalRadius)
    (hcap : ∀ i, 1 + radius i ≤ globalRadius) (d : Δ) :
    ‖cmp116SourceRestrictedShiftedCoupling carrier e z d‖ ≤
      1 + globalRadius := by
  calc
    ‖cmp116SourceRestrictedShiftedCoupling carrier e z d‖ =
        ‖(cmp116SourceRestrictedShiftedCoupling carrier e z d - 1) + 1‖ := by
      ring_nf
    _ ≤
        ‖cmp116SourceRestrictedShiftedCoupling carrier e z d - 1‖ + 1 :=
      by
        simpa using
          (norm_add_le
            (cmp116SourceRestrictedShiftedCoupling carrier e z d - 1)
            (1 : ℂ))
    _ ≤ globalRadius + 1 := by
      gcongr
      exact
        norm_cmp116SourceRestrictedShiftedCoupling_sub_one_le_global
          carrier e radius z hz hglobal hcap d
    _ = 1 + globalRadius := by ring

/-- When the local contour carrier lies in the literal `sigma₀` partition,
the distinguished `Pi⁴` collar remains exactly at full coupling. -/
theorem cmp116SourceRestrictedShiftedCoupling_eq_one_of_not_mem_sigmaZero
    {n Q : ℕ} [NeZero Q]
    (anchor : FinBox 4 Q)
    (carrier : Finset (FinBox 4 (2 * Q)))
    (hcarrier : carrier ⊆ cmp116SourceSigmaZero anchor)
    (e : Fin n ≃ ↥carrier) (z : Fin n → ℂ)
    {d : FinBox 4 (2 * Q)}
    (hd : d ∉ cmp116SourceSigmaZero anchor) :
    cmp116SourceRestrictedShiftedCoupling carrier e z d = 1 := by
  apply cmp116SourceRestrictedShiftedCoupling_eq_one_of_not_mem
  intro hdcarrier
  exact hd (hcarrier hdcarrier)

/-- A weakening monomial only sees the intersection of its walk carrier with
the localized Cauchy carrier. -/
theorem cmp116ComplexWeakeningMonomial_restrictedShiftedCoupling
    {n : ℕ} {Δ : Type*} [DecidableEq Δ]
    (active carrier : Finset Δ) (e : Fin n ≃ ↥carrier)
    (z : Fin n → ℂ) :
    cmp116ComplexWeakeningMonomial active
        (cmp116SourceRestrictedShiftedCoupling carrier e z) =
      cmp116ComplexWeakeningMonomial (active ∩ carrier)
        (cmp116SourceRestrictedShiftedCoupling carrier e z) := by
  classical
  unfold cmp116ComplexWeakeningMonomial
  symm
  apply Finset.prod_subset Finset.inter_subset_left
  intro d hdactive hdnot
  rw [cmp116SourceRestrictedShiftedCoupling_eq_one_of_not_mem
    carrier e z]
  intro hdcarrier
  exact hdnot (Finset.mem_inter.mpr ⟨hdactive, hdcarrier⟩)

/-- Exact expansion of a restricted walk defect by the nonempty subsets of
the physical contour coordinates actually visited by the walk. -/
theorem cmp116ComplexWeakeningMonomial_restrictedShiftedCoupling_sub_one_eq_sum
    {n : ℕ} {Δ : Type*} [DecidableEq Δ]
    (active carrier : Finset Δ) (e : Fin n ≃ ↥carrier)
    (z : Fin n → ℂ) :
    cmp116ComplexWeakeningMonomial active
          (cmp116SourceRestrictedShiftedCoupling carrier e z) - 1 =
      ∑ subset ∈ (active ∩ carrier).powerset.erase ∅,
        ∏ d ∈ subset,
          (cmp116SourceRestrictedShiftedCoupling carrier e z d - 1) := by
  rw [cmp116ComplexWeakeningMonomial_restrictedShiftedCoupling]
  exact
    cmp116ComplexWeakeningMonomial_sub_one_eq_sum_nonemptySubsets
      (active ∩ carrier)
      (cmp116SourceRestrictedShiftedCoupling carrier e z)

/-- A walk whose complete active carrier misses the localized contour carrier
has exactly zero weakening defect. -/
theorem cmp116ComplexWeakeningMonomial_restrictedShiftedCoupling_sub_one_eq_zero
    {n : ℕ} {Δ : Type*} [DecidableEq Δ]
    (active carrier : Finset Δ) (e : Fin n ≃ ↥carrier)
    (z : Fin n → ℂ) (hdisjoint : Disjoint active carrier) :
    cmp116ComplexWeakeningMonomial active
        (cmp116SourceRestrictedShiftedCoupling carrier e z) - 1 = 0 := by
  rw [cmp116ComplexWeakeningMonomial_restrictedShiftedCoupling]
  have hinter : active ∩ carrier = ∅ :=
    Finset.disjoint_iff_inter_eq_empty.mp hdisjoint
  simp [hinter, cmp116ComplexWeakeningMonomial]

end

end YangMills.RG
