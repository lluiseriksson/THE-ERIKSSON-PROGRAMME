/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.AppendixFQuantitative

/-!
# Appendix F: finite target-fiber entropy bound

This module closes the elementary finite entropy step for the first
Appendix-F activity.  A target fiber is a set of connected microscopic covers
whose full-support union projects to the same target `Y`.  For nonnegative
weights, we may forget connectedness and exact-union constraints, overcount by
all nonempty subsets of the indices whose target support is contained in `Y`,
and absorb the result into `exp (sum weights) - 1`.

This is a finite combinatorial bound only.  It does not prove Dimock (642), the
local modified-metric summability input, ultralocal integration, the second
Ursell expansion, or a Yang--Mills raw activity estimate.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

attribute [local instance] Classical.propDecidable

namespace YangMills.RG

open Finset
open scoped BigOperators

/-- Active skeletons are monotone under inclusion of full polymers. -/
theorem skeleton_mono_of_subset
    {d L : ℕ} (HF : HoleFamily d L)
    {X Y : Finset (Cube d L)} (hXY : X ⊆ Y) :
    skeleton HF X ⊆ skeleton HF Y := by
  intro r hr
  rw [skeleton, mem_filter] at hr ⊢
  exact ⟨hXY hr.1, hr.2⟩

/-- A target fiber is contained in the nonempty powerset of raw indices whose
declared target support is itself contained in the target `Y`.  This is the
finite `Π⁻¹(Y) ⊆ 𝒫(I_Y) \ {∅}` step. -/
theorem appendixFTargetFiber_subset_nonemptyPowerset
    {Site ι : Type*} [DecidableEq Site] [DecidableEq ι]
    (Ω : Finset Site)
    (overlapSupport targetSupport : ι → Finset Site)
    (Λ : Finset ι) (Y : Finset Site) :
    appendixFTargetFiber Ω overlapSupport targetSupport Λ Y ⊆
      ((Λ.filter fun i => targetSupport i ⊆ Y).powerset.erase ∅) := by
  classical
  intro C hC
  rw [Finset.mem_erase, Finset.mem_powerset]
  have hCfiber :
      C ∈ (appendixFConnectedCoverRegion Ω overlapSupport Λ).filter
        (fun C => appendixFCoverUnion targetSupport C = Y) := by
    simpa [appendixFTargetFiber] using hC
  have hCregion :
      C ∈ appendixFConnectedCoverRegion Ω overlapSupport Λ :=
    (Finset.mem_filter.mp hCfiber).1
  have hCdata :=
    (mem_appendixFConnectedCoverRegion_iff Ω overlapSupport Λ C).mp hCregion
  constructor
  · intro hEmpty
    subst hEmpty
    simpa using hCdata.2.1
  · intro i hi
    rw [Finset.mem_filter]
    exact ⟨hCdata.1 hi,
      targetSupport_subset_of_mem_appendixFConnectedActivityFiber
        Ω overlapSupport targetSupport Λ Y hCfiber hi⟩

private theorem prod_one_add_le_exp_sum_finset
    {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) :
    (∏ i ∈ s, (1 + w i)) ≤ Real.exp (∑ i ∈ s, w i) := by
  rw [Real.exp_sum]
  refine Finset.prod_le_prod ?nonneg ?bound
  · intro i hi
    exact add_nonneg zero_le_one (hw i hi)
  · intro i _hi
    have h := Real.add_one_le_exp (w i)
    linarith

/-- Summing a nonnegative product weight over all nonempty subsets is bounded
by `exp (sum weights) - 1`. -/
theorem sum_powerset_erase_empty_prod_le_exp_sub_one
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (w : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) :
    (∑ C ∈ s.powerset.erase ∅, ∏ i ∈ C, w i)
      ≤ Real.exp (∑ i ∈ s, w i) - 1 := by
  classical
  have hpowerset :
      (∑ C ∈ s.powerset, ∏ i ∈ C, w i) =
        ∏ i ∈ s, (1 + w i) := by
    have hprod :
        (∏ i ∈ s, (1 + w i)) =
          ∑ C ∈ s.powerset, ∏ i ∈ C, w i := by
      have hcomm : ∀ i ∈ s, 1 + w i = w i + 1 := by
        intro i _hi
        ring
      rw [Finset.prod_congr rfl hcomm, Finset.prod_add]
      exact Finset.sum_congr rfl fun C _hC => by
        rw [Finset.prod_const_one, mul_one]
    exact hprod.symm
  have hempty : (∅ : Finset ι) ∈ s.powerset := by
    rw [Finset.mem_powerset]
    exact empty_subset _
  have hsum_erase_add :
      (∑ C ∈ s.powerset.erase ∅, ∏ i ∈ C, w i) + 1 =
        ∑ C ∈ s.powerset, ∏ i ∈ C, w i := by
    simpa only [Finset.prod_empty] using
      (Finset.sum_erase_add s.powerset
        (fun C : Finset ι => ∏ i ∈ C, w i) hempty)
  have hfull_le :
      (∑ C ∈ s.powerset, ∏ i ∈ C, w i) ≤
        Real.exp (∑ i ∈ s, w i) := by
    rw [hpowerset]
    exact prod_one_add_le_exp_sum_finset s w hw
  have hplus :
      (∑ C ∈ s.powerset.erase ∅, ∏ i ∈ C, w i) + 1 ≤
        Real.exp (∑ i ∈ s, w i) := by
    rw [hsum_erase_add]
    exact hfull_le
  linarith

/-- The finite target-fiber entropy bound.  For nonnegative raw weights, the
fiber contribution to `K(Y)` is bounded by the exponential of the total weight
of every raw index whose target support is contained in `Y`, minus the empty
cover.  This is the precise finite overcounting step used before the later
modified-metric local summability estimate. -/
theorem appendixFTargetFiber_prod_le_exp_sub_one
    {Site ι : Type*} [DecidableEq Site] [DecidableEq ι]
    (Ω : Finset Site)
    (overlapSupport targetSupport : ι → Finset Site)
    (Λ : Finset ι) (Y : Finset Site) (w : ι → ℝ)
    (hw : ∀ i, i ∈ Λ → 0 ≤ w i) :
    (∑ C ∈ appendixFTargetFiber Ω overlapSupport targetSupport Λ Y,
        ∏ i ∈ C, w i)
      ≤
    Real.exp
        (∑ i ∈ Λ.filter (fun i => targetSupport i ⊆ Y), w i) - 1 := by
  classical
  let ΛY : Finset ι := Λ.filter fun i => targetSupport i ⊆ Y
  have hsub :
      appendixFTargetFiber Ω overlapSupport targetSupport Λ Y ⊆
        ΛY.powerset.erase ∅ := by
    simpa [ΛY] using
      appendixFTargetFiber_subset_nonemptyPowerset
        Ω overlapSupport targetSupport Λ Y
  have hnonneg :
      ∀ C ∈ ΛY.powerset.erase ∅,
        C ∉ appendixFTargetFiber Ω overlapSupport targetSupport Λ Y →
          0 ≤ ∏ i ∈ C, w i := by
    intro C hC _hnot
    rw [Finset.mem_erase, Finset.mem_powerset] at hC
    exact Finset.prod_nonneg fun i hi =>
      hw i ((Finset.mem_filter.mp (hC.2 hi)).1)
  have hsum_le :
      (∑ C ∈ appendixFTargetFiber Ω overlapSupport targetSupport Λ Y,
          ∏ i ∈ C, w i)
        ≤ ∑ C ∈ ΛY.powerset.erase ∅, ∏ i ∈ C, w i :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub hnonneg
  have hΛY_nonneg : ∀ i ∈ ΛY, 0 ≤ w i := by
    intro i hi
    exact hw i ((Finset.mem_filter.mp hi).1)
  exact hsum_le.trans
    (by
      simpa [ΛY] using
        sum_powerset_erase_empty_prod_le_exp_sub_one ΛY w hΛY_nonneg)

end YangMills.RG
