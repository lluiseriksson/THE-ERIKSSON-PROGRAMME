/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP95PeriodicCutoffSlope
import Mathlib.Data.Fintype.BigOperators

/-!
# Transposed overlap of the CMP95 periodic cutoffs

Compiler-verified at source checkpoint
`837040284f5ce1d358d42eb8f6c01689829db29b` in durable GitHub Actions run
`30971247380`.  The focal completed 8,495 jobs and all six audited
declarations use exactly `[propext, Classical.choice, Quot.sound]`.

CMP95 (1.118) uses one profile supported in `(-2/3,2/3)`.  Consequently, at
one fixed coordinate only the two integers bracketing that coordinate can
label nonzero translates.  Passing to residue classes modulo the finite
period cannot increase that cardinality.  Tensoring the same statement in
four dimensions gives the literal overlap bound `2^4 = 16`.

This is the transpose of the already audited fixed-cell support estimate:
the point is fixed and the source cell varies.  It is derived from the same
profile support and introduces no second overlap parameter.
-/

namespace YangMills.RG

noncomputable section

/-- The residue class of an integer translate in the finite period. -/
def cmp95PeriodicTranslateResidue
    (Q : ℕ) [NeZero Q] (n : ℤ) : Fin Q :=
  ((Int.divModEquiv Q) n).2

/-- The at-most-two residue classes whose translates can meet the source
support at a fixed one-dimensional coordinate. -/
def cmp95PeriodicActiveCellWindow
    (Q : ℕ) [NeZero Q] (t : ℝ) : Finset (Fin Q) :=
  (Finset.Icc ⌊t⌋ (⌊t⌋ + 1)).image
    (cmp95PeriodicTranslateResidue Q)

/-- Passing the two bracketing integers to residue classes cannot increase
their cardinality. -/
theorem card_cmp95PeriodicActiveCellWindow_le_two
    (Q : ℕ) [NeZero Q] (t : ℝ) :
    (cmp95PeriodicActiveCellWindow Q t).card ≤ 2 := by
  unfold cmp95PeriodicActiveCellWindow
  calc
    ((Finset.Icc ⌊t⌋ (⌊t⌋ + 1)).image
        (cmp95PeriodicTranslateResidue Q)).card ≤
        (Finset.Icc ⌊t⌋ (⌊t⌋ + 1)).card := Finset.card_image_le
    _ = 2 := by
      rw [Int.card_Icc]
      omega

/-- A nonzero residue-class square weight belongs to the transposed active
window.  The witness integer is constructed from the actual nonzero summand;
no overlap datum is accepted from the caller. -/
theorem mem_cmp95PeriodicActiveCellWindow_of_squareWeight_ne_zero
    (P : CMP95SourceSmoothPartitionProfile) (Q : ℕ) [NeZero Q]
    (cell : Fin Q) (t : ℝ)
    (hweight : cmp95PeriodicSquareWeight P Q cell t ≠ 0) :
    cell ∈ cmp95PeriodicActiveCellWindow Q t := by
  classical
  have hexists : ∃ k : ℤ,
      P.value
        (t - ((k * (Q : ℤ) + (cell.val : ℤ) : ℤ) : ℝ)) ^ 2 ≠ 0 := by
    by_contra hnone
    push_neg at hnone
    apply hweight
    unfold cmp95PeriodicSquareWeight
    calc
      (∑' k : ℤ,
          P.value
            (t - ((k * (Q : ℤ) + (cell.val : ℤ) : ℤ) : ℝ)) ^ 2) =
          ∑' _k : ℤ, 0 := tsum_congr hnone
      _ = 0 := tsum_zero
  obtain ⟨k, hk⟩ := hexists
  let n : ℤ := k * (Q : ℤ) + (cell.val : ℤ)
  have hvalue : P.value (t - (n : ℝ)) ≠ 0 := by
    intro hz
    apply hk
    push_cast [n] at hz ⊢
    rw [hz]
    norm_num
  have hsupp : t - (n : ℝ) ∈ Set.Ioo (-(2 / 3 : ℝ)) (2 / 3) :=
    P.support_subset (Function.mem_support.mpr hvalue)
  have hfloorLower : ((⌊t⌋ : ℤ) : ℝ) ≤ t := Int.floor_le t
  have hfloorUpper : t < ((⌊t⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one t
  have hnLowerReal : (((⌊t⌋ : ℤ) - 1 : ℤ) : ℝ) < (n : ℝ) := by
    rcases hsupp with ⟨hsuppLower, hsuppUpper⟩
    push_cast
    nlinarith
  have hnUpperReal : (n : ℝ) < ((((⌊t⌋ : ℤ) + 2 : ℤ)) : ℝ) := by
    rcases hsupp with ⟨hsuppLower, hsuppUpper⟩
    push_cast
    nlinarith
  have hnLower : (⌊t⌋ : ℤ) ≤ n := by
    have : (⌊t⌋ : ℤ) - 1 < n := by exact_mod_cast hnLowerReal
    omega
  have hnUpper : n ≤ (⌊t⌋ : ℤ) + 1 := by
    have : n < (⌊t⌋ : ℤ) + 2 := by exact_mod_cast hnUpperReal
    omega
  have hnWindow : n ∈ Finset.Icc ⌊t⌋ (⌊t⌋ + 1) :=
    Finset.mem_Icc.mpr ⟨hnLower, hnUpper⟩
  have hnSymm :
      n = (Int.divModEquiv Q).symm (k, cell) := by
    simp [n, Int.divModEquiv_symm_apply]
  have hpair : (Int.divModEquiv Q) n = (k, cell) := by
    rw [hnSymm, Equiv.apply_symm_apply]
  have hresidue : cmp95PeriodicTranslateResidue Q n = cell := by
    exact congrArg Prod.snd hpair
  exact Finset.mem_image.mpr ⟨n, hnWindow, hresidue⟩

/-- Cartesian product of the four one-dimensional active-cell windows. -/
def cmp95PeriodicTensorActiveCellWindow
    (Q : ℕ) [NeZero Q] (x : Fin 4 → ℝ) : Finset (FinBox 4 Q) :=
  Fintype.piFinset fun i => cmp95PeriodicActiveCellWindow Q (x i)

/-- The four-dimensional source partition has pointwise overlap at most
`2^4 = 16`, derived from the same one-dimensional support geometry. -/
theorem card_cmp95PeriodicTensorActiveCellWindow_le_sixteen
    (Q : ℕ) [NeZero Q] (x : Fin 4 → ℝ) :
    (cmp95PeriodicTensorActiveCellWindow Q x).card ≤ 16 := by
  unfold cmp95PeriodicTensorActiveCellWindow
  rw [Fintype.card_piFinset]
  calc
    ∏ i : Fin 4, (cmp95PeriodicActiveCellWindow Q (x i)).card ≤
        ∏ _i : Fin 4, 2 := by
      refine Finset.prod_le_prod (fun _i _hi => Nat.zero_le _) ?_
      intro i _hi
      exact card_cmp95PeriodicActiveCellWindow_le_two Q (x i)
    _ = 16 := by norm_num

/-- Every nonzero tensor cutoff lies in the derived sixteen-cell window. -/
theorem mem_cmp95PeriodicTensorActiveCellWindow_of_cutoff_ne_zero
    (P : CMP95SourceSmoothPartitionProfile) (Q : ℕ) [NeZero Q]
    (cell : FinBox 4 Q) (x : Fin 4 → ℝ)
    (hcutoff : cmp95PeriodicTensorCutoff P Q cell x ≠ 0) :
    cell ∈ cmp95PeriodicTensorActiveCellWindow Q x := by
  classical
  have hsquare : cmp95PeriodicTensorSquareWeight P Q cell x ≠ 0 := by
    intro hz
    apply hcutoff
    unfold cmp95PeriodicTensorCutoff
    rw [hz, Real.sqrt_zero]
  rw [cmp95PeriodicTensorActiveCellWindow, Fintype.mem_piFinset]
  intro i
  apply mem_cmp95PeriodicActiveCellWindow_of_squareWeight_ne_zero P Q
  intro hcoord
  apply hsquare
  unfold cmp95PeriodicTensorSquareWeight
  exact Finset.prod_eq_zero (Finset.mem_univ i) hcoord

/-- Active source cells for a cutoff evaluated at physical scale `M0`.
The window is not the unscaled window at `x`: it is the same residue window
at the dimensionless coordinate `x / M0`, exactly as in the definition of
`cmp95RescaledPeriodicTensorCutoff`. -/
def cmp95RescaledPeriodicTensorActiveCellWindow
    (Q : ℕ) [NeZero Q] (M0 : ℝ) (x : Fin 4 → ℝ) :
    Finset (FinBox 4 Q) :=
  cmp95PeriodicTensorActiveCellWindow Q (fun i => x i / M0)

/-- Physical rescaling changes the coordinate of the active window but not
its literal four-dimensional overlap bound `2^4 = 16`. -/
theorem card_cmp95RescaledPeriodicTensorActiveCellWindow_le_sixteen
    (Q : ℕ) [NeZero Q] (M0 : ℝ) (x : Fin 4 → ℝ) :
    (cmp95RescaledPeriodicTensorActiveCellWindow Q M0 x).card ≤ 16 := by
  exact card_cmp95PeriodicTensorActiveCellWindow_le_sixteen Q
    (fun i => x i / M0)

/-- A nonzero physically rescaled tensor cutoff lies in the active window at
the normalized coordinate.  This is a definitional transport through the
rescaled cutoff, not an identification with the unscaled window at `x`. -/
theorem mem_cmp95RescaledPeriodicTensorActiveCellWindow_of_cutoff_ne_zero
    (P : CMP95SourceSmoothPartitionProfile) (Q : ℕ) [NeZero Q]
    (M0 : ℝ) (cell : FinBox 4 Q) (x : Fin 4 → ℝ)
    (hcutoff : cmp95RescaledPeriodicTensorCutoff P Q M0 cell x ≠ 0) :
    cell ∈ cmp95RescaledPeriodicTensorActiveCellWindow Q M0 x := by
  unfold cmp95RescaledPeriodicTensorActiveCellWindow
  apply mem_cmp95PeriodicTensorActiveCellWindow_of_cutoff_ne_zero P Q
  change cmp95PeriodicTensorCutoff P Q cell (fun i => x i / M0) ≠ 0
  exact hcutoff

end

end YangMills.RG
