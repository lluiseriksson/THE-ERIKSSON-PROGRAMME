/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP95PeriodicSquareSlope
import YangMills.RG.BalabanCMP95SourceSmoothPartitionSecondDifference

/-!
# PRE-VALIDATION: sign-preserving periodic CMP95 cutoff

The source is present, but this module's `.olean` has not yet been materialized
and its declarations have not yet been verified by the Lean compiler.

CMP95 (1.118) prints the cutoff as the literal real profile `h`, not as the
square root of a periodized square weight.  This module periodizes `h`
linearly.  When the period contains at least two source cells, the printed
support interval `(-2/3,2/3)` makes distinct translates in one residue class
disjoint, so the square of the signed periodization is exactly the already
sealed residue-class square weight.  The one-cell torus is represented by the
explicit constant cutoff `1`; it is not hidden behind a `Q >= 2` hypothesis.

This module establishes only the exact periodic dictionary and square
partition.  Transport of the quadratic second-difference estimate, the tensor
cutoff-Laplacian bound, and the second species of CMP99 (3.89) remain separate
obligations.
-/

namespace YangMills.RG

noncomputable section

/-- Linear, sign-preserving periodization of the literal CMP95 source profile
inside one residue class. -/
def cmp95PeriodicSignedCutoff
    (P : CMP95SourceSmoothPartitionProfile) (Q : ℕ) [NeZero Q]
    (cell : Fin Q) (t : ℝ) : ℝ :=
  ∑' k : ℤ, P.value
    (t - ((k * (Q : ℤ) + (cell.val : ℤ) : ℤ) : ℝ))

/-- The signed periodization is literally finite at every point, with the
same two-point active window as the square weight. -/
theorem cmp95PeriodicSignedCutoff_eq_sum_activeWindow
    (P : CMP95SourceSmoothPartitionProfile) (Q : ℕ) [NeZero Q]
    (cell : Fin Q) (t : ℝ) :
    cmp95PeriodicSignedCutoff P Q cell t =
      ∑ k ∈ cmp95PeriodicActiveWindow Q cell t,
        P.value
          (t - ((k * (Q : ℤ) + (cell.val : ℤ) : ℤ) : ℝ)) := by
  unfold cmp95PeriodicSignedCutoff
  exact tsum_eq_sum fun k hk => by
    by_contra hne
    exact hk (mem_cmp95PeriodicActiveWindow_of_ne_zero P Q cell t k
      (pow_ne_zero 2 hne))

/-- One full source period leaves the signed residue-class cutoff unchanged. -/
theorem cmp95PeriodicSignedCutoff_add_period
    (P : CMP95SourceSmoothPartitionProfile) (Q : ℕ) [NeZero Q]
    (cell : Fin Q) (t : ℝ) :
    cmp95PeriodicSignedCutoff P Q cell (t + Q) =
      cmp95PeriodicSignedCutoff P Q cell t := by
  unfold cmp95PeriodicSignedCutoff
  rw [← (Equiv.addRight (1 : ℤ)).tsum_eq]
  apply tsum_congr
  intro k
  simp only [Equiv.coe_addRight]
  congr 1
  push_cast
  ring

/-- The two-point active window is the literal pair consisting of its lower
integer endpoint and its successor. -/
theorem cmp95PeriodicActiveWindow_eq_pair
    (Q : ℕ) [NeZero Q] (cell : Fin Q) (t : ℝ) :
    cmp95PeriodicActiveWindow Q cell t =
      {⌊(t - cell.val) / Q⌋, ⌊(t - cell.val) / Q⌋ + 1} := by
  ext k
  simp [cmp95PeriodicActiveWindow]
  omega

/-- Adjacent translates in one residue class cannot both meet the printed
support when the period has at least two source cells. -/
theorem cmp95PeriodicTranslate_mul_next_eq_zero
    (P : CMP95SourceSmoothPartitionProfile) (Q : ℕ) [NeZero Q]
    (hQ : 2 ≤ Q) (cell : Fin Q) (t : ℝ) (k : ℤ) :
    P.value (t - ((k * (Q : ℤ) + (cell.val : ℤ) : ℤ) : ℝ)) *
        P.value
          (t - (((k + 1) * (Q : ℤ) + (cell.val : ℤ) : ℤ) : ℝ)) = 0 := by
  by_cases hk : P.value
      (t - ((k * (Q : ℤ) + (cell.val : ℤ) : ℤ) : ℝ)) = 0
  · apply mul_eq_zero.mpr
    left
    convert hk using 1 <;> push_cast
  by_cases hk1 : P.value
      (t - (((k + 1) * (Q : ℤ) + (cell.val : ℤ) : ℤ) : ℝ)) = 0
  · apply mul_eq_zero.mpr
    right
    convert hk1 using 1 <;> push_cast
  have hsupp := P.support_subset (Function.mem_support.mpr hk)
  have hsupp1 := P.support_subset (Function.mem_support.mpr hk1)
  have hQreal : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hsep :
      t - (((k + 1) * (Q : ℤ) + (cell.val : ℤ) : ℤ) : ℝ) =
        (t - ((k * (Q : ℤ) + (cell.val : ℤ) : ℤ) : ℝ)) - Q := by
    push_cast
    ring
  rw [hsep] at hsupp1
  rcases hsupp with ⟨hkLower, hkUpper⟩
  rcases hsupp1 with ⟨hk1Lower, hk1Upper⟩
  exfalso
  nlinarith

/-- For periods with at least two cells, linear periodization is squarefree
inside each residue class: its square is exactly the sealed square weight. -/
theorem cmp95PeriodicSignedCutoff_sq
    (P : CMP95SourceSmoothPartitionProfile) (Q : ℕ) [NeZero Q]
    (hQ : 2 ≤ Q) (cell : Fin Q) (t : ℝ) :
    cmp95PeriodicSignedCutoff P Q cell t ^ 2 =
      cmp95PeriodicSquareWeight P Q cell t := by
  rw [cmp95PeriodicSignedCutoff_eq_sum_activeWindow,
    cmp95PeriodicSquareWeight_eq_sum_activeWindow]
  let n : ℤ := ⌊(t - cell.val) / Q⌋
  have hwindow : cmp95PeriodicActiveWindow Q cell t = {n, n + 1} := by
    simpa [n] using cmp95PeriodicActiveWindow_eq_pair Q cell t
  rw [hwindow]
  have hn : n ≠ n + 1 := by omega
  have hnmem : n ∉ {n + 1} := by simpa using hn
  simp only [Finset.sum_insert hnmem, Finset.sum_singleton]
  have hcross := cmp95PeriodicTranslate_mul_next_eq_zero
    P Q hQ cell t n
  nlinarith

/-- On the one-cell torus the unique residue-class square weight is one. -/
theorem cmp95PeriodicSquareWeight_eq_one_of_eq_one
    (P : CMP95SourceSmoothPartitionProfile) (Q : ℕ) [NeZero Q]
    (hQ : Q = 1) (cell : Fin Q) (t : ℝ) :
    cmp95PeriodicSquareWeight P Q cell t = 1 := by
  subst Q
  have hcell : cell = 0 := Subsingleton.elim _ _
  subst cell
  unfold cmp95PeriodicSquareWeight
  simpa using P.square_tsum t

/-- Source-faithful periodic cutoff with an explicit one-cell branch.  For
`Q >= 2` it is the signed linear periodization; for `Q = 1` it is the unique
constant partition cutoff. -/
def cmp95SourcePeriodicSignedCutoff
    (P : CMP95SourceSmoothPartitionProfile) (Q : ℕ) [NeZero Q]
    (cell : Fin Q) (t : ℝ) : ℝ :=
  if Q = 1 then 1 else cmp95PeriodicSignedCutoff P Q cell t

/-- The explicit one-cell branch and the disjoint-support branch have the
same square: the sealed periodic residue-class weight. -/
theorem cmp95SourcePeriodicSignedCutoff_sq
    (P : CMP95SourceSmoothPartitionProfile) (Q : ℕ) [NeZero Q]
    (cell : Fin Q) (t : ℝ) :
    cmp95SourcePeriodicSignedCutoff P Q cell t ^ 2 =
      cmp95PeriodicSquareWeight P Q cell t := by
  by_cases hQ1 : Q = 1
  · rw [cmp95PeriodicSquareWeight_eq_one_of_eq_one P Q hQ1 cell t]
    simp [cmp95SourcePeriodicSignedCutoff, hQ1]
  · have hQ2 : 2 ≤ Q := by
      have hQpos : 1 ≤ Q := NeZero.one_le
      omega
    simp only [cmp95SourcePeriodicSignedCutoff, hQ1, if_false]
    exact cmp95PeriodicSignedCutoff_sq P Q hQ2 cell t

/-- Tensor product of the source-faithful one-dimensional periodic cutoffs. -/
def cmp95SourcePeriodicSignedTensorCutoff
    (P : CMP95SourceSmoothPartitionProfile) (Q : ℕ) [NeZero Q]
    (cell : Fin 4 → Fin Q) (x : Fin 4 → ℝ) : ℝ :=
  ∏ i, cmp95SourcePeriodicSignedCutoff P Q (cell i) (x i)

/-- Squaring the signed tensor cutoff recovers the previously sealed tensor
square weight exactly. -/
theorem cmp95SourcePeriodicSignedTensorCutoff_sq
    (P : CMP95SourceSmoothPartitionProfile) (Q : ℕ) [NeZero Q]
    (cell : Fin 4 → Fin Q) (x : Fin 4 → ℝ) :
    cmp95SourcePeriodicSignedTensorCutoff P Q cell x ^ 2 =
      cmp95PeriodicTensorSquareWeight P Q cell x := by
  unfold cmp95SourcePeriodicSignedTensorCutoff
  rw [← Finset.prod_pow]
  unfold cmp95PeriodicTensorSquareWeight
  exact Finset.prod_congr rfl fun i _ =>
    cmp95SourcePeriodicSignedCutoff_sq P Q (cell i) (x i)

/-- Exact finite square partition for the source-faithful signed tensor
cutoff, including the explicit one-cell branch. -/
theorem sum_cmp95SourcePeriodicSignedTensorCutoff_sq
    (P : CMP95SourceSmoothPartitionProfile) (Q : ℕ) [NeZero Q]
    (x : Fin 4 → ℝ) :
    ∑ cell : Fin 4 → Fin Q,
      cmp95SourcePeriodicSignedTensorCutoff P Q cell x ^ 2 = 1 := by
  simp_rw [cmp95SourcePeriodicSignedTensorCutoff_sq]
  exact sum_cmp95PeriodicTensorSquareWeight P Q x

end

end YangMills.RG
