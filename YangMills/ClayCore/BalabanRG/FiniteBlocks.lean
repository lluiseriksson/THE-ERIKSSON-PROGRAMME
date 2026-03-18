import Mathlib
import YangMills.ClayCore.BalabanRG.BlockSpin

namespace YangMills.ClayCore

open scoped BigOperators

/-!
# FiniteBlocks — Layer 0B: Finite-volume block averaging

Key: corner_mem_block takes explicit hL0 : 0 < L.
Key: blockSpinAvg_eq lemma eliminates the empty-branch once and for all.
-/

variable {d : ℕ} (L : ℤ) (hL : 1 < L)

axiom blockFinset (d : ℕ) (L : ℤ) (hL : 1 < L)
    (corner : LatticeSite d) : Finset (LatticeSite d)

axiom blockFinset_spec (d : ℕ) (L : ℤ) (hL : 1 < L)
    (corner : LatticeSite d) (s : LatticeSite d) :
    s ∈ blockFinset d L hL corner ↔ s ∈ Block d L corner

/-- The corner belongs to its own block. -/
theorem corner_mem_block (corner : LatticeSite d) (hL0 : 0 < L) :
    corner ∈ Block d L corner := by
  show InBlock L corner corner
  intro i
  exact ⟨le_rfl, by linarith⟩

/-- blockFinset is never empty. -/
theorem blockFinset_card_ne_zero (corner : LatticeSite d) :
    (blockFinset d L hL corner).card ≠ 0 := by
  have hL0 : 0 < L := lt_trans Int.zero_lt_one hL
  apply Finset.card_ne_zero.mpr
  exact ⟨corner, (blockFinset_spec d L hL corner corner).mpr
    (corner_mem_block L corner hL0)⟩

noncomputable def blockSpinAvg (corner : LatticeSite d)
    (φ : LatticeSite d → ℝ) : ℝ :=
  let B := blockFinset d L hL corner
  if h : B.card = 0 then 0
  else (B.card : ℝ)⁻¹ * ∑ s ∈ B, φ s

/-- Helper: unwrap blockSpinAvg to its non-trivial branch. -/
theorem blockSpinAvg_eq (corner : LatticeSite d) (φ : LatticeSite d → ℝ) :
    blockSpinAvg L hL corner φ =
      ((blockFinset d L hL corner).card : ℝ)⁻¹ *
        ∑ s ∈ blockFinset d L hL corner, φ s := by
  have hB : (blockFinset d L hL corner).card ≠ 0 :=
    blockFinset_card_ne_zero (L := L) (hL := hL) corner
  simp [blockSpinAvg, hB]

theorem blockSpinAvg_linear (corner : LatticeSite d)
    (φ ψ : LatticeSite d → ℝ) (c : ℝ) :
    blockSpinAvg L hL corner (fun s => φ s + c * ψ s) =
    blockSpinAvg L hL corner φ + c * blockSpinAvg L hL corner ψ := by
  rw [blockSpinAvg_eq, blockSpinAvg_eq, blockSpinAvg_eq]
  set B : Finset (LatticeSite d) := blockFinset d L hL corner
  have hsum : (∑ s ∈ B, (φ s + c * ψ s)) =
      (∑ s ∈ B, φ s) + c * (∑ s ∈ B, ψ s) :=
    calc (∑ s ∈ B, (φ s + c * ψ s))
        = (∑ s ∈ B, φ s) + (∑ s ∈ B, c * ψ s) := Finset.sum_add_distrib
      _ = (∑ s ∈ B, φ s) + c * (∑ s ∈ B, ψ s) := by rw [← Finset.mul_sum]
  simp only [B, hsum]
  ring

theorem blockSpinAvg_const (corner : LatticeSite d) (c : ℝ) :
    blockSpinAvg L hL corner (fun _ => c) = c := by
  rw [blockSpinAvg_eq]
  have hB : ((blockFinset d L hL corner).card : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (blockFinset_card_ne_zero (L := L) (hL := hL) corner)
  simp [Finset.sum_const, nsmul_eq_mul]
  field_simp [hB]

end YangMills.ClayCore
