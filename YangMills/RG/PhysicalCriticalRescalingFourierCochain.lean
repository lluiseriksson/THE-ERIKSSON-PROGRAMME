/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.PhysicalCriticalRescalingFourierEnergy

/-!
# Physical Fourier transverse cochain
-/

namespace YangMills.RG

open Matrix Module

/-- A transverse one-cochain carrying the first within-block Fourier phase. -/
noncomputable def blockFourierModeCochain
    (d L N' Nc : ℕ) [NeZero L] [NeZero N'] (hNc : 2 ≤ Nc)
    (i j : Fin d) : FinePhysicalOneCochain d L N' Nc :=
  WithLp.toLp 2 fun b : PhysicalBond d (L * N') =>
    if b.2 = i then blockFourierProfile L N' Nc hNc (b.1 j) else 0

@[simp]
theorem blockFourierModeCochain_apply
    {d L N' Nc : ℕ} [NeZero L] [NeZero N'] (hNc : 2 ≤ Nc)
    (i j : Fin d) (b : PhysicalBond d (L * N')) :
    blockFourierModeCochain d L N' Nc hNc i j b =
      if b.2 = i then blockFourierProfile L N' Nc hNc (b.1 j) else 0 := rfl

theorem norm_sq_blockFourierModeCochain
    (d L N' Nc : ℕ) [NeZero L] [NeZero N'] (hNc : 2 ≤ Nc)
    (i j : Fin d) :
    ‖blockFourierModeCochain d L N' Nc hNc i j‖ ^ 2 =
      (((L * N' : ℕ) : ℝ) ^ d) := by
  classical
  rw [PiLp.norm_sq_eq_of_L2]
  have hterm : ∀ b : PhysicalBond d (L * N'),
      ‖blockFourierModeCochain d L N' Nc hNc i j b‖ ^ 2 =
        if b.2 = i then 1 else 0 := by
    intro b
    rw [blockFourierModeCochain_apply]
    by_cases hb : b.2 = i
    · rw [if_pos hb, if_pos hb, norm_sq_blockFourierProfile]
    · rw [if_neg hb, if_neg hb, norm_zero]
      norm_num
  rw [Finset.sum_congr rfl (fun b _ => hterm b), Fintype.sum_prod_type]
  have hinner : ∀ _x : FinBox d (L * N'),
      (∑ k : Fin d, if k = i then (1 : ℝ) else 0) = 1 :=
    fun _x => (Finset.sum_ite_eq' Finset.univ i (fun _ => (1 : ℝ))).trans
      (if_pos (Finset.mem_univ i))
  rw [Finset.sum_congr rfl (fun x _ => hinner x)]
  rw [Finset.sum_const, Finset.card_univ, card_finBox, nsmul_eq_mul]
  push_cast
  ring

theorem flatBlockConstraintQCLM_blockFourierMode_eq_zero
    {d L N' Nc : ℕ} [NeZero d] [NeZero L] [NeZero N'] [NeZero Nc]
    (hL : 2 ≤ L) (hNc : 2 ≤ Nc)
    (i j : Fin d) (hij : i ≠ j) :
    flatBlockConstraintQCLM (d := d) (Nc := Nc) L N'
        (blockFourierModeCochain d L N' Nc hNc i j) = 0 := by
  classical
  apply PiLp.ext
  intro b
  change flatBlockConstraintQCLM (d := d) (Nc := Nc) L N'
      (blockFourierModeCochain d L N' Nc hNc i j) b = 0
  rw [flatBlockConstraintQCLM_apply]
  unfold linAvg fineLineSum
  by_cases hb : b.2 = i
  · subst i
    have hsum :
        (∑ x ∈ blockOf L N' b.1,
          ∑ k ∈ Finset.range L,
            blockFourierProfile L N' Nc hNc
              (((fun z => FinBox.shift z b.2)^[k] x) j)) = 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_eq_zero
      intro k hk
      rw [Finset.sum_congr rfl (fun x _ => by
        rw [blockFourierProfile_iterate_shift_other hNc x b.2 j hij k])]
      exact sum_blockFourierProfile_block_eq_zero hL hNc b.1 j
    simp only [physicalBondOfEdge_mk_true,
      blockFourierModeCochain_apply, if_true]
    rw [hsum, smul_zero]
  · simp only [physicalBondOfEdge_mk_true,
      blockFourierModeCochain_apply, hb, if_false,
      Finset.sum_const_zero, smul_zero]

theorem criticalScaledBlockConstraintQCLM_blockFourierMode_eq_zero
    {d L N' Nc : ℕ} [NeZero d] [NeZero L] [NeZero N'] [NeZero Nc]
    (hL : 2 ≤ L) (hNc : 2 ≤ Nc)
    (i j : Fin d) (hij : i ≠ j) :
    scaledFlatBlockConstraintQCLM (d := d) (Nc := Nc) (L : ℝ)
        (blockFourierModeCochain d L N' Nc hNc i j) = 0 := by
  rw [scaledFlatBlockConstraintQCLM, ContinuousLinearMap.smul_apply,
    flatBlockConstraintQCLM_blockFourierMode_eq_zero hL hNc i j hij,
    smul_zero]

theorem covariantD1CLM_blockFourierModeCochain_apply
    (d L N' Nc : ℕ) [NeZero d] [NeZero L] [NeZero N'] [NeZero Nc]
    (ρ : SUNAdjointModel Nc) (hNc : 2 ≤ Nc) (i j : Fin d)
    (p : ConcretePlaquette d (L * N')) :
    covariantD1CLM ρ (trivialPhysicalGaugeBackground d (L * N') Nc)
        (blockFourierModeCochain d L N' Nc hNc i j) p =
      if p.dir1 = i then
        blockFourierProfile L N' Nc hNc (p.site j) -
          blockFourierProfile L N' Nc hNc ((p.site.shift p.dir2) j)
      else if p.dir2 = i then
        blockFourierProfile L N' Nc hNc ((p.site.shift p.dir1) j) -
          blockFourierProfile L N' Nc hNc (p.site j)
      else 0 := by
  rw [covariantD1CLM_trivial_apply]
  simp only [blockFourierModeCochain_apply]
  by_cases h1 : p.dir1 = i <;> by_cases h2 : p.dir2 = i
  · exfalso
    have := p.hlt
    omega
  · simp [h1, h2]
  · simp [h1, h2]
  · simp [h1, h2]

theorem gaugeConstraintQCLM_blockFourierModeCochain_apply
    (d L N' Nc : ℕ) [NeZero d] [NeZero L] [NeZero N'] [NeZero Nc]
    (ρ : SUNAdjointModel Nc) (hNc : 2 ≤ Nc) (i j : Fin d)
    (x : FinBox d (L * N')) :
    gaugeConstraintQCLM ρ (trivialPhysicalGaugeBackground d (L * N') Nc)
        (blockFourierModeCochain d L N' Nc hNc i j) x =
      blockFourierProfile L N' Nc hNc (x j) -
        blockFourierProfile L N' Nc hNc ((x.shiftBack i) j) := by
  rw [gaugeConstraintQCLM_trivial_apply]
  have hterm : ∀ k : Fin d,
      (blockFourierModeCochain d L N' Nc hNc i j (x, k) -
        blockFourierModeCochain d L N' Nc hNc i j (x.shiftBack k, k)) =
      if k = i then
        blockFourierProfile L N' Nc hNc (x j) -
          blockFourierProfile L N' Nc hNc ((x.shiftBack i) j)
      else 0 := by
    intro k
    rw [blockFourierModeCochain_apply, blockFourierModeCochain_apply]
    by_cases hk : k = i
    · subst k
      simp
    · simp [hk]
  rw [Finset.sum_congr rfl (fun k _ => hterm k)]
  rw [Finset.sum_ite_eq' Finset.univ i]
  simp only [Finset.mem_univ, if_true]

theorem gaugeConstraintQCLM_blockFourierModeCochain_eq_zero_of_ne
    (d L N' Nc : ℕ) [NeZero d] [NeZero L] [NeZero N'] [NeZero Nc]
    (ρ : SUNAdjointModel Nc) (hNc : 2 ≤ Nc)
    (i j : Fin d) (hij : i ≠ j) :
    gaugeConstraintQCLM ρ (trivialPhysicalGaugeBackground d (L * N') Nc)
        (blockFourierModeCochain d L N' Nc hNc i j) = 0 := by
  apply PiLp.ext
  intro x
  change gaugeConstraintQCLM ρ
      (trivialPhysicalGaugeBackground d (L * N') Nc)
      (blockFourierModeCochain d L N' Nc hNc i j) x = 0
  rw [gaugeConstraintQCLM_blockFourierModeCochain_apply]
  have hcoord : (x.shiftBack i) j = x j := by
    simp [FinBox.shiftBack, Ne.symm hij]
  rw [hcoord, sub_self]

end YangMills.RG
