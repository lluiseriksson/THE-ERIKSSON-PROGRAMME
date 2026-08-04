/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.PhysicalPoincareLowModeBlock
import YangMills.RG.PhysicalPoincareCriticalRescaling

/-!
# Critical-rescaling all-mode audit

The critical factor removes the constant-sector scaling obstruction, but it
does not control low Hodge modes that lie in the block-map kernel.  On the
one-site coarse torus and every even fine scale `L = M + M`, a transverse
square mode has exactly zero block average and Hodge Rayleigh quotient `8/L`.
Consequently the current full-space, constant-before-volume critical
Poincare gate is false for `Nc >= 2`.

This is a statement about the combined quadratic form
`K0 + (LQ)^*(LQ)`, not merely about the Gram term.  A positive continuation
must change the domain (sector/quotient) or add a further positive operator,
for example from an interacting Hessian.
-/

namespace YangMills.RG

open Matrix Module

/-- On the one-site coarse torus, a transverse even-period square mode has
exactly zero block average. -/
theorem flatBlockConstraintQCLM_squareMode_one_eq_zero
    {d M Nc : ℕ} [NeZero d] [NeZero M] [NeZero Nc]
    (i j : Fin d) (hij : i ≠ j) (w : SUNLieCoord Nc) :
    flatBlockConstraintQCLM (d := d) (Nc := Nc) (M + M) 1
        (blockScaleSquareModeCochain d M 1 Nc i j w) = 0 := by
  classical
  apply PiLp.ext
  intro b
  change flatBlockConstraintQCLM (d := d) (Nc := Nc) (M + M) 1
      (blockScaleSquareModeCochain d M 1 Nc i j w) b = 0
  rw [flatBlockConstraintQCLM_apply]
  unfold linAvg fineLineSum
  have hblock : blockOf (d := d) (M + M) 1 b.1 = Finset.univ := by
    ext x
    rw [mem_blockOf]
    simp only [Finset.mem_univ, iff_true]
    exact Subsingleton.elim _ _
  rw [hblock]
  by_cases hb : b.2 = i
  · subst i
    let hside := blockScale_side_eq M 1
    let e := finBoxSideCongr (d := d) hside
    have hbj : b.2 ≠ j := hij
    have hshift : ∀ (x : FinBox d ((M + M) * 1)) (k : ℕ),
        e.symm ((fun z => FinBox.shift z b.2)^[k] x) j = e.symm x j := by
      intro x k
      induction k with
      | zero => rfl
      | succ k ih =>
          rw [Function.iterate_succ_apply']
          rw [finBoxSideCongr_symm_shift]
          simpa [FinBox.shift, Ne.symm hbj] using ih
    have hprofile :
        (∑ x : FinBox d ((M + M) * 1),
          squareSign (M * 1) (e.symm x j)) = 0 := by
      have he := e.sum_comp
        (fun x : FinBox d ((M + M) * 1) =>
          squareSign (M * 1) (e.symm x j))
      calc
        (∑ x : FinBox d ((M + M) * 1),
            squareSign (M * 1) (e.symm x j)) =
            ∑ y : FinBox d ((M * 1) + (M * 1)),
              squareSign (M * 1) (y j) := by simpa [e] using he.symm
        _ = 0 := sum_finBox_squareSign d (M * 1) j
    have hsum :
        (∑ x : FinBox d ((M + M) * 1), ∑ k ∈ Finset.range (M + M),
          squareSign (M * 1)
              (e.symm ((fun z => FinBox.shift z b.2)^[k] x) j) • w) = 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_eq_zero
      intro k hk
      rw [Finset.sum_congr rfl (fun x _ => by rw [hshift x k])]
      rw [← Finset.sum_smul, hprofile, zero_smul]
    have hsum' :
        (∑ x : FinBox d ((M + M) * 1), ∑ k ∈ Finset.range (M + M),
          squareSign (M * 1)
              ((finBoxSideCongr (blockScale_side_eq M 1)).symm
                ((fun z => FinBox.shift z b.2)^[k] x) j) • w) = 0 := by
      simpa only [e, hside] using hsum
    simp only [physicalBondOfEdge_mk_true, blockScaleSquareModeCochain,
      physicalOneCochainSideCongr_apply, physicalBondSideCongr_symm_apply,
      squareModeCochain_apply, if_true]
    rw [hsum', smul_zero]
  · simp only [physicalBondOfEdge_mk_true, blockScaleSquareModeCochain,
      physicalOneCochainSideCongr_apply, physicalBondSideCongr_symm_apply,
      squareModeCochain_apply, hb, if_false, Finset.sum_const_zero, smul_zero]

/-- The same exact kernel witness for the critically rescaled map `LQ`. -/
theorem criticalScaledBlockConstraintQCLM_squareMode_one_eq_zero
    {d M Nc : ℕ} [NeZero d] [NeZero M] [NeZero Nc]
    (i j : Fin d) (hij : i ≠ j) (w : SUNLieCoord Nc) :
    scaledFlatBlockConstraintQCLM (d := d) (Nc := Nc)
        (((M + M : ℕ) : ℝ))
        (blockScaleSquareModeCochain d M 1 Nc i j w) = 0 := by
  rw [scaledFlatBlockConstraintQCLM, ContinuousLinearMap.smul_apply,
    flatBlockConstraintQCLM_squareMode_one_eq_zero i j hij w, smul_zero]

/-- **Critical all-mode no-go at one coarse site.**  For `Nc >= 2`, the
current full-space critical Poincare gate is false: even scales carry a
nonzero transverse square mode annihilated by `LQ`, while its Hodge Rayleigh
quotient is `8/L`. -/
theorem volumeUniformCriticalRescaledFlatPoincareGate_one_false
    {Nc : ℕ} [NeZero Nc] (hNc : 2 ≤ Nc) (ρ : SUNAdjointModel Nc) :
    ¬ VolumeUniformCriticalRescaledFlatPoincareGate 1 Nc ρ := by
  rintro ⟨CP, _hCP, hall⟩
  obtain ⟨n, hn⟩ := exists_nat_gt (8 * CP)
  let M := n + 1
  haveI : NeZero M := ⟨by simp [M]⟩
  let k := (M + M) - 1
  have hk : k + 1 = M + M := by
    dsimp [k]
    omega
  have hP :
      ScaledFlatGaugeHodgePoincare 4 (M + M) 1 Nc ρ
        (((M + M : ℕ) : ℝ)) CP := by
    simpa only [hk] using hall k
  have hdim : 0 < Nc ^ 2 - 1 := by
    have h4 : 2 * 2 ≤ Nc * Nc := Nat.mul_le_mul hNc hNc
    have hsq : Nc ^ 2 = Nc * Nc := by ring
    rw [hsq]
    omega
  let w : SUNLieCoord Nc :=
    EuclideanSpace.single (⟨0, hdim⟩ : Fin (Nc ^ 2 - 1)) (1 : ℝ)
  let i : Fin 4 := ⟨0, by omega⟩
  let j : Fin 4 := ⟨1, by omega⟩
  have hij : i ≠ j := by simp [i, j]
  let A : FinePhysicalOneCochain 4 (M + M) 1 Nc :=
    blockScaleSquareModeCochain 4 M 1 Nc i j w
  have hw : ‖w‖ ^ 2 = 1 := by
    dsimp [w]
    rw [EuclideanSpace.norm_single]
    norm_num
  have hnorm : ‖A‖ ^ 2 = (((M + M : ℕ) : ℝ)) ^ 4 := by
    dsimp [A]
    rw [norm_sq_blockScaleSquareModeCochain, hw, mul_one]
    norm_num
  have hH :
      inner ℝ A (flatGaugeHodgeK0CLM 4 ((M + M) * 1) Nc ρ A) =
        8 * (((M + M : ℕ) : ℝ)) ^ 3 := by
    dsimp [A]
    rw [flatGaugeHodgeK0_inner_blockScaleSquareModeCochain, hw, mul_one]
    norm_num
  have hQ :
      scaledFlatBlockConstraintQCLM (d := 4) (Nc := Nc)
        (((M + M : ℕ) : ℝ)) A = 0 := by
    dsimp [A]
    exact criticalScaledBlockConstraintQCLM_squareMode_one_eq_zero i j hij w
  have hmain := hP.2 A
  rw [hQ, norm_zero, zero_pow (by norm_num), add_zero, hH, hnorm] at hmain
  have hL : (0 : ℝ) < ((M + M : ℕ) : ℝ) := by
    positivity
  have hL3 : (0 : ℝ) < ((M + M : ℕ) : ℝ) ^ 3 := pow_pos hL 3
  have hfac :
      ((M + M : ℕ) : ℝ) * ((M + M : ℕ) : ℝ) ^ 3 ≤
        (8 * CP) * ((M + M : ℕ) : ℝ) ^ 3 := by
    convert hmain using 1 <;> ring
  have hupper : ((M + M : ℕ) : ℝ) ≤ 8 * CP :=
    (mul_le_mul_iff_of_pos_right hL3).mp hfac
  have hbig : 8 * CP < ((M + M : ℕ) : ℝ) := by
    dsimp [M]
    push_cast
    linarith
  linarith

end YangMills.RG
