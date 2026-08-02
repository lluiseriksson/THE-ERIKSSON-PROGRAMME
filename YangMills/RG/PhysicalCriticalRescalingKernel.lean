/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.PhysicalShellLocalityQ
import YangMills.RG.PhysicalCriticalRescalingCTAudit

/-!
# Critical-scale kernel bound for the rescaled block Gram operator

The earlier shell-locality proof counted the probe samples exactly but dropped
the factor `L^{-d}` before its final estimate, retaining only the crude bound
`‖Q δ_p v‖ ≤ L ‖v‖`.  Here the normalization is preserved throughout:

`‖Q δ_p v‖ ≤ L^{-d} L ‖v‖`.

In dimension four, multiplying the block map by the critical factor `L` gives

`‖(LQ) δ_p v‖ ≤ L^{-2} ‖v‖`.

The Gram calculus therefore yields the actual entrywise kernel bound
`M_L = L^{-4}` for `(LQ)†(LQ)`, closing the first operator input of the
scale-adapted CT audit.  The range remains `3L` in the fine metric.
-/

namespace YangMills.RG

open scoped RealInnerProductSpace

variable {d L N' Nc : ℕ} [NeZero L] [NeZero N'] [NeZero d] [NeZero Nc]

/-- Critical-scale single-probe bound retaining the exact `L^{-d}`
normalization. -/
theorem flatBlockConstraint_single_norm_le_criticalScale
    (p : PhysicalBond d (L * N')) (v : SUNLieCoord Nc) :
    ‖flatBlockConstraintQCLM (d := d) (Nc := Nc) L N'
        (singlePhysicalBondCochain (d := d) (N := L * N') (Nc := Nc) p v)‖ ≤
      ((L : ℝ) ^ d)⁻¹ * (L : ℝ) * ‖v‖ := by
  classical
  have hLpow : (0 : ℝ) < (L : ℝ) ^ d := by
    have hL : (0 : ℝ) < (L : ℝ) := by exact_mod_cast NeZero.pos L
    positivity
  have hinv : 0 ≤ ((L : ℝ) ^ d)⁻¹ := (inv_pos.mpr hLpow).le
  have hbond : ∀ b : PhysicalBond d N',
      ‖flatBlockConstraintQCLM (d := d) (Nc := Nc) L N'
          (singlePhysicalBondCochain (d := d) (N := L * N') (Nc := Nc) p v) b‖
        ≤ ((L : ℝ) ^ d)⁻¹ *
          ∑ x ∈ blockOf L N' b.1, ∑ k ∈ Finset.range L,
            (if (((fun z => FinBox.shift z b.2)^[k] x, b.2) :
                PhysicalBond d (L * N')) = p then ‖v‖ else 0) := by
    intro b
    rw [flatBlockConstraint_single_apply, norm_smul]
    have habs : ‖((L : ℝ) ^ d)⁻¹‖ = ((L : ℝ) ^ d)⁻¹ := by
      rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hLpow)]
    rw [habs]
    apply mul_le_mul_of_nonneg_left _ hinv
    calc
      ‖∑ x ∈ blockOf L N' b.1, ∑ k ∈ Finset.range L,
          (if (((fun z => FinBox.shift z b.2)^[k] x, b.2) :
              PhysicalBond d (L * N')) = p then v else 0)‖
          ≤ ∑ x ∈ blockOf L N' b.1,
              ‖∑ k ∈ Finset.range L,
                (if (((fun z => FinBox.shift z b.2)^[k] x, b.2) :
                    PhysicalBond d (L * N')) = p then v else 0)‖ :=
            norm_sum_le _ _
      _ ≤ ∑ x ∈ blockOf L N' b.1, ∑ k ∈ Finset.range L,
            ‖(if (((fun z => FinBox.shift z b.2)^[k] x, b.2) :
                PhysicalBond d (L * N')) = p then v else 0)‖ :=
          Finset.sum_le_sum (fun x _ => norm_sum_le _ _)
      _ = ∑ x ∈ blockOf L N' b.1, ∑ k ∈ Finset.range L,
            (if (((fun z => FinBox.shift z b.2)^[k] x, b.2) :
                PhysicalBond d (L * N')) = p then ‖v‖ else 0) := by
          refine Finset.sum_congr rfl (fun x _ => ?_)
          refine Finset.sum_congr rfl (fun k _ => ?_)
          split <;> simp_all
  have hglobal :
      (∑ b : PhysicalBond d N',
        ∑ x ∈ blockOf L N' b.1, ∑ k ∈ Finset.range L,
          (if (((fun z => FinBox.shift z b.2)^[k] x, b.2) :
              PhysicalBond d (L * N')) = p then ‖v‖ else 0))
        ≤ (L : ℝ) * ‖v‖ := by
    calc
      (∑ b : PhysicalBond d N',
        ∑ x ∈ blockOf L N' b.1, ∑ k ∈ Finset.range L,
          (if (((fun z => FinBox.shift z b.2)^[k] x, b.2) :
              PhysicalBond d (L * N')) = p then ‖v‖ else 0))
          = ∑ c : FinBox d N', ∑ μ : Fin d,
              ∑ x ∈ blockOf L N' c, ∑ k ∈ Finset.range L,
                (if (((fun z => FinBox.shift z μ)^[k] x, μ) :
                    PhysicalBond d (L * N')) = p then ‖v‖ else 0) :=
            Fintype.sum_prod_type _
      _ = ∑ μ : Fin d, ∑ c : FinBox d N',
            ∑ x ∈ blockOf L N' c, ∑ k ∈ Finset.range L,
              (if (((fun z => FinBox.shift z μ)^[k] x, μ) :
                  PhysicalBond d (L * N')) = p then ‖v‖ else 0) :=
          Finset.sum_comm
      _ = ∑ μ : Fin d, ∑ k ∈ Finset.range L,
            ∑ x : FinBox d (L * N'),
              (if (((fun z => FinBox.shift z μ)^[k] x, μ) :
                  PhysicalBond d (L * N')) = p then ‖v‖ else 0) := by
          refine Finset.sum_congr rfl (fun μ _ => ?_)
          rw [sum_blocks_eq_sum_sites
            (F := fun x => ∑ k ∈ Finset.range L,
              (if (((fun z => FinBox.shift z μ)^[k] x, μ) :
                  PhysicalBond d (L * N')) = p then ‖v‖ else 0))]
          exact Finset.sum_comm
      _ ≤ ∑ μ : Fin d, ∑ k ∈ Finset.range L,
            (if μ = p.2 then ‖v‖ else 0) := by
          refine Finset.sum_le_sum (fun μ _ => ?_)
          refine Finset.sum_le_sum (fun k _ => ?_)
          by_cases hμ : μ = p.2
          · rw [if_pos hμ]
            have hbij : Function.Bijective
                (fun x : FinBox d (L * N') =>
                  (fun z => FinBox.shift z μ)^[k] x) :=
              Function.Bijective.iterate (FinBox.shift_bijective μ) k
            calc
              ∑ x : FinBox d (L * N'),
                  (if (((fun z => FinBox.shift z μ)^[k] x, μ) :
                      PhysicalBond d (L * N')) = p then ‖v‖ else 0)
                  ≤ ∑ x : FinBox d (L * N'),
                    (if (fun z => FinBox.shift z μ)^[k] x = p.1
                      then ‖v‖ else 0) := by
                    refine Finset.sum_le_sum (fun x _ => ?_)
                    split
                    · rename_i h
                      rw [if_pos (congrArg Prod.fst h)]
                    · split <;> positivity
              _ = ∑ y : FinBox d (L * N'),
                    (if y = p.1 then ‖v‖ else 0) :=
                  hbij.sum_comp (fun y => if y = p.1 then ‖v‖ else 0)
              _ = ‖v‖ := by
                  rw [Finset.sum_ite_eq' Finset.univ p.1,
                    if_pos (Finset.mem_univ _)]
          · rw [if_neg hμ]
            apply le_of_eq
            apply Finset.sum_eq_zero
            intro x _
            rw [if_neg]
            intro h
            exact hμ (congrArg Prod.snd h)
      _ = (L : ℝ) * ‖v‖ := by
          rw [Finset.sum_comm]
          have hinner : ∀ k ∈ Finset.range L,
              ∑ μ : Fin d, (if μ = p.2 then ‖v‖ else 0) = ‖v‖ := by
            intro k _
            rw [Finset.sum_ite_eq' Finset.univ p.2,
              if_pos (Finset.mem_univ _)]
          rw [Finset.sum_congr rfl hinner, Finset.sum_const,
            Finset.card_range, nsmul_eq_mul]
  calc
    ‖flatBlockConstraintQCLM (d := d) (Nc := Nc) L N'
        (singlePhysicalBondCochain (d := d) (N := L * N') (Nc := Nc) p v)‖
        ≤ ∑ b : PhysicalBond d N',
            ‖flatBlockConstraintQCLM (d := d) (Nc := Nc) L N'
              (singlePhysicalBondCochain
                (d := d) (N := L * N') (Nc := Nc) p v) b‖ :=
          piLp_norm_le_sum_norm _
    _ ≤ ∑ b : PhysicalBond d N',
          ((L : ℝ) ^ d)⁻¹ *
            ∑ x ∈ blockOf L N' b.1, ∑ k ∈ Finset.range L,
              (if (((fun z => FinBox.shift z b.2)^[k] x, b.2) :
                  PhysicalBond d (L * N')) = p then ‖v‖ else 0) :=
        Finset.sum_le_sum (fun b _ => hbond b)
    _ = ((L : ℝ) ^ d)⁻¹ *
          (∑ b : PhysicalBond d N',
            ∑ x ∈ blockOf L N' b.1, ∑ k ∈ Finset.range L,
              (if (((fun z => FinBox.shift z b.2)^[k] x, b.2) :
                  PhysicalBond d (L * N')) = p then ‖v‖ else 0)) := by
        rw [Finset.mul_sum]
    _ ≤ ((L : ℝ) ^ d)⁻¹ * ((L : ℝ) * ‖v‖) :=
        mul_le_mul_of_nonneg_left hglobal hinv
    _ = ((L : ℝ) ^ d)⁻¹ * (L : ℝ) * ‖v‖ := by ring

/-- At critical scaling in dimension four, a single probe has amplitude
`L^{-2}`. -/
theorem criticalScaledBlockConstraint_single_norm_le
    (p : PhysicalBond 4 (L * N')) (v : SUNLieCoord Nc) :
    ‖scaledFlatBlockConstraintQCLM (d := 4) (Nc := Nc) (L : ℝ)
        (singlePhysicalBondCochain (d := 4) (N := L * N') (Nc := Nc) p v)‖ ≤
      ((L : ℝ) ^ 2)⁻¹ * ‖v‖ := by
  have hL : (0 : ℝ) < (L : ℝ) := by exact_mod_cast NeZero.pos L
  rw [scaledFlatBlockConstraintQCLM, ContinuousLinearMap.smul_apply, norm_smul,
    Real.norm_of_nonneg hL.le]
  calc
    (L : ℝ) *
        ‖flatBlockConstraintQCLM (d := 4) (Nc := Nc) L N'
          (singlePhysicalBondCochain (d := 4) (N := L * N') (Nc := Nc) p v)‖
        ≤ (L : ℝ) * (((L : ℝ) ^ 4)⁻¹ * (L : ℝ) * ‖v‖) :=
          mul_le_mul_of_nonneg_left
            (flatBlockConstraint_single_norm_le_criticalScale p v) hL.le
    _ = ((L : ℝ) ^ 2)⁻¹ * ‖v‖ := by
          field_simp

/-- **Critical-scale operator input.**  The critically rescaled
four-dimensional Gram term has entrywise kernel amplitude `L^{-4}`. -/
theorem criticalScaledBlockGram_kernelBound :
    PhysicalCovarianceKernelBound
      ((scaledFlatBlockConstraintQCLM (d := 4) (L := L) (N' := N')
          (Nc := Nc) (L : ℝ)).adjoint.comp
        (scaledFlatBlockConstraintQCLM (d := 4) (L := L) (N' := N')
          (Nc := Nc) (L : ℝ)))
      (fun _ _ => criticalKernelMajorant L) := by
  have h := adjointCompSelf_kernelBound
    (scaledFlatBlockConstraintQCLM (d := 4) (L := L) (N' := N')
      (Nc := Nc) (L : ℝ))
    (fun p v => criticalScaledBlockConstraint_single_norm_le p v)
  intro q p v
  have hp := h q p v
  rw [criticalKernelMajorant]
  convert hp using 1
  field_simp

/-- Critical rescaling does not enlarge the fine-metric range certificate. -/
theorem criticalScaledBlockGram_finiteRange :
    PhysicalCovarianceFiniteRange
      ((scaledFlatBlockConstraintQCLM (d := 4) (L := L) (N' := N')
          (Nc := Nc) (L : ℝ)).adjoint.comp
        (scaledFlatBlockConstraintQCLM (d := 4) (L := L) (N' := N')
          (Nc := Nc) (L : ℝ)))
      physicalBondDist (3 * L) := by
  apply adjointCompSelf_finiteRange
  intro p q v w hfar
  rw [scaledFlatBlockConstraintQCLM, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smul_apply, inner_smul_left, inner_smul_right]
  rw [flatBlockConstraint_gram_orthogonal p q v w hfar]
  simp

end YangMills.RG
