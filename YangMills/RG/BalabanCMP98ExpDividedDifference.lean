/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP98AdBinomial
import Mathlib.Algebra.Ring.GeomSum

/-!
# The exponential derivative as a divided difference

For commuting left and right multiplication operators `L_Y` and `R_Y`,
the ordered derivative of the `n`-th exponential term is the homogeneous
divided difference

`(1/n!) * sum i<n, L_Y^(n-1-i) R_Y^i`.

Multiplication by `ad Y = L_Y - R_Y` telescopes this finite sum to

`(1/n!) * (L_Y^n - R_Y^n)`.

This is the finite bridge between the ordered derivative and the
`g(ad Y)` functional calculus in CMP98 (32).
-/

namespace YangMills.RG

open scoped BigOperators RightActions

noncomputable section

variable {𝔸 : Type*}
variable [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

/-- Each ordered insertion operator is the corresponding product of a left
and a right multiplication power. -/
theorem leftMul_pow_mul_rightMul_pow_apply
    (Y H : 𝔸) (a b : ℕ) :
    ((cmp98LeftMulCLM Y) ^ a * (cmp98RightMulCLM Y) ^ b) H =
      Y ^ a * H * Y ^ b := by
  rw [ContinuousLinearMap.mul_apply,
    cmp98RightMulCLM_pow_apply, cmp98LeftMulCLM_pow_apply]
  rw [mul_assoc]

/-- Operator form of the ordered insertion derivative. -/
theorem expTermFDeriv_eq_leftRightGeom (Y : 𝔸) (n : ℕ) :
    expTermFDeriv Y n =
      ((n.factorial : ℝ)⁻¹) •
        ∑ i ∈ Finset.range n,
          (cmp98LeftMulCLM Y) ^ (n.pred - i) *
            (cmp98RightMulCLM Y) ^ i := by
  unfold expTermFDeriv
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  ext H
  simp [leftMul_pow_mul_rightMul_pow_apply]

/-- The geometric sum may be written in the source ordering even though
Mathlib's telescoping lemma places the right multiplication power first. -/
theorem leftRightGeom_eq_rightLeftGeom (Y : 𝔸) (n : ℕ) :
    (∑ i ∈ Finset.range n,
        (cmp98LeftMulCLM Y) ^ (n.pred - i) *
          (cmp98RightMulCLM Y) ^ i) =
      ∑ i ∈ Finset.range n,
        (cmp98RightMulCLM Y) ^ i *
          (cmp98LeftMulCLM Y) ^ (n.pred - i) := by
  apply Finset.sum_congr rfl
  intro i hi
  exact ((cmp98LeftMulCLM_commute_rightMulCLM Y).pow_pow _ _).eq

/-- Finite divided-difference identity for every exponential term. -/
theorem cmp98AdCLM_mul_expTermFDeriv (Y : 𝔸) (n : ℕ) :
    cmp98AdCLM Y * expTermFDeriv Y n =
      ((n.factorial : ℝ)⁻¹) •
        ((cmp98LeftMulCLM Y) ^ n - (cmp98RightMulCLM Y) ^ n) := by
  rw [expTermFDeriv_eq_leftRightGeom,
    leftRightGeom_eq_rightLeftGeom]
  ext H
  simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.smul_apply,
    map_smul]
  have hgeom :=
    (cmp98LeftMulCLM_commute_rightMulCLM Y).symm.mul_neg_geom_sum₂ n
  have happ := congrArg (fun T : 𝔸 →L[ℝ] 𝔸 => T H) hgeom
  rw [cmp98AdCLM_eq_left_sub_right]
  exact congrArg (fun z : 𝔸 => ((n.factorial : ℝ)⁻¹) • z) happ

/-- Pointwise telescoping identity. -/
theorem cmp98AdCLM_expTermFDeriv_apply (Y H : 𝔸) (n : ℕ) :
    cmp98AdCLM Y (expTermFDeriv Y n H) =
      ((n.factorial : ℝ)⁻¹) • (Y ^ n * H - H * Y ^ n) := by
  have h := congrArg (fun T : 𝔸 →L[ℝ] 𝔸 => T H)
    (cmp98AdCLM_mul_expTermFDeriv Y n)
  dsimp only at h
  rw [ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sub_apply,
    cmp98LeftMulCLM_pow_apply,
    cmp98RightMulCLM_pow_apply] at h
  simpa [ContinuousLinearMap.mul_apply] using h

end

end YangMills.RG
