/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80PropagatorDerivativeUniform
import YangMills.RG.BalabanCMP102Eq80MinimizerTelescoping

/-!
# One uniform equation-(80) bound over all outer Neumann segments

Absolute summability of the physical minimizer layers bounds every
ordered prefix and its next affine segment by the same norm budget.  In
finite dimension, the corresponding arguments of `fderiv V₀` lie in one
compact ball.  This produces one uniform directional-derivative
constant for all outer Neumann lengths, rather than assuming a family
of unrelated constants `C n`.
-/

open scoped RealInnerProductSpace

namespace YangMills.RG

noncomputable section

/-- A summable family of minimizer layers generates one uniform
equation-(80) derivative bound over every ordered outer segment. -/
theorem
    exists_uniform_bound_cmp102Eq80OuterNeumannDirectionalDerivative
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (D D₃ : E → F)
    (V₀ : E → ℝ)
    (term : ℕ → (F →L[ℝ] E))
    (Δπ : E →L[ℝ] E)
    (J A : E)
    (hV₀ : ContDiff ℝ 1 V₀)
    (htermNorm : Summable fun i : ℕ => ‖term i‖) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (n : ℕ) (t : ℝ), t ∈ Set.uIcc (0 : ℝ) 1 →
        cmp102Eq80PropagatorDirectionalDerivativeBound
          D D₃
          (cmp102Eq80MinimizerPartialSum term n + t • term n)
          Δπ J A
          (fderiv ℝ V₀
            (A -
              (cmp102Eq80MinimizerPartialSum term n + t • term n)
                (D A))) ≤ C := by
  let S : ℝ := ∑' i : ℕ, ‖term i‖
  have hS0 : 0 ≤ S := by
    dsimp [S]
    exact tsum_nonneg fun _ => norm_nonneg _
  let radius : ℝ := S * ‖D A‖
  have hradius0 : 0 ≤ radius := mul_nonneg hS0 (norm_nonneg _)
  have hfderivContinuous :
      Continuous fun x : E => ‖fderiv ℝ V₀ x‖ :=
    (hV₀.continuous_fderiv one_ne_zero).norm
  obtain ⟨B, hB⟩ :=
    (isCompact_closedBall A radius).exists_bound_of_continuousOn
      hfderivContinuous.continuousOn
  have hB0 : 0 ≤ B := by
    have hcenter : A ∈ Metric.closedBall A radius :=
      Metric.mem_closedBall_self hradius0
    exact (norm_nonneg _).trans (hB A hcenter)
  let C : ℝ :=
    ‖D₃ A‖ * ‖J‖ +
      ‖A‖ * (‖Δπ‖ * ‖D A‖) +
      S * ‖D A‖ * (‖Δπ‖ * ‖D A‖) +
      B * ‖D A‖
  have hC0 : 0 ≤ C := by
    dsimp [C]
    positivity
  refine ⟨C, hC0, ?_⟩
  intro n t ht
  have htIcc : t ∈ Set.Icc (0 : ℝ) 1 := by
    simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht
  have htAbs : |t| ≤ 1 := by
    rw [abs_of_nonneg htIcc.1]
    exact htIcc.2
  let H : F →L[ℝ] E :=
    cmp102Eq80MinimizerPartialSum term n + t • term n
  have hprefix :
      ‖cmp102Eq80MinimizerPartialSum term n‖ ≤
        ∑ i ∈ Finset.range n, ‖term i‖ := by
    unfold cmp102Eq80MinimizerPartialSum
    exact norm_sum_le _ _
  have hH : ‖H‖ ≤ S := by
    calc
      ‖H‖ ≤
          ‖cmp102Eq80MinimizerPartialSum term n‖ +
            ‖t • term n‖ := norm_add_le _ _
      _ ≤ (∑ i ∈ Finset.range n, ‖term i‖) + ‖term n‖ := by
        apply add_le_add hprefix
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_of_le_one_left (norm_nonneg _) htAbs
      _ = ∑ i ∈ Finset.range (n + 1), ‖term i‖ := by
        rw [Finset.sum_range_succ]
      _ ≤ S := by
        exact htermNorm.sum_le_tsum (Finset.range (n + 1))
          (fun _ _ => norm_nonneg _)
  have hx :
      A - H (D A) ∈ Metric.closedBall A radius := by
    rw [Metric.mem_closedBall]
    have hdist : dist (A - H (D A)) A = ‖H (D A)‖ := by
      rw [dist_eq_norm]
      have heq : (A - H (D A)) - A = -H (D A) := by abel
      rw [heq, norm_neg]
    rw [hdist]
    exact (H.le_opNorm (D A)).trans
      (mul_le_mul_of_nonneg_right hH (norm_nonneg _))
  have hfderivBound :
      ‖fderiv ℝ V₀ (A - H (D A))‖ ≤ B := by
    simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using
      hB (A - H (D A)) hx
  unfold cmp102Eq80PropagatorDirectionalDerivativeBound
  dsimp [H] at hH hfderivBound ⊢
  dsimp [C]
  gcongr

end

end YangMills.RG
