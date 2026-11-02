import YangMills.RG.ActualConcentratedRepair
import YangMills.RG.LocalizedSignedMeanCounterexample

/-! Actual positive-total budget and reuse of the existing site-gradient map.
Candidate only until ownColab focal reproduction; no rank theorem here. -/
namespace YangMills.RG
open scoped BigOperators RealInnerProductSpace
variable {d n Nc : ℕ} [NeZero d] [NeZero n] [NeZero Nc]

theorem actualOriginDifference_eq_existing_site_gradient (x0 : FinBox d n)
    (A : PhysicalGaugeOneCochain d n Nc) :
    actualOriginDifferenceLin x0 A = WithLp.ofLp (signedSiteGradientCLM x0 A) := rfl

theorem actualConcentrated_repair_energy (x0 : FinBox d n) (b : ℝ)
    (A : PhysicalGaugeOneCochain d n Nc) :
    inner ℝ A (componentwiseWeightedRepairCLM (actualConcentratedWeight x0 b) A) =
      b * ‖signedSiteGradientCLM x0 A‖^2 := by
  classical
  rw [componentwiseWeightedRepair_energy, PiLp.norm_sq_eq_of_L2]
  simp only [actualConcentratedWeight, Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simp [signedSiteGradientCLM, ite_mul]

theorem actualConcentrated_positive_total_sum (x0 : FinBox d n) (b : ℝ)
    (hb : 0 ≤ b) (i j : Fin d) :
    (∑ x : FinBox d n, max (1 + actualConcentratedWeight x0 b (i, (x, j))) 0) =
      (n : ℝ)^d + b := by
  classical
  have hmax (x : FinBox d n) :
      max (1 + actualConcentratedWeight x0 b (i, (x, j))) 0 =
        1 + actualConcentratedWeight x0 b (i, (x, j)) := by
    apply max_eq_left
    have h := actualConcentrated_weight_nonneg x0 b hb (i, (x, j))
    linarith
  simp_rw [hmax]
  simp [Finset.sum_add_distrib, actualConcentratedWeight, card_finBox, nsmul_eq_mul]

theorem actualConcentrated_positive_total_budget (x0 : FinBox d n) (m : ℝ)
    (hm : 1 ≤ m) (i j : Fin d) :
    (∑ x : FinBox d n,
      max (1 + actualConcentratedWeight x0 ((m - 1) * (n : ℝ)^d) (i, (x, j))) 0) =
      (n : ℝ)^d * m := by
  have hb : 0 ≤ (m - 1) * (n : ℝ)^d :=
    mul_nonneg (sub_nonneg.mpr hm) (by positivity)
  rw [actualConcentrated_positive_total_sum x0 _ hb i j]
  ring
end YangMills.RG
