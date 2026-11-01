import YangMills.RG.ComponentwiseFlatHodge

/-! Actual concentrated repair and origin-difference restriction.
This is an energy adapter only, not the full mean-budget rank theorem. -/
namespace YangMills.RG
open scoped BigOperators RealInnerProductSpace
variable {d n Nc : ℕ} [NeZero d] [NeZero n] [NeZero Nc]

noncomputable def actualConcentratedWeight (x0 : FinBox d n) (b : ℝ) :
    PhysicalGradientIndex d n → ℝ := by
  classical
  exact fun p => if p.2.1 = x0 then b else 0

noncomputable def actualOriginDifferenceLin (x0 : FinBox d n) :
    PhysicalGaugeOneCochain d n Nc →ₗ[ℝ] (Fin d × Fin d → SUNLieCoord Nc) where
  toFun A p := A (x0.shift p.1, p.2) - A (x0, p.2)
  map_add' := by
    intro A B
    funext p
    change (A _ + B _) - (A _ + B _) = (A _ - A _) + (B _ - B _)
    abel
  map_smul' := by
    intro t A
    funext p
    change t • A _ - t • A _ = t • (A _ - A _)
    exact (smul_sub t _ _).symm

theorem actualConcentrated_weight_nonneg (x0 : FinBox d n) (b : ℝ) (hb : 0 ≤ b) :
    ∀ p, 0 ≤ actualConcentratedWeight x0 b p := by
  classical
  intro p
  simp only [actualConcentratedWeight]
  split <;> positivity

theorem actualConcentrated_repair_energy_zero (x0 : FinBox d n) (b : ℝ)
    (A : PhysicalGaugeOneCochain d n Nc) (hA : actualOriginDifferenceLin x0 A = 0) :
    inner ℝ A (componentwiseWeightedRepairCLM (actualConcentratedWeight x0 b) A) = 0 := by
  classical
  rw [componentwiseWeightedRepair_energy]
  apply Finset.sum_eq_zero
  intro p _
  by_cases hp : p.2.1 = x0
  · have h := congrArg (fun f : Fin d × Fin d → SUNLieCoord Nc => f (p.1, p.2.2)) hA
    change A (x0.shift p.1, p.2.2) - A (x0, p.2.2) = 0 at h
    have hd : A (p.2.1.shift p.1, p.2.2) - A p.2 = 0 := by simpa only [hp] using h
    simp [hd]
  · simp [actualConcentratedWeight, hp]

theorem actualConcentrated_total_energy_on_kernel (rho : SUNAdjointModel Nc)
    (x0 : FinBox d n) (b : ℝ) (A : PhysicalGaugeOneCochain d n Nc)
    (hA : actualOriginDifferenceLin x0 A = 0) :
    inner ℝ A (flatGaugeHodgeK0CLM d n Nc rho A) +
      inner ℝ A (componentwiseWeightedRepairCLM (actualConcentratedWeight x0 b) A) =
      ‖componentwiseFlatGradientCLM A‖^2 := by
  rw [actualConcentrated_repair_energy_zero x0 b A hA, add_zero,
    componentwiseFlatGradient_eq_hodge rho A]
end YangMills.RG
