import YangMills.RG.ActualVolumeFullTailDensity
import YangMills.RG.PhysicalPoincareSectorQuotient

/-! Actual harmonic-sector observation rank under the original local nonlinear
coercivity and upper-quadratic penalty hypotheses. Constant cochains, zero
energy and derivative injection are derived, without a supplied kernel/rank
certificate. This addresses the small-lattice regime of the mean-budget order
question; it does not formalize the matching Fourier upper construction. -/
namespace YangMills.RG
open Module
open scoped BigOperators RealInnerProductSpace
set_option maxHeartbeats 1600000
variable {d n Nc : ℕ} [NeZero n] [NeZero Nc]

theorem actualConstant_total_energy_zero (rho : SUNAdjointModel Nc)
    (w : PhysicalGradientIndex (d + 2) n → ℝ)
    (v : Fin (d + 2) → SUNLieCoord Nc) :
    inner ℝ (constantSectorLin (d + 2) n Nc v)
      (flatGaugeHodgeK0CLM (d + 2) n Nc rho (constantSectorLin (d + 2) n Nc v)) +
    inner ℝ (constantSectorLin (d + 2) n Nc v)
      (componentwiseWeightedRepairCLM w (constantSectorLin (d + 2) n Nc v)) = 0 := by
  rw [actualTotalStiffness_energy]
  simp [constantSectorLin_apply, constantPhysicalGaugeOneCochain_apply]

section Observation
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
variable (rho : SUNAdjointModel Nc) (w : PhysicalGradientIndex (d + 2) n → ℝ)
variable (C : PhysicalGaugeOneCochain (d + 2) n Nc → F)
variable (L : PhysicalGaugeOneCochain (d + 2) n Nc →L[ℝ] F)
variable (hC : HasFDerivAt C L 0) (hC0 : C 0 = 0)
variable (Phi : F → ℝ) (K delta radius c : ℝ) (hc : 0 < c)
variable (hdelta : 0 < delta) (hradius : 0 < radius)
variable (hPhi : ∀ y, ‖y‖ < delta → Phi y ≤ K * ‖y‖^2)
variable (hlocal : ∀ A : PhysicalGaugeOneCochain (d + 2) n Nc,
  gaugeConstraintQCLM rho (trivialPhysicalGaugeBackground (d + 2) n Nc) A = 0 →
  ‖A‖ < radius → c * ‖A‖^2 ≤
    inner ℝ A (flatGaugeHodgeK0CLM (d + 2) n Nc rho A) +
    inner ℝ A (componentwiseWeightedRepairCLM w A) + Phi (C A))

include rho w C L hC hC0 Phi K delta radius c hc hdelta hradius hPhi hlocal

theorem actualConstant_derivative_injective :
    Function.Injective (L.toLinearMap.comp (constantSectorLin (d + 2) n Nc)) := by
  classical
  let f := L.toLinearMap.comp (constantSectorLin (d + 2) n Nc)
  change Function.Injective f
  intro u v huv
  let A := constantSectorLin (d + 2) n Nc (u - v)
  have hLA : L A = 0 := by
    change f (u - v) = 0
    rw [map_sub, huv, sub_self]
  let S := (gaugeConstraintQCLM rho (trivialPhysicalGaugeBackground (d + 2) n Nc)).ker
  let T := (flatGaugeHodgeK0CLM (d + 2) n Nc rho + componentwiseWeightedRepairCLM w).toLinearMap
  have hAS : A ∈ S := by
    exact gaugeConstraintQCLM_trivial_constantPhysicalGaugeOneCochain rho (u - v)
  have hb := local_derivative_kernel_quadratic_lower S T C L hC hC0 Phi K delta radius c
    hdelta hradius hPhi (by
      intro B hB hnorm
      have hdiv : gaugeConstraintQCLM rho
          (trivialPhysicalGaugeBackground (d + 2) n Nc) B = 0 := hB
      simpa [T, ContinuousLinearMap.add_apply, inner_add_right] using hlocal B hdiv hnorm)
    A hAS hLA
  have hE := actualConstant_total_energy_zero rho w (u - v)
  have hb0 : c * ‖A‖^2 ≤ 0 := by
    simpa [T, A, ContinuousLinearMap.add_apply, inner_add_right, hE] using hb
  have hAz : A = 0 := by
    by_contra hne
    have hp : 0 < c * ‖A‖^2 := mul_pos hc (sq_pos_of_pos (norm_pos_iff.mpr hne))
    linarith
  have hz : u - v = 0 := by
    funext i
    have h := congrArg (fun B : PhysicalGaugeOneCochain (d + 2) n Nc =>
      B ((default : FinBox (d + 2) n), i)) hAz
    simpa [A, constantSectorLin_apply, constantPhysicalGaugeOneCochain_apply] using h
  exact sub_eq_zero.mp hz

theorem actualConstant_observation_rank :
    (d + 2) * (Nc^2 - 1) ≤ finrank ℝ F := by
  have hinj := actualConstant_derivative_injective rho w C L hC hC0 Phi K delta radius c
    hc hdelta hradius hPhi hlocal
  have h := LinearMap.finrank_le_finrank_of_injective hinj
  simpa [SUNLieCoord, Module.finrank_pi] using h
end Observation
end YangMills.RG