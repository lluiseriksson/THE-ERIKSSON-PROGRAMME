import YangMills.RG.TorusMeanPoincare
import YangMills.RG.TorusPhysicalShift
import YangMills.RG.ComponentwiseFlatGradient

/-! Actual physical quadratic-scale gradient repair and fixed directional mean.
The safe factor2 avoids needing an optimal or orthogonal decomposition. -/
namespace YangMills.RG
open scoped BigOperators RealInnerProductSpace

section Sites
variable {d n : ℕ} [NeZero n] {V : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V]

noncomputable def finBoxArithmeticMean (f : FinBox d n → V) : V :=
  ((n : ℝ) ^ d)⁻¹ • ∑ x, f x

theorem finBoxMean_poincare_energy_le (f : FinBox d n → V) :
    (∑ x, ‖f x - finBoxArithmeticMean f‖ ^ 2) ≤
      (d : ℝ) * (n : ℝ) ^ 2 * ∑ i : Fin d, ∑ x, ‖f (x.shift i) - f x‖ ^ 2 := by
  classical
  let e := finBoxZModEquiv d n
  let g : PeriodicL2 (Fin d → ZMod n) V := WithLp.toLp 2 (fun y => f (e.symm y))
  have hm : finiteArithmeticMean g = finBoxArithmeticMean f := by
    unfold finiteArithmeticMean finBoxArithmeticMean
    have hc : Fintype.card (Fin d → ZMod n) = n ^ d := by simp
    rw [hc]
    congr 1
    exact Equiv.sum_comp e.symm f
  have hl : (∑ y : Fin d → ZMod n, ‖g y - finiteArithmeticMean g‖ ^ 2) =
      ∑ x, ‖f x - finBoxArithmeticMean f‖ ^ 2 := by
    rw [hm]
    have he := Equiv.sum_comp e (fun y => ‖g y - finBoxArithmeticMean f‖ ^ 2)
    simpa [g] using he.symm
  have hr (i : Fin d) : (∑ y : Fin d → ZMod n, ‖g (y + torusUnit i) - g y‖ ^ 2) =
      ∑ x, ‖f (x.shift i) - f x‖ ^ 2 := by
    have hshift (x : FinBox d n) : e.symm (e x + torusUnit i) = x.shift i := by
      apply e.injective
      rw [Equiv.apply_symm_apply]
      exact (finBoxZModEquiv_shift x i).symm
    calc
      _ = ∑ x : FinBox d n, ‖g (e x + torusUnit i) - g (e x)‖ ^ 2 :=
        (Equiv.sum_comp e _).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro x _
        simp only [g, WithLp.toLp_apply, hshift, Equiv.symm_apply_apply]
  have h := torusMean_poincare_energy_le g
  rw [hl] at h
  simpa only [hr] using h
end Sites

abbrev PhysicalDirectionalMean (d Nc : ℕ) := PiLp 2 (fun _ : Fin d => SUNLieCoord Nc)

section Physical
variable {d n Nc : ℕ} [NeZero d] [NeZero n] [NeZero Nc]

noncomputable def physicalDirectionalMean (A : PhysicalGaugeOneCochain d n Nc) :
    PhysicalDirectionalMean d Nc :=
  WithLp.toLp 2 (fun j => finBoxArithmeticMean (fun x => A (x, j)))

noncomputable def physicalDirectionalMeanCLM :
    PhysicalGaugeOneCochain d n Nc →L[ℝ] PhysicalDirectionalMean d Nc :=
  LinearMap.toContinuousLinearMap
    { toFun := physicalDirectionalMean
      map_add' := by
        intro A B
        apply PiLp.ext
        intro j
        change ((n : ℝ)^d)⁻¹ • (∑ x, (A (x,j) + B (x,j))) =
          ((n : ℝ)^d)⁻¹ • (∑ x, A (x,j)) + ((n : ℝ)^d)⁻¹ • (∑ x, B (x,j))
        rw [Finset.sum_add_distrib, smul_add]
      map_smul' := by
        intro r A
        apply PiLp.ext
        intro j
        change ((n : ℝ)^d)⁻¹ • (∑ x, r • A (x,j)) =
          r • (((n : ℝ)^d)⁻¹ • ∑ x, A (x,j))
        rw [← Finset.smul_sum, smul_smul, smul_smul, mul_comm] }

theorem physicalDirectionalMean_hasFDerivAt (A : PhysicalGaugeOneCochain d n Nc) :
    HasFDerivAt (physicalDirectionalMeanCLM (d := d) (n := n) (Nc := Nc))
      (physicalDirectionalMeanCLM (d := d) (n := n) (Nc := Nc)) A :=
  (physicalDirectionalMeanCLM (d := d) (n := n) (Nc := Nc)).hasFDerivAt

noncomputable def physicalMeanLift (A : PhysicalGaugeOneCochain d n Nc) :
    PhysicalGaugeOneCochain d n Nc :=
  WithLp.toLp 2 (fun p => physicalDirectionalMean A p.2)

theorem physicalMeanLift_norm_sq (A : PhysicalGaugeOneCochain d n Nc) :
    ‖physicalMeanLift A‖ ^ 2 = (n : ℝ)^d * ‖physicalDirectionalMean A‖ ^ 2 := by
  classical
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2, Fintype.sum_prod_type]
  change (∑ _x : FinBox d n, ∑ j : Fin d, ‖physicalDirectionalMean A j‖ ^ 2) = _
  simp [card_finBox, nsmul_eq_mul]

theorem physicalMean_poincare_energy_le (A : PhysicalGaugeOneCochain d n Nc) :
    ‖A - physicalMeanLift A‖ ^ 2 ≤
      (d : ℝ) * (n : ℝ)^2 * ‖componentwiseFlatGradientCLM A‖ ^ 2 := by
  classical
  have hl : ‖A - physicalMeanLift A‖ ^ 2 =
      ∑ j : Fin d, ∑ x : FinBox d n,
        ‖A (x,j) - finBoxArithmeticMean (fun y => A (y,j))‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, Fintype.sum_prod_type, Finset.sum_comm]
    rfl
  have hr : ‖componentwiseFlatGradientCLM A‖ ^ 2 =
      ∑ j : Fin d, ∑ i : Fin d, ∑ x : FinBox d n, ‖A (x.shift i,j) - A (x,j)‖ ^ 2 := by
    rw [componentwiseFlatGradient_energy]
    simp only [Fintype.sum_prod_type]
    calc
      _ = ∑ i : Fin d, ∑ j : Fin d, ∑ x : FinBox d n,
          ‖A (x.shift i,j) - A (x,j)‖ ^ 2 :=
        Finset.sum_congr rfl (fun i _ => Finset.sum_comm)
      _ = _ := Finset.sum_comm
  rw [hl, hr, Finset.mul_sum]
  exact Finset.sum_le_sum (fun j _ => finBoxMean_poincare_energy_le (fun x => A (x,j)))

def physicalQuadraticMeanPenalty (d n Nc : ℕ) (y : PhysicalDirectionalMean d Nc) : ℝ :=
  (2 * (n : ℝ)^d) * ‖y‖ ^ 2

def physicalQuadraticWeights (p : PhysicalGradientIndex d n) : ℝ :=
  2 * (d : ℝ) * (n : ℝ)^2

theorem physicalQuadraticMean_global_coercive (A : PhysicalGaugeOneCochain d n Nc) :
    ‖A‖ ^ 2 ≤ inner ℝ A (componentwiseWeightedRepairCLM physicalQuadraticWeights A) +
      physicalQuadraticMeanPenalty d n Nc (physicalDirectionalMeanCLM A) := by
  have hp := physicalMean_poincare_energy_le A
  have ht : ‖A‖ ≤ ‖A - physicalMeanLift A‖ + ‖physicalMeanLift A‖ := by
    simpa only [sub_add_cancel] using norm_add_le (A - physicalMeanLift A) (physicalMeanLift A)
  have hs := pow_le_pow_left₀ (norm_nonneg A) ht 2
  have hc := sq_nonneg (‖A - physicalMeanLift A‖ - ‖physicalMeanLift A‖)
  have hb : ‖A‖ ^ 2 ≤ 2 * ‖A - physicalMeanLift A‖ ^ 2 +
      2 * ‖physicalMeanLift A‖ ^ 2 := by nlinarith
  have hw : inner ℝ A (componentwiseWeightedRepairCLM physicalQuadraticWeights A) =
      (2 * (d : ℝ) * (n : ℝ)^2) * ‖componentwiseFlatGradientCLM A‖ ^ 2 := by
    rw [componentwiseWeightedRepair_energy, componentwiseFlatGradient_energy, Finset.mul_sum]
    rfl
  rw [hw]
  change ‖A‖ ^ 2 ≤ (2 * (d : ℝ) * (n : ℝ)^2) * ‖componentwiseFlatGradientCLM A‖ ^ 2 +
    (2 * (n : ℝ)^d) * ‖physicalDirectionalMean A‖ ^ 2
  rw [physicalMeanLift_norm_sq] at hb
  nlinarith

theorem physicalDirectionalMean_output_finite :
    FiniteDimensional ℝ (PhysicalDirectionalMean d Nc) := inferInstance

theorem physicalQuadraticMeanPenalty_exact (y : PhysicalDirectionalMean d Nc) :
    physicalQuadraticMeanPenalty d n Nc y = (2 * (n : ℝ)^d) * ‖y‖ ^ 2 := rfl
end Physical
end YangMills.RG
