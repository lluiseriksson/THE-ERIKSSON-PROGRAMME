import YangMills.RG.PhysicalQuadraticMeanRepair
import YangMills.RG.PhysicalTransverseCharacterStrip

/-! Explicit localized signed repair. The output type has no lattice-side
parameter. No energy cancellation or zero-mean certificate is assumed. -/
namespace YangMills.RG
open scoped BigOperators RealInnerProductSpace

abbrev SignedSiteGradient (d Nc : ℕ) :=
  PiLp 2 (fun _ : Fin d × Fin d => SUNLieCoord Nc)
abbrev SignedMeanObservation (d Nc : ℕ) :=
  PhysicalDirectionalMean d Nc × SignedSiteGradient d Nc

section Actual
variable {d n Nc : ℕ} [NeZero d] [NeZero n] [NeZero Nc]

noncomputable def signedSiteGradientCLM (o : FinBox d n) :
    PhysicalGaugeOneCochain d n Nc →L[ℝ] SignedSiteGradient d Nc :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => WithLp.toLp 2 (fun p => A (o.shift p.1,p.2) - A (o,p.2))
      map_add' := by
        intro A B
        apply PiLp.ext
        intro p
        change (A _ + B _) - (A _ + B _) = (A _ - A _) + (B _ - B _)
        abel
      map_smul' := by
        intro r A
        apply PiLp.ext
        intro p
        change r • A _ - r • A _ = r • (A _ - A _)
        exact (smul_sub r _ _).symm }

noncomputable def signedMeanObservationCLM (o : FinBox d n) :
    PhysicalGaugeOneCochain d n Nc →L[ℝ] SignedMeanObservation d Nc :=
  (physicalDirectionalMeanCLM (d := d) (n := n) (Nc := Nc)).prod
    (signedSiteGradientCLM o)

noncomputable def localizedSignedWeights (o : FinBox d n)
    (p : PhysicalGradientIndex d n) : ℝ :=
  (2 * (d : ℝ) * (n : ℝ)^2) -
    if p.2.1 = o then (2 * (d : ℝ) * (n : ℝ)^2) * (n : ℝ)^d else 0

theorem localizedSignedWeights_average_zero (o : FinBox d n) (i j : Fin d) :
    physicalDirectionalWeightAverage (localizedSignedWeights o) i j = 0 := by
  classical
  unfold physicalDirectionalWeightAverage localizedSignedWeights
  have hs : (∑ x : FinBox d n,
      ((2 * (d : ℝ) * (n : ℝ)^2) -
        if x = o then (2 * (d : ℝ) * (n : ℝ)^2) * (n : ℝ)^d else 0)) = 0 := by
    rw [Finset.sum_sub_distrib]
    simp [card_finBox, nsmul_eq_mul, mul_comm]
  rw [hs, mul_zero]

theorem localizedSignedWeights_energy (o : FinBox d n)
    (A : PhysicalGaugeOneCochain d n Nc) :
    inner ℝ A (componentwiseWeightedRepairCLM (localizedSignedWeights o) A) =
      (2 * (d : ℝ) * (n : ℝ)^2) * ‖componentwiseFlatGradientCLM A‖^2 -
      ((2 * (d : ℝ) * (n : ℝ)^2) * (n : ℝ)^d) *
        ‖signedSiteGradientCLM o A‖^2 := by
  classical
  rw [componentwiseWeightedRepair_energy, componentwiseFlatGradient_energy]
  simp only [localizedSignedWeights, sub_mul, Finset.sum_sub_distrib,
    ← Finset.mul_sum]
  congr 1
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [Fintype.sum_prod_type]
  simp [signedSiteGradientCLM, ite_mul, Finset.mul_sum,
    Finset.sum_comm, mul_assoc]

noncomputable def localizedSignedPenalty (d n Nc : ℕ)
    (y : SignedMeanObservation d Nc) : ℝ :=
  (2 * (n : ℝ)^d) * ‖y.1‖^2 +
    ((2 * (d : ℝ) * (n : ℝ)^2) * (n : ℝ)^d) * ‖y.2‖^2

theorem localizedSignedPenalty_nonneg (y : SignedMeanObservation d Nc) :
    0 ≤ localizedSignedPenalty d n Nc y := by
  unfold localizedSignedPenalty
  positivity

theorem localizedSignedPenalty_quadratic_upper (y : SignedMeanObservation d Nc) :
    localizedSignedPenalty d n Nc y ≤
      ((n : ℝ)^d * (2 + 2 * (d : ℝ) * (n : ℝ)^2)) * ‖y‖^2 := by
  have hy₁ : ‖y.1‖ ≤ ‖y‖ := le_max_left _ _
  have hy₂ : ‖y.2‖ ≤ ‖y‖ := le_max_right _ _
  have h₁ := pow_le_pow_left₀ (norm_nonneg y.1) hy₁ 2
  have h₂ := pow_le_pow_left₀ (norm_nonneg y.2) hy₂ 2
  have ha : 0 ≤ (2 * (n : ℝ)^d) := by positivity
  have hb : 0 ≤ (2 * (d : ℝ) * (n : ℝ)^2) * (n : ℝ)^d := by positivity
  have h := add_le_add (mul_le_mul_of_nonneg_left h₁ ha)
    (mul_le_mul_of_nonneg_left h₂ hb)
  unfold localizedSignedPenalty
  nlinarith

theorem localizedSignedMean_global_coercive (o : FinBox d n)
    (A : PhysicalGaugeOneCochain d n Nc) :
    ‖A‖^2 ≤ inner ℝ A (componentwiseWeightedRepairCLM (localizedSignedWeights o) A) +
      localizedSignedPenalty d n Nc (signedMeanObservationCLM o A) := by
  have h := physicalQuadraticMean_global_coercive A
  have hw : inner ℝ A (componentwiseWeightedRepairCLM physicalQuadraticWeights A) =
      (2 * (d : ℝ) * (n : ℝ)^2) * ‖componentwiseFlatGradientCLM A‖^2 := by
    rw [componentwiseWeightedRepair_energy, componentwiseFlatGradient_energy,
      Finset.mul_sum]
    rfl
  rw [hw] at h
  rw [localizedSignedWeights_energy]
  change ‖A‖^2 ≤ _ + ((2 * (n : ℝ)^d) * ‖physicalDirectionalMeanCLM A‖^2 +
    ((2 * (d : ℝ) * (n : ℝ)^2) * (n : ℝ)^d) * ‖signedSiteGradientCLM o A‖^2)
  change ‖A‖^2 ≤ _ + (2 * (n : ℝ)^d) * ‖physicalDirectionalMeanCLM A‖^2 at h
  linarith

theorem signedMeanObservation_hasFDerivAt (o : FinBox d n)
    (A : PhysicalGaugeOneCochain d n Nc) :
    HasFDerivAt (signedMeanObservationCLM (Nc := Nc) o)
      (signedMeanObservationCLM o) A := (signedMeanObservationCLM o).hasFDerivAt

theorem signedMeanObservation_zero (o : FinBox d n) :
    signedMeanObservationCLM (Nc := Nc) o 0 = 0 := map_zero _

theorem signedMeanObservation_output_finite :
    FiniteDimensional ℝ (SignedMeanObservation d Nc) := inferInstance

end Actual
end YangMills.RG
