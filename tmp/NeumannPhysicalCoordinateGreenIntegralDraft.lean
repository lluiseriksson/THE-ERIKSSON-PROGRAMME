import NeumannPhysicalCoordinateReflectionDomainDraft
import NeumannCoordinateIntegralReflectionDraft
import YangMills.RG.BalabanCMP89Eq246MassUniformPhysicalContour

/-!
# PRE-VALIDATION: literal normalized physical Green coordinate reflection
Source present; .olean not materialized; result not compiler-verified.
Integrability and both solver domains are produced from the existing common
mass-uniform windows. No Green symmetry or integrability is assumed.
The original Brillouin measure and normalization are preserved.
-/

namespace YangMills.RG
open MeasureTheory
noncomputable section

theorem neumannBrillouinMomentum_coordinateReflection (mu : Fin 4)
    (x : Fin 4 → ℝ) :
    (fun k => (cmp89Eq251PhysicalBrillouinParameter
      (neumannIntervalCoordinateReflection mu (2 * Real.pi) x) k : ℂ)) =
    neumannMomentumCoordinateReflection 4 mu
      (fun k => (cmp89Eq251PhysicalBrillouinParameter x k : ℂ)) := by
  funext k
  by_cases h : k = mu
  · subst k
    simp [cmp89Eq251PhysicalBrillouinParameter,
      neumannIntervalCoordinateReflection, neumannMomentumCoordinateReflection] <;> ring
  · simp [cmp89Eq251PhysicalBrillouinParameter,
      neumannIntervalCoordinateReflection, neumannMomentumCoordinateReflection, h]

theorem neumannPhysicalGreen_coordinateReflection_massUniform
    {L j : ℕ} [NeZero L] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hrho : 0 ≤ rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hdenWindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hpairWindow : CMP89Eq249CentralAveragePairComplexWindow rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (mu : Fin 4) (target source : Fin 4 → ℤ) :
    cmp89Eq246NormalizedPhysicalFineToFineGreen L j mass a
      (neumannFineEndpointCoordinateReflection 4 (L ^ j) mu target)
      (neumannFineEndpointCoordinateReflection 4 (L ^ j) mu source) =
    cmp89Eq246NormalizedPhysicalFineToFineGreen L j mass a target source := by
  let F := fun (t s : Fin 4 → ℤ) (x : Fin 4 → ℝ) =>
    cmp89Eq246PhysicalFineToFineGreenIntegrand L j mass a
      (fun k => (cmp89Eq251PhysicalBrillouinParameter x k : ℂ)) t s
  let T := neumannFineEndpointCoordinateReflection 4 (L ^ j) mu
  let R := neumannIntervalCoordinateReflection mu (2 * Real.pi)
  have hi (t s : Fin 4 → ℤ) :
      Integrable (F t s) cmp89Eq249FourDimensionalBrillouinMeasure := by
    simpa only [F, cmp89Eq249FourDimensionalBrillouinMeasure,
      cmp89Eq246PhysicalFineToFineGreenPartialProductIntegrand,
      cmp89Eq251EndpointPartialSignedContourMomentum_zero] using
      integrable_cmp89Eq246PhysicalFineToFineGreenPartialProductIntegrand_massUniform
        (L := L) (j := j) ha hrho hamplitude hradius hdenWindow hpairWindow
        hmass 0 t s
  have htwoPi : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  let S : Set (Fin 4 → ℝ) := Set.univ.pi fun _ => Set.Ioc 0 (2 * Real.pi)
  have hmeasure : cmp89Eq249FourDimensionalBrillouinMeasure =
      (volume : Measure (Fin 4 → ℝ)).restrict S := by
    unfold cmp89Eq249FourDimensionalBrillouinMeasure S
    rw [volume_pi, Measure.restrict_pi_pi]
    simp only [Set.uIoc_of_le htwoPi]
  have hS : MeasurableSet S :=
    MeasurableSet.pi (Set.to_countable Set.univ) fun _ _ => measurableSet_Ioc
  have hmem : ∀ᵐ x ∂cmp89Eq249FourDimensionalBrillouinMeasure, x ∈ S := by
    rw [hmeasure]
    exact ae_restrict_mem hS
  have heq : (fun x => F target source (R x)) =ᵐ[
      cmp89Eq249FourDimensionalBrillouinMeasure] F (T target) (T source) := by
    filter_upwards [hmem] with x hx
    have hp : ∀ k, |cmp89Eq251PhysicalBrillouinParameter x k| ≤ Real.pi := by
      intro k
      have hk := hx k (Set.mem_univ k)
      rw [abs_le]
      dsimp [cmp89Eq251PhysicalBrillouinParameter]
      constructor <;> linarith [hk.1, hk.2]
    have h := neumannPhysicalFineGreenIntegrand_coordinateReflection_massUniform
      (L := L) (j := j) ha hrho hamplitude hradius hdenWindow hpairWindow
      hmass mu (fun k => (cmp89Eq251PhysicalBrillouinParameter x k : ℂ))
      (by simpa only [Complex.ofReal_re] using hp)
      (by intro k; simpa only [Complex.ofReal_im, abs_zero] using hrho)
      (T target) (T source)
    dsimp [F, R]
    rw [neumannBrillouinMomentum_coordinateReflection]
    simpa only [T, neumannFineEndpointCoordinateReflection_involutive] using h
  have hr : Integrable (fun x => F target source (R x))
      cmp89Eq249FourDimensionalBrillouinMeasure :=
    (hi (T target) (T source)).congr heq.symm
  have htransport := neumannIntegral_coordinateReflection mu htwoPi
    (F target source) (hi target source) hr
  have hint : (∫ x, F (T target) (T source) x
      ∂cmp89Eq249FourDimensionalBrillouinMeasure) =
      ∫ x, F target source x ∂cmp89Eq249FourDimensionalBrillouinMeasure := by
    calc
      _ = ∫ x, F target source (R x)
          ∂cmp89Eq249FourDimensionalBrillouinMeasure := integral_congr_ae heq.symm
      _ = _ := htransport
  unfold cmp89Eq246NormalizedPhysicalFineToFineGreen
    cmp89Eq249NormalizedFourDimensionalBrillouinIntegral
  exact congrArg (fun z : ℂ => ((((2 * Real.pi) ^ 4)⁻¹ : ℝ) : ℂ) * z) hint

#print axioms neumannBrillouinMomentum_coordinateReflection
#print axioms neumannPhysicalGreen_coordinateReflection_massUniform

end
end YangMills.RG
