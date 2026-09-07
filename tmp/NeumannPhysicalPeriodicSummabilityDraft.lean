import YangMills.RG.NeumannActualFullGreenReflectionSummability
import YangMills.RG.BalabanCMP89SignedLatticeL1TotalSum
import Mathlib.Tactic.LinearCombination

/-!
# PRE-VALIDATION: one-branch periodic source summability
Source present; .olean not materialized; result not compiler-verified.
The coordinatewise periods are nonzero. No reflection branch is introduced.
The actual full Green certificate retains all source strip/mass windows.
This establishes only convergence, not a scale-uniform norm budget, mixed
coverage, a point-source equation, a regional inverse, B0 or window15.
-/

namespace YangMills.RG
noncomputable section

theorem neumannPeriodicSourceDifference_injective
    {d : ℕ} (x n P : Fin d → ℤ) (hP : ∀ i, P i ≠ 0) :
    Function.Injective (fun k : Fin d → ℤ => x - (fun i => n i + P i * k i)) := by
  intro k l h
  funext i
  have hi := congrFun h i
  change x i - (n i + P i * k i) = x i - (n i + P i * l i) at hi
  have hz : P i * (k i - l i) = 0 := by
    linear_combination -hi
  exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left (hP i))

theorem summable_neumannPeriodicSource_of_decay
    {d : ℕ} {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    {G : (Fin d → ℤ) → (Fin d → ℤ) → E} {B delta : ℝ}
    (C : CMP89FullLatticeGreenDecayCertificate G B delta)
    (x n P : Fin d → ℤ) (hP : ∀ i, P i ≠ 0) :
    Summable (fun k : Fin d → ℤ => G x (fun i => n i + P i * k i)) := by
  have hw := (summable_cmp89SignedLatticeL1ExponentialWeight
    (d := d) C.delta0_pos).comp_injective
      (neumannPeriodicSourceDifference_injective x n P hP)
  apply Summable.of_norm_bounded (hw.mul_left B)
  intro k
  exact C.bound x (fun i => n i + P i * k i)

theorem summable_neumannActualFullGreen_periodicSource
    {L j : ℕ} [NeZero L] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hrho : 0 < rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hdenWindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hpairWindow : CMP89Eq249CentralAveragePairComplexWindow rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (target source period : Fin 4 → ℤ) (hperiod : ∀ i, period i ≠ 0) :
    Summable (fun k : Fin 4 → ℤ =>
      cmp89Eq246NormalizedPhysicalFineToFineGreen L j mass a target
        (fun i => source i + period i * k i)) := by
  exact summable_neumannPeriodicSource_of_decay
    (neumannActualFullGreenDecayCertificate
      ha hrho hamplitude hradius hdenWindow hpairWindow hmass)
    target source period hperiod

end
end YangMills.RG

#print axioms YangMills.RG.neumannPeriodicSourceDifference_injective
#print axioms YangMills.RG.summable_neumannPeriodicSource_of_decay
#print axioms YangMills.RG.summable_neumannActualFullGreen_periodicSource
