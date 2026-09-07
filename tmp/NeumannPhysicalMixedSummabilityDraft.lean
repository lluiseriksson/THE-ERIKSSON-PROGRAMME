import YangMills.RG.NeumannMixedOwnerTransport
import YangMills.RG.NeumannPhysicalPeriodicSummability

/-!
PRE-VALIDATION: source present; .olean not materialized and compiler result
not verified. Convergence of the actual full two-endpoint Green over the
SAME mixed index, with one branch in FULL directions. All source windows
remain explicit. No uniform B0, inverse, operator interchange or window15.
The flag is an algebraic parameter here; the physical consumer must use
the independently computed actual-carrier flag, not choose a free family.
-/

namespace YangMills.RG
noncomputable section

theorem neumannMixedSourceDifference_injective {d : ℕ}
    (full : Fin d → Bool) (m : Fin d → ℤ) (hm : ∀ i, 0 < m i)
    (n : ∀ i : Fin d, neumannImageIntervalPoint (m i)) (target : Fin d → ℤ) :
    Function.Injective (fun p : (Fin d → ℤ) ×
      (∀ i : Fin d, neumannMixedBranch (full i)) =>
        target - neumannMixedImage full m (fun i => (n i).1) p.1 p.2) := by
  intro p q he
  apply neumannMixedGlobalFixedSource_injective full m hm n
  change neumannMixedFixedSourceImage full m n (neumannMixedGlobalFixedIndexEquiv full p) =
    neumannMixedFixedSourceImage full m n (neumannMixedGlobalFixedIndexEquiv full q)
  rw [neumannMixedImage_pack, neumannMixedImage_pack]
  funext i
  have hi := congrFun he i
  change target i - neumannMixedImage full m (fun i => (n i).1) p.1 p.2 i =
    target i - neumannMixedImage full m (fun i => (n i).1) q.1 q.2 i at hi
  omega

theorem summable_neumannMixedSource_of_decay
    {d : ℕ} {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    {G : (Fin d → ℤ) → (Fin d → ℤ) → E} {B delta : ℝ}
    (C : CMP89FullLatticeGreenDecayCertificate G B delta)
    (full : Fin d → Bool) (m : Fin d → ℤ) (hm : ∀ i, 0 < m i)
    (n : ∀ i : Fin d, neumannImageIntervalPoint (m i)) (target : Fin d → ℤ) :
    Summable (fun p : (Fin d → ℤ) ×
      (∀ i : Fin d, neumannMixedBranch (full i)) =>
        G target (neumannMixedImage full m (fun i => (n i).1) p.1 p.2)) := by
  have hw := (summable_cmp89SignedLatticeL1ExponentialWeight
    (d := d) C.delta0_pos).comp_injective
      (neumannMixedSourceDifference_injective full m hm n target)
  apply Summable.of_norm_bounded (hw.mul_left B)
  intro p
  exact C.bound target (neumannMixedImage full m (fun i => (n i).1) p.1 p.2)

theorem summable_neumannActualFullGreen_mixedSource
    {L j : ℕ} [NeZero L] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hrho : 0 < rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hdenWindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hpairWindow : CMP89Eq249CentralAveragePairComplexWindow rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (full : Fin 4 → Bool) (m : Fin 4 → ℤ) (hm : ∀ i, 0 < m i)
    (n : ∀ i : Fin 4, neumannImageIntervalPoint (m i)) (target : Fin 4 → ℤ) :
    Summable (fun p : (Fin 4 → ℤ) ×
      (∀ i : Fin 4, neumannMixedBranch (full i)) =>
        cmp89Eq246NormalizedPhysicalFineToFineGreen L j mass a target
          (neumannMixedImage full m (fun i => (n i).1) p.1 p.2)) := by
  exact summable_neumannMixedSource_of_decay
    (neumannActualFullGreenDecayCertificate
      ha hrho hamplitude hradius hdenWindow hpairWindow hmass)
    full m hm n target

end
end YangMills.RG

#print axioms YangMills.RG.neumannMixedSourceDifference_injective
#print axioms YangMills.RG.summable_neumannMixedSource_of_decay
#print axioms YangMills.RG.summable_neumannActualFullGreen_mixedSource

