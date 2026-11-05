import YangMills.RG.TorusPhysicalShift

/-! First formal part of the analytic unit142 cycle lift.
Actual divergence, injectivity, counting norm and selected normalized fibre
means. Energy transport and the final physical counterexample are NOT claimed
by this module until separately proved. Candidate until Colab/oracle evidence.
-/
namespace YangMills.RG
open scoped BigOperators RealInnerProductSpace
variable {d n Nc : ℕ} [NeZero n] [NeZero Nc]

noncomputable def cycleCoordinateProfile (u : ZMod n → ℝ) :
    (Fin (d + 2) → ZMod n) → ℂ := fun x => (u (x 0) : ℂ)

noncomputable def physicalCycleLift (hNc : 2 ≤ Nc) (u : ZMod n → ℝ) :
    PhysicalGaugeOneCochain (d + 2) n Nc :=
  torusPhysicalEmbed hNc (Fin.succ 0) (cycleCoordinateProfile u)

def cycleCoordinateSplit :
    (Fin (d + 2) → ZMod n) ≃ ZMod n × (Fin (d + 1) → ZMod n) where
  toFun f := (f 0, fun i => f i.succ)
  invFun p := Fin.cases p.1 p.2
  left_inv f := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  right_inv p := by
    rcases p with ⟨a, f⟩
    rfl

theorem physicalCycleLift_divergence_zero (hNc : 2 ≤ Nc)
    (rho : SUNAdjointModel Nc) (u : ZMod n → ℝ) :
    gaugeConstraintQCLM rho (trivialPhysicalGaugeBackground (d + 2) n Nc)
      (physicalCycleLift hNc u) = 0 := by
  ext x i
  rw [physicalCycleLift, torusPhysicalEmbed_flat_div_apply]
  simp [cycleCoordinateProfile, Pi.sub_apply, Pi.single_apply,
    sunComplexPlane, EuclideanSpace.single_apply]

theorem physicalCycleLift_injective (hNc : 2 ≤ Nc) :
    Function.Injective (physicalCycleLift (d := d) (n := n) hNc) := by
  intro u v h
  have hh := torusPhysicalEmbed_injective hNc (Fin.succ 0) h
  funext t
  have ht := congrFun hh (fun _ => t)
  exact Complex.ofReal_injective ht

theorem cycleCoordinateProfile_counting_mass (u : ZMod n → ℝ) :
    countingL2Mass (cycleCoordinateProfile (d := d) u) =
      (n : ℝ) ^ (d + 1) * ∑ t : ZMod n, (u t) ^ 2 := by
  classical
  unfold countingL2Mass cycleCoordinateProfile
  calc
    (∑ x : Fin (d + 2) → ZMod n, ‖(u (x 0) : ℂ)‖ ^ 2) =
        ∑ z : ZMod n × (Fin (d + 1) → ZMod n), ‖(u z.1 : ℂ)‖ ^ 2 := by
      refine Fintype.sum_equiv (cycleCoordinateSplit (d := d) (n := n)) _ _ ?_
      intro x
      rfl
    _ = _ := by
      simp [Fintype.sum_prod_type, Complex.norm_real, Real.norm_eq_abs,
        sq_abs, Fintype.card_fun, ZMod.card, Finset.mul_sum]

theorem physicalCycleLift_norm_sq (hNc : 2 ≤ Nc) (u : ZMod n → ℝ) :
    ‖physicalCycleLift (d := d) hNc u‖ ^ 2 =
      (n : ℝ) ^ (d + 1) * ∑ t : ZMod n, (u t) ^ 2 := by
  rw [physicalCycleLift, torusPhysicalEmbed_norm_sq, cycleCoordinateProfile_counting_mass]

private theorem cycleCoord_zero_lt (hNc : 2 ≤ Nc) : 0 < Nc ^ 2 - 1 := by
  have hs : 4 ≤ Nc ^ 2 := by nlinarith
  omega

noncomputable def actualCycleFibreObservation (hNc : 2 ≤ Nc)
    (I : Finset (ZMod n)) (y : Fin (d + 1) → ZMod n)
    (A : PhysicalGaugeOneCochain (d + 2) n Nc) : ℝ :=
  (∑ t ∈ I, A ((finBoxZModEquiv (d + 2) n).symm (Fin.cases t y), Fin.succ 0)
    ⟨0, cycleCoord_zero_lt hNc⟩) / Real.sqrt (I.card : ℝ)

theorem actualCycleFibreObservation_lift (hNc : 2 ≤ Nc)
    (I : Finset (ZMod n)) (y : Fin (d + 1) → ZMod n) (u : ZMod n → ℝ) :
    actualCycleFibreObservation hNc I y (physicalCycleLift hNc u) =
      (∑ t ∈ I, u t) / Real.sqrt (I.card : ℝ) := by
  classical
  simp [actualCycleFibreObservation, physicalCycleLift, torusPhysicalEmbed,
    cycleCoordinateProfile, sunComplexPlane, EuclideanSpace.single_apply]

end YangMills.RG
