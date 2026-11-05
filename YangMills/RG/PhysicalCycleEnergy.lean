import YangMills.RG.PhysicalCycleLift
import YangMills.RG.ComponentwiseFlatHodge

/-! Actual original weighted-energy and FULL normalized-mean transport.
Candidate until own Colab build and axiom audit. Does not itself assert
an instantiated four-cycle negative-defect endpoint or paired reproduction.
-/
namespace YangMills.RG
open scoped BigOperators RealInnerProductSpace
variable {d n Nc : ℕ} [NeZero n] [NeZero Nc]
set_option maxHeartbeats 1600000

theorem cycleCoordinate_sum (f : ZMod n → ℝ) :
    (∑ x : Fin (d + 2) → ZMod n, f (x 0)) =
      (n : ℝ) ^ (d + 1) * ∑ t : ZMod n, f t := by
  classical
  calc
    _ = ∑ z : ZMod n × (Fin (d + 1) → ZMod n), f z.1 := by
      refine Fintype.sum_equiv (cycleCoordinateSplit (d := d) (n := n)) _ _ ?_
      intro x
      rfl
    _ = _ := by simp [Fintype.sum_prod_type, Fintype.card_fun, ZMod.card, Finset.mul_sum]

theorem physicalCycleLift_gradient_norm_sq (hNc : 2 ≤ Nc) (u : ZMod n → ℝ)
    (x : FinBox (d + 2) n) (i l : Fin (d + 2)) :
    ‖physicalCycleLift hNc u (x.shift i, l) - physicalCycleLift hNc u (x, l)‖ ^ 2 =
      if l = Fin.succ 0 then
        if i = 0 then (u (finBoxZModEquiv (d + 2) n x 0 + 1) -
          u (finBoxZModEquiv (d + 2) n x 0)) ^ 2 else 0
      else 0 := by
  classical
  by_cases hl : l = Fin.succ 0
  · subst l
    simp only [physicalCycleLift, torusPhysicalEmbed, if_pos rfl, PiLp.toLp_apply]
    rw [← sunComplexPlane_sub, sunComplexPlane_norm_sq]
    by_cases hi : i = 0
    · subst i
      simp [cycleCoordinateProfile, finBoxZModEquiv_shift, Pi.add_apply,
        Pi.single_apply, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    · have hs : finBoxZModEquiv (d + 2) n (x.shift i) 0 =
          finBoxZModEquiv (d + 2) n x 0 := by
        simp [finBoxZModEquiv_shift, Pi.add_apply, Pi.single_apply, Ne.symm hi]
      simp [cycleCoordinateProfile, hs, hi]
  · simp [physicalCycleLift, torusPhysicalEmbed, hl]

noncomputable def physicalCycleRepairWeights (alpha : ZMod n → ℝ) :
    PhysicalGradientIndex (d + 2) n → ℝ :=
  fun p => alpha (finBoxZModEquiv (d + 2) n p.2.1 0) - 1

theorem physicalCycleLift_total_energy (hNc : 2 ≤ Nc) (rho : SUNAdjointModel Nc)
    (alpha u : ZMod n → ℝ) :
    inner ℝ (physicalCycleLift (d := d) hNc u)
      (flatGaugeHodgeK0CLM (d + 2) n Nc rho (physicalCycleLift hNc u)) +
    inner ℝ (physicalCycleLift (d := d) hNc u)
      (componentwiseWeightedRepairCLM (physicalCycleRepairWeights alpha)
        (physicalCycleLift hNc u)) =
      (n : ℝ) ^ (d + 1) * ∑ t : ZMod n, alpha t * (u (t + 1) - u t) ^ 2 := by
  classical
  rw [← componentwiseFlatGradient_eq_hodge rho,
    componentwiseFlatGradient_energy, componentwiseWeightedRepair_energy,
    ← Finset.sum_add_distrib]
  have ht (p : PhysicalGradientIndex (d + 2) n) :
      ‖physicalCycleLift hNc u ((p.2.1).shift p.1, p.2.2) - physicalCycleLift hNc u p.2‖ ^ 2 +
      physicalCycleRepairWeights alpha p *
      ‖physicalCycleLift hNc u ((p.2.1).shift p.1, p.2.2) - physicalCycleLift hNc u p.2‖ ^ 2 =
      alpha (finBoxZModEquiv (d + 2) n p.2.1 0) *
      (if p.2.2 = Fin.succ 0 then if p.1 = 0 then
        (u (finBoxZModEquiv (d + 2) n p.2.1 0 + 1) -
          u (finBoxZModEquiv (d + 2) n p.2.1 0)) ^ 2 else 0 else 0) := by
    rw [physicalCycleLift_gradient_norm_sq]
    dsimp [physicalCycleRepairWeights]
    ring
  simp_rw [ht]
  have hsum : (∑ p : PhysicalGradientIndex (d + 2) n,
      alpha (finBoxZModEquiv (d + 2) n p.2.1 0) *
      (if p.2.2 = Fin.succ 0 then if p.1 = 0 then
        (u (finBoxZModEquiv (d + 2) n p.2.1 0 + 1) -
          u (finBoxZModEquiv (d + 2) n p.2.1 0)) ^ 2 else 0 else 0)) =
      ∑ x : FinBox (d + 2) n, alpha (finBoxZModEquiv (d + 2) n x 0) *
        (u (finBoxZModEquiv (d + 2) n x 0 + 1) -
          u (finBoxZModEquiv (d + 2) n x 0)) ^ 2 := by
    simp only [PhysicalGradientIndex, Fintype.sum_prod_type]
    simp_rw [mul_ite, mul_zero]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [hsum]
  calc
    _ = ∑ x : Fin (d + 2) → ZMod n, alpha (x 0) * (u (x 0 + 1) - u (x 0)) ^ 2 := by
      exact Equiv.sum_comp (finBoxZModEquiv (d + 2) n) _
    _ = _ := cycleCoordinate_sum _

noncomputable def cycleInternalZero (hNc : 2 ≤ Nc) : Fin (Nc ^ 2 - 1) :=
  ⟨0, by have hs : 4 ≤ Nc ^ 2 := by nlinarith; omega⟩

theorem physicalCycleLift_fibre_coordinate (hNc : 2 ≤ Nc)
    (u : ZMod n → ℝ) (t : ZMod n) (y : Fin (d + 1) → ZMod n)
    (l : Fin (d + 2)) (k : Fin (Nc ^ 2 - 1)) :
    physicalCycleLift hNc u
      ((finBoxZModEquiv (d + 2) n).symm (Fin.cases t y), l) k =
      if l = Fin.succ 0 then if k = cycleInternalZero hNc then u t else 0 else 0 := by
  classical
  by_cases hl : l = Fin.succ 0
  · subst l
    simp [physicalCycleLift, torusPhysicalEmbed, cycleCoordinateProfile,
      sunComplexPlane, EuclideanSpace.single_apply, cycleInternalZero, Fin.ext_iff]
  · simp [physicalCycleLift, torusPhysicalEmbed, hl]

noncomputable def actualCycleFullObservation {B : Type*} [Fintype B]
    (I : B → Finset (ZMod n)) (A : PhysicalGaugeOneCochain (d + 2) n Nc) :
    EuclideanSpace ℝ ((B × (Fin (d + 1) → ZMod n)) ×
      (Fin (d + 2) × Fin (Nc ^ 2 - 1))) :=
  WithLp.toLp 2 (fun z =>
    (∑ t ∈ I z.1.1, A ((finBoxZModEquiv (d + 2) n).symm
      (Fin.cases t z.1.2), z.2.1) z.2.2) / Real.sqrt ((I z.1.1).card : ℝ))

theorem actualCycleFullObservation_lift_norm_sq {B : Type*} [Fintype B]
    (hNc : 2 ≤ Nc) (I : B → Finset (ZMod n)) (u : ZMod n → ℝ) :
    ‖actualCycleFullObservation I (physicalCycleLift (d := d) hNc u)‖ ^ 2 =
      (n : ℝ) ^ (d + 1) * ∑ b, ((∑ t ∈ I b, u t) / Real.sqrt ((I b).card : ℝ)) ^ 2 := by
  classical
  rw [PiLp.norm_sq_eq_of_L2]
  have hp (z : (B × (Fin (d + 1) → ZMod n)) ×
      (Fin (d + 2) × Fin (Nc ^ 2 - 1))) :
      ‖actualCycleFullObservation I (physicalCycleLift hNc u) z‖ ^ 2 =
      if z.2.1 = Fin.succ 0 then if z.2.2 = cycleInternalZero hNc then
        ((∑ t ∈ I z.1.1, u t) / Real.sqrt ((I z.1.1).card : ℝ)) ^ 2 else 0 else 0 := by
    by_cases hl : z.2.1 = Fin.succ 0 <;> by_cases hk : z.2.2 = cycleInternalZero hNc
    all_goals simp [actualCycleFullObservation, physicalCycleLift_fibre_coordinate,
      hl, hk, Real.norm_eq_abs, sq_abs]
  simp_rw [hp]
  simp [Fintype.sum_prod_type, Fintype.card_fun, ZMod.card, Finset.mul_sum]

end YangMills.RG
