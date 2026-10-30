import YangMills.RG.TorusPhysicalShift
import YangMills.RG.TorusFourierEnergyBound
import YangMills.RG.PhysicalPoincareLowModeHodge

/-! Exact physical-interface flat Hodge energy of the constructed Fourier map.
    Unordered plaquettes are counted once. No dimension or continuum claim. -/
namespace YangMills.RG
open scoped BigOperators RealInnerProductSpace
variable {d n Nc : ℕ} [NeZero n]

set_option maxHeartbeats 800000 in
theorem orderedDirectionPair_incident_sum (j : Fin d) (F : Fin d → ℝ) :
    (∑ q : OrderedDirectionPair d,
      ((if q.1.1 = j then F q.1.2 else 0) +
       (if q.1.2 = j then F q.1.1 else 0))) =
      ∑ i ∈ Finset.univ.erase j, F i := by
  classical
  let H : Fin d × Fin d → ℝ := fun q =>
    (if q.1 = j then F q.2 else 0) + (if q.2 = j then F q.1 else 0)
  have hsub : (∑ q : OrderedDirectionPair d, H q.1) =
      ∑ q : Fin d × Fin d, if q.1 < q.2 then H q else 0 := by
    rw [← Finset.sum_filter]
    exact (Finset.sum_subtype
      (Finset.univ.filter (fun q : Fin d × Fin d => q.1 < q.2))
      (by intro q; simp) H).symm
  change (∑ q : OrderedDirectionPair d, H q.1) = _
  rw [hsub]
  have hpoint (q : Fin d × Fin d) :
      (if q.1 < q.2 then H q else 0) =
        (if q.1 = j then (if j < q.2 then F q.2 else 0) else 0) +
        (if q.2 = j then (if q.1 < j then F q.1 else 0) else 0) := by
    by_cases h : q.1 < q.2 <;> by_cases h1 : q.1 = j <;>
      by_cases h2 : q.2 = j <;> simp_all [H]
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib, Fintype.sum_prod_type, Fintype.sum_prod_type]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [← Finset.sum_add_distrib]
  have he : Finset.univ.erase j = Finset.univ.filter (fun i : Fin d => i ≠ j) := by
    ext i
    simp [ne_comm]
  rw [he, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases h : i = j
  · subst i; simp
  · rcases lt_or_gt_of_ne h with hij | hji
    · simp [h, hij, not_lt_of_ge (le_of_lt hij)]
    · simp [h, hji, not_lt_of_ge (le_of_lt hji)]

variable [NeZero d] [NeZero Nc]

set_option maxHeartbeats 800000 in
theorem torusPhysicalEmbed_flat_curl_norm_point (hNc : 2 ≤ Nc) (ρ : SUNAdjointModel Nc)
    (j : Fin d) (f : (Fin d → ZMod n) → ℂ) (p : ConcretePlaquette d n) :
    ‖covariantD1CLM ρ (trivialPhysicalGaugeBackground d n Nc)
      (torusPhysicalEmbed hNc j f) p‖ ^ 2 =
    (if p.dir1 = j then ‖f (finBoxZModEquiv d n p.site + Pi.single p.dir2 (1 : ZMod n)) -
      f (finBoxZModEquiv d n p.site)‖ ^ 2 else 0) +
    (if p.dir2 = j then ‖f (finBoxZModEquiv d n p.site + Pi.single p.dir1 (1 : ZMod n)) -
      f (finBoxZModEquiv d n p.site)‖ ^ 2 else 0) := by
  rw [torusPhysicalEmbed_flat_curl_apply]
  by_cases h1 : p.dir1 = j <;> by_cases h2 : p.dir2 = j
  · have hlt := p.hlt
    rw [h1, h2] at hlt
    exact False.elim ((lt_irrefl j) hlt)
  · simp only [if_pos h1, if_neg h2, add_zero, sunComplexPlane_norm_sq]
    rw [norm_sub_rev]
  · simp [h1, h2, sunComplexPlane_norm_sq]
  · simp [h1, h2]

set_option maxHeartbeats 1500000 in
theorem torusPhysicalEmbed_flat_curl_norm_sq (hNc : 2 ≤ Nc) (ρ : SUNAdjointModel Nc)
    (j : Fin d) (f : (Fin d → ZMod n) → ℂ) :
    ‖covariantD1CLM ρ (trivialPhysicalGaugeBackground d n Nc)
      (torusPhysicalEmbed hNc j f)‖ ^ 2 =
      ∑ i ∈ Finset.univ.erase j, forwardShiftEnergy f (Pi.single i (1 : ZMod n)) := by
  classical
  let D := covariantD1CLM ρ (trivialPhysicalGaugeBackground d n Nc)
    (torusPhysicalEmbed hNc j f)
  let E (x : FinBox d n) (i : Fin d) :=
    ‖f (finBoxZModEquiv d n x + Pi.single i (1 : ZMod n)) -
      f (finBoxZModEquiv d n x)‖ ^ 2
  calc
    _ = ∑ p : ConcretePlaquette d n, ‖D p‖ ^ 2 := PiLp.norm_sq_eq_of_L2 _ D
    _ = ∑ z : FinBox d n × OrderedDirectionPair d,
        ((if z.2.1.1 = j then E z.1 z.2.1.2 else 0) +
         (if z.2.1.2 = j then E z.1 z.2.1.1 else 0)) := by
      refine Fintype.sum_equiv (concretePlaquetteEquivOrderedPair d n) _ _ ?_
      intro p
      exact torusPhysicalEmbed_flat_curl_norm_point hNc ρ j f p
    _ = ∑ x : FinBox d n, ∑ i ∈ Finset.univ.erase j, E x i := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro x hx
      exact orderedDirectionPair_incident_sum j (E x)
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      unfold forwardShiftEnergy
      refine Fintype.sum_equiv (finBoxZModEquiv d n) _ _ ?_
      intro x
      rfl

set_option maxHeartbeats 800000 in
theorem torusPhysicalEmbed_flat_hodge_eq_stencil (hNc : 2 ≤ Nc) (ρ : SUNAdjointModel Nc)
    (j : Fin d) (f : (Fin d → ZMod n) → ℂ) :
    inner ℝ (torusPhysicalEmbed hNc j f)
      (flatGaugeHodgeK0CLM d n Nc ρ (torusPhysicalEmbed hNc j f)) =
      oneComponentStencilEnergy f (fun i => Pi.single i (1 : ZMod n)) j := by
  rw [flatGaugeHodgeK0_inner_right,
    torusPhysicalEmbed_flat_curl_norm_sq, torusPhysicalEmbed_flat_div_norm_sq]
  rfl

set_option maxHeartbeats 800000 in
theorem centeredFourier_physical_hodge_le (hNc : 2 ≤ Nc) (ρ : SUNAdjointModel Nc)
    (j : Fin d) (R : ℕ) (hR : 2 * R < n) (c : (Fin d → Fin (2 * R + 1)) → ℂ) :
    let A := torusPhysicalEmbed hNc j
      (fun x => ∑ k, c k * centeredFourierProfile (d := d) (n := n) R k x)
    inner ℝ A (flatGaugeHodgeK0CLM d n Nc ρ A) ≤
      (4 * Real.pi ^ 2 * (d : ℝ) * (R : ℝ) ^ 2 / (n : ℝ) ^ 2) * ‖A‖ ^ 2 := by
  dsimp only
  rw [torusPhysicalEmbed_flat_hodge_eq_stencil, torusPhysicalEmbed_norm_sq]
  exact centeredFourier_stencilEnergy_le R hR c j

end YangMills.RG
