import YangMills.RG.ComponentwiseFlatGradient

/-! Global all-cochain flat Hodge identity at the actual unordered plaquette
and counting-space conventions. No assumed comparison or physical bridge. -/
namespace YangMills.RG
open scoped BigOperators RealInnerProductSpace
set_option maxHeartbeats 1600000

theorem matrix_sum_eq_diag_add_orderedPairs {d : ℕ} (F : Fin d → Fin d → ℝ) :
    (∑ i, ∑ j, F i j) = (∑ i, F i i) +
      ∑ p : OrderedDirectionPair d, (F p.1.1 p.1.2 + F p.1.2 p.1.1) := by
  classical
  have hp : (∑ p : OrderedDirectionPair d, (F p.1.1 p.1.2 + F p.1.2 p.1.1)) =
      ∑ j : Fin d, ∑ i ∈ Finset.univ.erase j, F j i := by
    calc
      _ = ∑ j : Fin d, ∑ p : OrderedDirectionPair d,
          ((if p.1.1 = j then F j p.1.2 else 0) +
           (if p.1.2 = j then F j p.1.1 else 0)) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro p _
        rw [Finset.sum_add_distrib]
        simp
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j _
        exact orderedDirectionPair_incident_sum j (F j)
  rw [hp, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have h := Finset.sum_erase_add (Finset.univ : Finset (Fin d)) (F i)
    (Finset.mem_univ i)
  linarith

section Generic
variable {d n : ℕ} [NeZero n]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

private theorem norm_sub_sq_two_cross (u v : V) :
    ‖u - v‖ ^ 2 = ‖u‖ ^ 2 + ‖v‖ ^ 2 - inner ℝ u v - inner ℝ v u := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [inner_sub_left, inner_sub_right, real_inner_self_eq_norm_sq]
  ring

theorem finite_flat_curl_div_energy (a : Fin d → FinBox d n → V) :
    (∑ p : OrderedDirectionPair d, ∑ x : FinBox d n,
      ‖(a p.1.2 (x.shift p.1.1) - a p.1.2 x) -
        (a p.1.1 (x.shift p.1.2) - a p.1.1 x)‖ ^ 2) +
    (∑ x : FinBox d n, ‖∑ i : Fin d, (a i x - a i (x.shiftBack i))‖ ^ 2) =
      ∑ i : Fin d, ∑ j : Fin d, ∑ x : FinBox d n,
        ‖a j (x.shift i) - a j x‖ ^ 2 := by
  classical
  let Q (i j : Fin d) : ℝ := ∑ x, ‖a j (x.shift i) - a j x‖ ^ 2
  let R (i j : Fin d) : ℝ := ∑ x,
    inner ℝ (a i x - a i (x.shiftBack i)) (a j x - a j (x.shiftBack j))
  have hdiag : (∑ i, R i i) = ∑ i, Q i i := by
    apply Finset.sum_congr rfl
    intro i _
    dsimp [R, Q]
    simp only [real_inner_self_eq_norm_sq]
    exact flat_backward_forward_energy (a i) i
  have hdiv : (∑ x : FinBox d n, ‖∑ i : Fin d,
      (a i x - a i (x.shiftBack i))‖ ^ 2) = ∑ i, ∑ j, R i j := by
    simp only [← real_inner_self_eq_norm_sq, sum_inner, inner_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    dsimp [R]
    apply Finset.sum_congr rfl
    intro x _
    exact real_inner_comm _ _
  have hpair (i j : Fin d) :
      (∑ x : FinBox d n, ‖(a j (x.shift i) - a j x) -
        (a i (x.shift j) - a i x)‖ ^ 2) = Q i j + Q j i - (R i j + R j i) := by
    have hc₁ := flat_commuting_cross_cancellation (a j) (a i) i j
    have hc₂ := flat_commuting_cross_cancellation (a i) (a j) j i
    calc
      _ = ∑ x : FinBox d n,
          (‖a j (x.shift i) - a j x‖ ^ 2 + ‖a i (x.shift j) - a i x‖ ^ 2 -
            inner ℝ (a j (x.shift i) - a j x) (a i (x.shift j) - a i x) -
            inner ℝ (a i (x.shift j) - a i x) (a j (x.shift i) - a j x)) := by
        apply Finset.sum_congr rfl
        intro x _
        exact norm_sub_sq_two_cross _ _
      _ = _ := by
        simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
        dsimp [Q, R]
        linarith
  have hcurl : (∑ p : OrderedDirectionPair d, ∑ x : FinBox d n,
      ‖(a p.1.2 (x.shift p.1.1) - a p.1.2 x) -
        (a p.1.1 (x.shift p.1.2) - a p.1.1 x)‖ ^ 2) =
      (∑ p : OrderedDirectionPair d, (Q p.1.1 p.1.2 + Q p.1.2 p.1.1)) -
      ∑ p : OrderedDirectionPair d, (R p.1.1 p.1.2 + R p.1.2 p.1.1) := by
    simp_rw [hpair]
    rw [Finset.sum_sub_distrib]
  rw [hcurl, hdiv]
  have hR := matrix_sum_eq_diag_add_orderedPairs R
  have hQ := matrix_sum_eq_diag_add_orderedPairs Q
  change _ = ∑ i, ∑ j, Q i j
  linarith
end Generic

section Physical
variable {d n Nc : ℕ} [NeZero d] [NeZero n] [NeZero Nc]

theorem componentwiseFlatGradient_eq_hodge (ρ : SUNAdjointModel Nc)
    (A : PhysicalGaugeOneCochain d n Nc) :
    ‖componentwiseFlatGradientCLM A‖ ^ 2 =
      inner ℝ A (flatGaugeHodgeK0CLM d n Nc ρ A) := by
  classical
  let a : Fin d → FinBox d n → SUNLieCoord Nc := fun j x => A (x, j)
  have hcurl : ‖covariantD1CLM ρ (trivialPhysicalGaugeBackground d n Nc) A‖ ^ 2 =
      ∑ p : OrderedDirectionPair d, ∑ x : FinBox d n,
        ‖(a p.1.2 (x.shift p.1.1) - a p.1.2 x) -
          (a p.1.1 (x.shift p.1.2) - a p.1.1 x)‖ ^ 2 := by
    calc
      _ = ∑ p : ConcretePlaquette d n,
          ‖covariantD1CLM ρ (trivialPhysicalGaugeBackground d n Nc) A p‖ ^ 2 :=
        PiLp.norm_sq_eq_of_L2 _ _
      _ = ∑ z : FinBox d n × OrderedDirectionPair d,
          ‖(a z.2.1.2 (z.1.shift z.2.1.1) - a z.2.1.2 z.1) -
            (a z.2.1.1 (z.1.shift z.2.1.2) - a z.2.1.1 z.1)‖ ^ 2 := by
        refine Fintype.sum_equiv (concretePlaquetteEquivOrderedPair d n) _ _ ?_
        intro p
        rw [covariantD1CLM_trivial_apply]
        change ‖_‖ ^ 2 = ‖(A (p.site.shift p.dir1, p.dir2) - A (p.site, p.dir2)) -
          (A (p.site.shift p.dir2, p.dir1) - A (p.site, p.dir1))‖ ^ 2
        congr 2
        abel
      _ = _ := by rw [Fintype.sum_prod_type, Finset.sum_comm]
  have hdiv : ‖gaugeConstraintQCLM ρ (trivialPhysicalGaugeBackground d n Nc) A‖ ^ 2 =
      ∑ x : FinBox d n, ‖∑ i : Fin d, (a i x - a i (x.shiftBack i))‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    apply Finset.sum_congr rfl
    intro x _
    rw [gaugeConstraintQCLM_trivial_apply]
  have hg : ‖componentwiseFlatGradientCLM A‖ ^ 2 =
      ∑ i : Fin d, ∑ j : Fin d, ∑ x : FinBox d n,
        ‖a j (x.shift i) - a j x‖ ^ 2 := by
    rw [componentwiseFlatGradient_energy, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i _
    rw [Fintype.sum_prod_type, Finset.sum_comm]
  rw [flatGaugeHodgeK0_inner_right, hcurl, hdiv, hg]
  exact (finite_flat_curl_div_energy a).symm

theorem componentwiseWeightedRepair_le_hodge (ρ : SUNAdjointModel Nc)
    (w : PhysicalGradientIndex d n → ℝ) (M : ℝ) (hw : ∀ p, w p ≤ M)
    (A : PhysicalGaugeOneCochain d n Nc) :
    inner ℝ A (componentwiseWeightedRepairCLM w A) ≤
      M * inner ℝ A (flatGaugeHodgeK0CLM d n Nc ρ A) := by
  have h := componentwiseWeightedRepair_le_gradient w M hw A
  rw [componentwiseFlatGradient_eq_hodge ρ A] at h
  exact h
end Physical
end YangMills.RG
