import YangMills.RG.SignedPositiveMeanFamily
import YangMills.RG.TorusPhysicalShift

/-! Actual square-path cancellation. The operator order is derived from
telescoping differences; it is not an input comparison certificate. -/
namespace YangMills.RG
open Module Filter
open scoped BigOperators Topology RealInnerProductSpace

theorem three_term_norm_sq_le {V : Type*} [NormedAddCommGroup V] (x y z : V) :
    ‖x + y - z‖^2 ≤ 3 * (‖x‖^2 + ‖y‖^2 + ‖z‖^2) := by
  have ht : ‖x + y - z‖ ≤ ‖x‖ + ‖y‖ + ‖z‖ := by
    have h1 := norm_sub_le (x+y) z
    have h2 := norm_add_le x y
    linarith
  have hs := pow_le_pow_left₀ (norm_nonneg (x+y-z)) ht 2
  nlinarith [sq_nonneg (‖x‖-‖y‖), sq_nonneg (‖x‖-‖z‖),
    sq_nonneg (‖y‖-‖z‖)]

section Actual
variable {d n Nc : ℕ} [NeZero d] [NeZero n] [NeZero Nc]

theorem finBox_shift_ne_of_one_lt (hn : 1 < n) (o : FinBox d n) (k : Fin d) :
    o.shift k ≠ o := by
  letI : Fact (1 < n) := ⟨hn⟩
  intro h
  have he := congrArg (finBoxZModEquiv d n) h
  rw [finBoxZModEquiv_shift] at he
  have hk := congrFun he k
  have h1 : finBoxZModEquiv d n o k + (1 : ZMod n) =
      finBoxZModEquiv d n o k + 0 := by simpa using hk
  exact one_ne_zero (add_left_cancel h1)

theorem squareCycle_path_norm_sq_le (o : FinBox d n) (i k j : Fin d) (hik : i ≠ k)
    (A : PhysicalGaugeOneCochain d n Nc) :
    ‖A (o.shift i,j) - A (o,j)‖^2 ≤
      3 * (‖A (o.shift k,j) - A (o,j)‖^2 +
        ‖A ((o.shift k).shift i,j) - A (o.shift k,j)‖^2 +
        ‖A ((o.shift i).shift k,j) - A (o.shift i,j)‖^2) := by
  have he : A (o.shift i,j) - A (o,j) =
      (A (o.shift k,j) - A (o,j)) +
      (A ((o.shift k).shift i,j) - A (o.shift k,j)) -
      (A ((o.shift i).shift k,j) - A (o.shift i,j)) := by
    rw [FinBox.shift_comm o i k hik]
    abel
  rw [he]
  exact three_term_norm_sq_le _ _ _

noncomputable def squareCycleWeights (o : FinBox d n) (i k j : Fin d) (a : ℝ)
    (p : PhysicalGradientIndex d n) : ℝ :=
  (if p = (i,(o,j)) then a else 0) -
  (if p = (k,(o,j)) then 3*a else 0) -
  (if p = (i,(o.shift k,j)) then 3*a else 0) -
  (if p = (k,(o.shift i,j)) then 3*a else 0)

theorem squareCycleWeights_energy (o : FinBox d n) (i k j : Fin d) (a : ℝ)
    (A : PhysicalGaugeOneCochain d n Nc) :
    inner ℝ A (componentwiseWeightedRepairCLM (squareCycleWeights o i k j a) A) =
      a * ‖A (o.shift i,j) - A (o,j)‖^2 -
      3*a * ‖A (o.shift k,j) - A (o,j)‖^2 -
      3*a * ‖A ((o.shift k).shift i,j) - A (o.shift k,j)‖^2 -
      3*a * ‖A ((o.shift i).shift k,j) - A (o.shift i,j)‖^2 := by
  classical
  rw [componentwiseWeightedRepair_energy]
  simp [squareCycleWeights, sub_mul, Finset.sum_sub_distrib, ite_mul]

theorem squareCycleWeights_nonpositive (o : FinBox d n) (i k j : Fin d)
    (hik : i ≠ k) (a : ℝ) (ha : 0 ≤ a) (A : PhysicalGaugeOneCochain d n Nc) :
    inner ℝ A (componentwiseWeightedRepairCLM (squareCycleWeights o i k j a) A) ≤ 0 := by
  rw [squareCycleWeights_energy]
  have h := mul_le_mul_of_nonneg_left (squareCycle_path_norm_sq_le o i k j hik A) ha
  nlinarith

theorem squareCycleWeights_positive_part (hn : 1 < n) (o : FinBox d n)
    (i k j : Fin d) (hik : i ≠ k) (a : ℝ) (ha : 0 ≤ a)
    (p : PhysicalGradientIndex d n) :
    signedWeightPositivePart (squareCycleWeights o i k j a) p =
      if p = (i,(o,j)) then a else 0 := by
  classical
  have hshift := finBox_shift_ne_of_one_lt hn o k
  have hp1 : (i,(o,j)) ≠ (k,(o,j)) := by
    intro h
    exact hik (congrArg Prod.fst h)
  have hp2 : (i,(o,j)) ≠ (i,(o.shift k,j)) := by
    intro h
    exact hshift (congrArg (fun p : PhysicalGradientIndex d n => p.2.1) h).symm
  have hp3 : (i,(o,j)) ≠ (k,(o.shift i,j)) := by
    intro h
    exact hik (congrArg Prod.fst h)
  by_cases hp : p = (i,(o,j))
  · subst p
    simp [signedWeightPositivePart, squareCycleWeights, hp1, hp2, hp3, max_eq_left ha]
  · have hw : squareCycleWeights o i k j a p ≤ 0 := by
      unfold squareCycleWeights
      rw [if_neg hp]
      have h1 : 0 ≤ if p = (k,(o,j)) then 3*a else 0 := by positivity
      have h2 : 0 ≤ if p = (i,(o.shift k,j)) then 3*a else 0 := by positivity
      have h3 : 0 ≤ if p = (k,(o.shift i,j)) then 3*a else 0 := by positivity
      linarith
    simp [signedWeightPositivePart, max_eq_right hw, hp]

theorem squareCycleWeights_positive_average (hn : 1 < n) (o : FinBox d n)
    (i k j : Fin d) (hik : i ≠ k) (a : ℝ) (ha : 0 ≤ a) :
    physicalDirectionalWeightAverage
      (signedWeightPositivePart (squareCycleWeights o i k j a)) i j =
      ((n : ℝ)^d)⁻¹ * a := by
  classical
  unfold physicalDirectionalWeightAverage
  simp_rw [squareCycleWeights_positive_part hn o i k j hik a ha]
  simp

theorem squareCycleWeights_critical_positive_average (hn : 1 < n) (o : FinBox d n)
    (i k j : Fin d) (hik : i ≠ k) :
    physicalDirectionalWeightAverage
      (signedWeightPositivePart
        (squareCycleWeights o i k j ((n : ℝ)^d * (n : ℝ)^2))) i j = (n : ℝ)^2 := by
  rw [squareCycleWeights_positive_average hn o i k j hik _ (by positivity)]
  have hne : (n : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne n
  rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero d hne), one_mul]

end Actual

theorem zeroWeightAverage_subquadratic {d : ℕ} [NeZero d] (i j : Fin d) :
    Tendsto (fun n : ℕ =>
      (1 + physicalDirectionalWeightAverage
        (fun _ : PhysicalGradientIndex d (n+1) => (0 : ℝ)) i j) /
        ((n+1 : ℕ) : ℝ)^2) atTop (𝓝 0) := by
  have hn : Tendsto (fun n : ℕ => ((n+1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_atTop_mono (fun n => by exact_mod_cast Nat.le_succ n)
      tendsto_natCast_atTop_atTop
  have hi := tendsto_inv_atTop_zero.comp hn
  have hs := hi.pow 2
  simpa [physicalDirectionalWeightAverage, one_div, inv_pow] using hs

section Family
variable {d Nc : ℕ} [NeZero d] [NeZero Nc]
variable (hNc : 2 ≤ Nc) (rho : SUNAdjointModel Nc)
  (i k j : Fin d) (hik : i ≠ k)
variable (F : ℕ → Type*) [∀ n, NormedAddCommGroup (F n)]
  [∀ n, NormedSpace ℝ (F n)] [∀ n, FiniteDimensional ℝ (F n)]
variable (o : ∀ n, FinBox d (n+1))
variable (C : ∀ n, PhysicalGaugeOneCochain d (n+1) Nc → F n)
  (L : ∀ n, PhysicalGaugeOneCochain d (n+1) Nc →L[ℝ] F n)
  (hC : ∀ n, HasFDerivAt (C n) (L n) 0) (hC0 : ∀ n, C n 0 = 0)
variable (Phi : ∀ n, F n → ℝ) (K delta radius : ℕ → ℝ) (c : ℝ)
  (hdelta : ∀ n, 0 < delta n) (hradius : ∀ n, 0 < radius n)
  (hPhi : ∀ n y, ‖y‖ < delta n → Phi n y ≤ K n * ‖y‖^2) (hc : 0 < c)
variable (hlocal : ∀ n (A : PhysicalGaugeOneCochain d (n+1) Nc),
  gaugeConstraintQCLM rho (trivialPhysicalGaugeBackground d (n+1) Nc) A = 0 →
  ‖A‖ < radius n → c * ‖A‖^2 ≤
    inner ℝ A (flatGaugeHodgeK0CLM d (n+1) Nc rho A) +
    inner ℝ A (componentwiseWeightedRepairCLM
      (squareCycleWeights (o n) i k j (((n+1 : ℕ) : ℝ)^d * ((n+1 : ℕ) : ℝ)^2)) A) +
    Phi n (C n A))

include hNc rho i k j hik F o C L hC hC0 Phi K delta radius c hdelta hradius hPhi hc hlocal

theorem squareCycle_finrank_tendsto :
    Tendsto (fun n : ℕ => finrank ℝ (F n)) atTop atTop := by
  have hlocal0 : ∀ n (A : PhysicalGaugeOneCochain d (n+1) Nc),
      gaugeConstraintQCLM rho (trivialPhysicalGaugeBackground d (n+1) Nc) A = 0 →
      ‖A‖ < radius n → c * ‖A‖^2 ≤
        inner ℝ A (flatGaugeHodgeK0CLM d (n+1) Nc rho A) +
        inner ℝ A (componentwiseWeightedRepairCLM (fun _ => 0) A) + Phi n (C n A) := by
    intro n A hdiv hsmall
    have h := hlocal n A hdiv hsmall
    have hneg := squareCycleWeights_nonpositive (o n) i k j hik
      (((n+1 : ℕ) : ℝ)^d * ((n+1 : ℕ) : ℝ)^2) (by positivity) A
    have hz : inner ℝ A (componentwiseWeightedRepairCLM (fun _ => 0) A) = 0 := by
      rw [componentwiseWeightedRepair_energy]
      simp
    rw [hz]
    linarith
  exact physicalAverage_subquadratic_finrank_tendsto hNc rho i k hik F
    (fun _ _ => 0) (fun _ _ => le_rfl) C L hC hC0 Phi K delta radius c
    hdelta hradius hPhi hc (zeroWeightAverage_subquadratic i k) hlocal0

theorem squareCycle_no_bounded_output :
    ¬ ∃ m : ℕ, ∀ n, finrank ℝ (F n) ≤ m := by
  rintro ⟨m, hm⟩
  have ht := squareCycle_finrank_tendsto hNc rho i k j hik F o C L hC hC0
    Phi K delta radius c hdelta hradius hPhi hc hlocal
  have he : ∀ᶠ n : ℕ in atTop, m+1 ≤ finrank ℝ (F n) :=
    (tendsto_atTop.1 ht) (m+1)
  obtain ⟨n, hn⟩ := he.exists
  have := hm n
  omega
end Family
end YangMills.RG
