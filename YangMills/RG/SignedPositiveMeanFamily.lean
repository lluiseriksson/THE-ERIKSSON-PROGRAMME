import YangMills.RG.PhysicalAverageWeightFamily

/-! Signed actual weights are allowed. The constructed pointwise positive part
dominates their actual repair energy; its spatial mean, not the positive part
of the signed spatial mean, is used in the family condition. -/
namespace YangMills.RG
open Module Filter
open scoped Topology RealInnerProductSpace

section Weights
variable {d n Nc : ℕ} [NeZero d] [NeZero n] [NeZero Nc]

noncomputable def signedWeightPositivePart (w : PhysicalGradientIndex d n → ℝ) :
    PhysicalGradientIndex d n → ℝ := fun p => max (w p) 0

theorem signedWeightPositivePart_nonneg (w : PhysicalGradientIndex d n → ℝ)
    (p : PhysicalGradientIndex d n) : 0 ≤ signedWeightPositivePart w p :=
  le_max_right _ _

theorem componentwiseWeightedRepair_mono
    (w v : PhysicalGradientIndex d n → ℝ) (hwv : ∀ p, w p ≤ v p)
    (A : PhysicalGaugeOneCochain d n Nc) :
    inner ℝ A (componentwiseWeightedRepairCLM w A) ≤
      inner ℝ A (componentwiseWeightedRepairCLM v A) := by
  classical
  rw [componentwiseWeightedRepair_energy, componentwiseWeightedRepair_energy]
  exact Finset.sum_le_sum (fun p _ =>
    mul_le_mul_of_nonneg_right (hwv p) (sq_nonneg _))

theorem signedWeightPositivePart_energy_le (w : PhysicalGradientIndex d n → ℝ)
    (A : PhysicalGaugeOneCochain d n Nc) :
    inner ℝ A (componentwiseWeightedRepairCLM w A) ≤
      inner ℝ A (componentwiseWeightedRepairCLM (signedWeightPositivePart w) A) := by
  exact componentwiseWeightedRepair_mono w (signedWeightPositivePart w)
    (fun p => le_max_left (w p) 0) A

end Weights

section Physical
variable {d n Nc R : ℕ} [NeZero d] [NeZero n] [NeZero Nc]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem physicalSignedPositiveMean_rank_quantitative_bound (hNc : 2 ≤ Nc)
    (rho : SUNAdjointModel Nc) (i j : Fin d) (hij : i ≠ j) (hR : R < n)
    (w : PhysicalGradientIndex d n → ℝ)
    (C : PhysicalGaugeOneCochain d n Nc → F)
    (L : PhysicalGaugeOneCochain d n Nc →L[ℝ] F)
    (hC : HasFDerivAt C L 0) (hC0 : C 0 = 0)
    (Phi : F → ℝ) (K delta radius c : ℝ) (hc : 0 ≤ c)
    (hdelta : 0 < delta) (hradius : 0 < radius)
    (hPhi : ∀ y, ‖y‖ < delta → Phi y ≤ K * ‖y‖ ^ 2)
    (hlocal : ∀ A : PhysicalGaugeOneCochain d n Nc,
      gaugeConstraintQCLM rho (trivialPhysicalGaugeBackground d n Nc) A = 0 →
      ‖A‖ < radius → c * ‖A‖ ^ 2 ≤
        inner ℝ A (flatGaugeHodgeK0CLM d n Nc rho A) +
        inner ℝ A (componentwiseWeightedRepairCLM w A) + Phi (C A)) :
    c * (2 * (R : ℝ) - (finrank ℝ F : ℝ)) ≤
      8 * Real.pi ^ 2 *
        (1 + physicalDirectionalWeightAverage (signedWeightPositivePart w) i j) *
        (R : ℝ) ^ 3 / (n : ℝ) ^ 2 := by
  apply physicalStrip_nonlinear_average_rank_quantitative_bound hNc rho i j hij hR
    (signedWeightPositivePart w) (signedWeightPositivePart_nonneg w)
    C L hC hC0 Phi K delta radius c hc hdelta hradius hPhi
  intro A hdiv hsmall
  have h := hlocal A hdiv hsmall
  have horder := signedWeightPositivePart_energy_le w A
  linarith
end Physical

section ActualFamily
variable {d Nc : ℕ} [NeZero d] [NeZero Nc]
variable (hNc : 2 ≤ Nc) (rho : SUNAdjointModel Nc) (i j : Fin d) (hij : i ≠ j)
variable (F : ℕ → Type*) [∀ n, NormedAddCommGroup (F n)]
  [∀ n, NormedSpace ℝ (F n)] [∀ n, FiniteDimensional ℝ (F n)]
variable (w : ∀ n : ℕ, PhysicalGradientIndex d (n + 1) → ℝ)
variable (C : ∀ n : ℕ, PhysicalGaugeOneCochain d (n + 1) Nc → F n)
  (L : ∀ n : ℕ, PhysicalGaugeOneCochain d (n + 1) Nc →L[ℝ] F n)
  (hC : ∀ n, HasFDerivAt (C n) (L n) 0) (hC0 : ∀ n, C n 0 = 0)
variable (Phi : ∀ n, F n → ℝ) (K delta radius : ℕ → ℝ) (c : ℝ)
  (hdelta : ∀ n, 0 < delta n) (hradius : ∀ n, 0 < radius n)
  (hPhi : ∀ n y, ‖y‖ < delta n → Phi n y ≤ K n * ‖y‖ ^ 2) (hc : 0 < c)
  (hsub : Tendsto (fun n : ℕ =>
    (1 + physicalDirectionalWeightAverage (signedWeightPositivePart (w n)) i j) /
    ((n + 1 : ℕ) : ℝ) ^ 2) atTop (𝓝 0))
variable (hlocal : ∀ n (A : PhysicalGaugeOneCochain d (n + 1) Nc),
    gaugeConstraintQCLM rho (trivialPhysicalGaugeBackground d (n + 1) Nc) A = 0 →
    ‖A‖ < radius n → c * ‖A‖ ^ 2 ≤
      inner ℝ A (flatGaugeHodgeK0CLM d (n + 1) Nc rho A) +
      inner ℝ A (componentwiseWeightedRepairCLM (w n) A) + Phi n (C n A))

include hNc rho i j hij w C L hC hC0 Phi K delta radius c hdelta hradius hPhi hc hsub hlocal

theorem physicalSignedPositiveMean_finrank_tendsto :
    Tendsto (fun n : ℕ => finrank ℝ (F n)) atTop atTop := by
  have hlocalPos : ∀ n (A : PhysicalGaugeOneCochain d (n + 1) Nc),
      gaugeConstraintQCLM rho (trivialPhysicalGaugeBackground d (n + 1) Nc) A = 0 →
      ‖A‖ < radius n → c * ‖A‖ ^ 2 ≤
        inner ℝ A (flatGaugeHodgeK0CLM d (n + 1) Nc rho A) +
        inner ℝ A (componentwiseWeightedRepairCLM (signedWeightPositivePart (w n)) A) +
        Phi n (C n A) := by
    intro n A hdiv hsmall
    have h := hlocal n A hdiv hsmall
    have horder := signedWeightPositivePart_energy_le (w n) A
    linarith
  exact physicalAverage_subquadratic_finrank_tendsto hNc rho i j hij F
    (fun n => signedWeightPositivePart (w n))
    (fun n => signedWeightPositivePart_nonneg (w n)) C L hC hC0 Phi K delta radius c
    hdelta hradius hPhi hc hsub hlocalPos

theorem physicalSignedPositiveMean_no_bounded_output :
    ¬ ∃ m : ℕ, ∀ n, finrank ℝ (F n) ≤ m := by
  rintro ⟨m, hm⟩
  have ht := physicalSignedPositiveMean_finrank_tendsto hNc rho i j hij F w C L hC hC0
    Phi K delta radius c hdelta hradius hPhi hc hsub hlocal
  have he : ∀ᶠ n : ℕ in atTop, m + 1 ≤ finrank ℝ (F n) :=
    (tendsto_atTop.1 ht) (m + 1)
  obtain ⟨n, hn⟩ := he.exists
  have := hm n
  omega
end ActualFamily
end YangMills.RG
