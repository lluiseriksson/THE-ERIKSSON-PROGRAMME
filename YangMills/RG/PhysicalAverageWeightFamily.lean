import YangMills.RG.PhysicalAverageWeightRank
import YangMills.RG.TorusFourierEnergyBound

/-! Actual average-weight nonlinear output-rank divergence. Positive strip
frequencies are transported through integer lifts; no wrapped-frequency or
desired trace comparison is an assumed certificate. -/
namespace YangMills.RG
open Module Filter
open scoped Topology RealInnerProductSpace
set_option maxHeartbeats 1600000

section Multipliers
variable {n R : ℕ} [NeZero n]

theorem positiveStripCharacter_multiplier_bound (r : Fin R) :
    ‖ZMod.stdAddChar ((r.val + 1 : ℕ) : ZMod n) - 1‖ ≤
      2 * Real.pi * (R : ℝ) / (n : ℝ) := by
  let k : Fin (2 * R + 1) := ⟨r.val + 1 + R, by omega⟩
  have heq : ((k.val : ℕ) : ZMod n) - (R : ZMod n) =
      ((r.val + 1 : ℕ) : ZMod n) := by
    dsimp [k]
    push_cast
    ring
  have h := stdAddChar_centered_bound (n := n) R k
  rw [heq] at h
  exact h

theorem positiveStrip_multiplier_sum_sq_le :
    (∑ r : Fin R, ‖ZMod.stdAddChar ((r.val + 1 : ℕ) : ZMod n) - 1‖ ^ 2) ≤
      (R : ℝ) * (2 * Real.pi * (R : ℝ) / (n : ℝ)) ^ 2 := by
  classical
  calc
    _ ≤ ∑ _r : Fin R, (2 * Real.pi * (R : ℝ) / (n : ℝ)) ^ 2 := by
      apply Finset.sum_le_sum
      intro r _
      have h := positiveStripCharacter_multiplier_bound (n := n) r
      have ha := norm_nonneg (ZMod.stdAddChar ((r.val + 1 : ℕ) : ZMod n) - 1)
      have hb : (0 : ℝ) ≤ 2 * Real.pi * (R : ℝ) / (n : ℝ) := by positivity
      nlinarith [mul_nonneg (sub_nonneg.mpr h) (add_nonneg hb ha)]
    _ = _ := by simp
end Multipliers

section Physical
variable {d n Nc R : ℕ} [NeZero d] [NeZero n] [NeZero Nc]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem physicalDirectionalWeightAverage_nonneg
    (w : PhysicalGradientIndex d n → ℝ) (hw : ∀ p, 0 ≤ w p) (i j : Fin d) :
    0 ≤ physicalDirectionalWeightAverage w i j := by
  unfold physicalDirectionalWeightAverage
  apply mul_nonneg
  · positivity
  · exact Finset.sum_nonneg (fun x _ => hw (i,(x,j)))

theorem physicalStrip_average_trace_le (w : PhysicalGradientIndex d n → ℝ)
    (hw : ∀ p, 0 ≤ w p) (i j : Fin d) :
    2 * (1 + physicalDirectionalWeightAverage w i j) *
      (∑ r : Fin R, ‖ZMod.stdAddChar ((r.val + 1 : ℕ) : ZMod n) - 1‖ ^ 2) ≤
      8 * Real.pi ^ 2 * (1 + physicalDirectionalWeightAverage w i j) *
        (R : ℝ) ^ 3 / (n : ℝ) ^ 2 := by
  have hb := physicalDirectionalWeightAverage_nonneg w hw i j
  calc
    _ ≤ 2 * (1 + physicalDirectionalWeightAverage w i j) *
        ((R : ℝ) * (2 * Real.pi * (R : ℝ) / (n : ℝ)) ^ 2) :=
      mul_le_mul_of_nonneg_left (positiveStrip_multiplier_sum_sq_le (n := n) (R := R))
        (by positivity)
    _ = _ := by rw [div_pow]; ring

theorem physicalStrip_nonlinear_average_rank_quantitative_bound (hNc : 2 ≤ Nc)
    (rho : SUNAdjointModel Nc) (i j : Fin d) (hij : i ≠ j) (hR : R < n)
    (w : PhysicalGradientIndex d n → ℝ) (hw : ∀ p, 0 ≤ w p)
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
      8 * Real.pi ^ 2 * (1 + physicalDirectionalWeightAverage w i j) *
        (R : ℝ) ^ 3 / (n : ℝ) ^ 2 := by
  exact (physicalStrip_nonlinear_average_rank_bound hNc rho i j hij hR w hw
    C L hC hC0 Phi K delta radius c hc hdelta hradius hPhi hlocal).trans
      (physicalStrip_average_trace_le w hw i j)
end Physical

theorem average_strip_cutoff_eventually (R : ℕ) :
    ∀ᶠ n : ℕ in atTop, R < n + 1 := by
  exact eventually_atTop.2 ⟨R, fun n hn => by omega⟩

theorem average_trace_threshold_eventually (R : ℕ) (b : ℕ → ℝ) (c : ℝ) (hc : 0 < c)
    (hsub : Tendsto (fun n : ℕ => (1 + b n) / ((n + 1 : ℕ) : ℝ) ^ 2)
      atTop (𝓝 0)) :
    ∀ᶠ n : ℕ in atTop,
      8 * Real.pi ^ 2 * (1 + b n) * (R : ℝ) ^ 3 / ((n + 1 : ℕ) : ℝ) ^ 2 < c := by
  have hlim := hsub.mul_const (8 * Real.pi ^ 2 * (R : ℝ) ^ 3)
  simp only [zero_mul] at hlim
  have hsmall := hlim.eventually (gt_mem_nhds hc)
  filter_upwards [hsmall] with n hn
  convert hn using 1 <;> ring

section ActualFamily
variable {d Nc : ℕ} [NeZero d] [NeZero Nc]
variable (hNc : 2 ≤ Nc) (rho : SUNAdjointModel Nc) (i j : Fin d) (hij : i ≠ j)
variable (F : ℕ → Type*) [∀ n, NormedAddCommGroup (F n)]
  [∀ n, NormedSpace ℝ (F n)] [∀ n, FiniteDimensional ℝ (F n)]
variable (w : ∀ n : ℕ, PhysicalGradientIndex d (n + 1) → ℝ)
  (hw : ∀ n p, 0 ≤ w n p)
variable (C : ∀ n : ℕ, PhysicalGaugeOneCochain d (n + 1) Nc → F n)
  (L : ∀ n : ℕ, PhysicalGaugeOneCochain d (n + 1) Nc →L[ℝ] F n)
  (hC : ∀ n, HasFDerivAt (C n) (L n) 0) (hC0 : ∀ n, C n 0 = 0)
variable (Phi : ∀ n, F n → ℝ) (K delta radius : ℕ → ℝ) (c : ℝ)
  (hdelta : ∀ n, 0 < delta n) (hradius : ∀ n, 0 < radius n)
  (hPhi : ∀ n y, ‖y‖ < delta n → Phi n y ≤ K n * ‖y‖ ^ 2) (hc : 0 < c)
  (hsub : Tendsto (fun n : ℕ => (1 + physicalDirectionalWeightAverage (w n) i j) /
    ((n + 1 : ℕ) : ℝ) ^ 2) atTop (𝓝 0))
variable (hlocal : ∀ n (A : PhysicalGaugeOneCochain d (n + 1) Nc),
    gaugeConstraintQCLM rho (trivialPhysicalGaugeBackground d (n + 1) Nc) A = 0 →
    ‖A‖ < radius n → c * ‖A‖ ^ 2 ≤
      inner ℝ A (flatGaugeHodgeK0CLM d (n + 1) Nc rho A) +
      inner ℝ A (componentwiseWeightedRepairCLM (w n) A) + Phi n (C n A))

include hNc rho i j hij w hw C L hC hC0 Phi K delta radius c hdelta hradius hPhi hc hsub hlocal

theorem physicalAverage_subquadratic_finrank_eventually_ge (R : ℕ) :
    ∀ᶠ n : ℕ in atTop, 2 * R ≤ finrank ℝ (F n) := by
  filter_upwards [average_strip_cutoff_eventually R,
    average_trace_threshold_eventually R (fun n => physicalDirectionalWeightAverage (w n) i j)
      c hc hsub] with n hcut hthreshold
  have h := physicalStrip_nonlinear_average_rank_quantitative_bound hNc rho i j hij hcut
    (w n) (hw n) (C n) (L n) (hC n) (hC0 n) (Phi n) (K n) (delta n)
    (radius n) c (le_of_lt hc) (hdelta n) (hradius n) (hPhi n) (hlocal n)
  by_contra hbad
  have hdim : finrank ℝ (F n) + 1 ≤ 2 * R := by omega
  have hdim' : (finrank ℝ (F n) : ℝ) + 1 ≤ 2 * (R : ℝ) := by exact_mod_cast hdim
  have hclower : c ≤ c * (2 * (R : ℝ) - (finrank ℝ (F n) : ℝ)) := by nlinarith
  linarith

theorem physicalAverage_subquadratic_finrank_tendsto :
    Tendsto (fun n : ℕ => finrank ℝ (F n)) atTop atTop := by
  apply tendsto_atTop.2
  intro m
  have h := physicalAverage_subquadratic_finrank_eventually_ge hNc rho i j hij F w hw
    C L hC hC0 Phi K delta radius c hdelta hradius hPhi hc hsub hlocal (m + 1)
  filter_upwards [h] with n hn
  omega

theorem physicalAverage_subquadratic_no_bounded_output :
    ¬ ∃ m : ℕ, ∀ n, finrank ℝ (F n) ≤ m := by
  rintro ⟨m, hm⟩
  have ht := physicalAverage_subquadratic_finrank_tendsto hNc rho i j hij F w hw
    C L hC hC0 Phi K delta radius c hdelta hradius hPhi hc hsub hlocal
  have he : ∀ᶠ n : ℕ in atTop, m + 1 ≤ finrank ℝ (F n) :=
    (tendsto_atTop.1 ht) (m + 1)
  obtain ⟨n, hn⟩ := he.exists
  have := hm n
  omega
end ActualFamily
end YangMills.RG
