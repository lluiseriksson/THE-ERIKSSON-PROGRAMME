import YangMills.RG.CoexactFlatEnergy

/-! Growing-volume consequences for actual maps and actual flat cochains.
No low-band, energy comparison or desired cutoff is a structure field.
The lattice size is n+1, so every member is a genuine positive-size torus. -/
namespace YangMills.RG
open Filter
open scoped Topology RealInnerProductSpace

theorem coexact_band_budget_dominates (d m : ℕ) :
    m < 2 * (m + 1) * (2 * (m + 1) + 1) ^ (d + 1) := by
  have hp : 0 < (2 * (m + 1) + 1) ^ (d + 1) := by positivity
  nlinarith

theorem coexact_subquadratic_cutoff_eventually (R : ℕ) :
    ∀ᶠ n : ℕ in atTop, 2 * R < n + 1 := by
  exact eventually_atTop.2 ⟨2 * R, fun n hn => by omega⟩

theorem coexact_subquadratic_threshold_eventually
    (d R : ℕ) (M : ℕ → ℝ) (c : ℝ) (hc : 0 < c)
    (hsub : Tendsto (fun n : ℕ => (1 + M n) / ((n + 1 : ℕ) : ℝ) ^ 2)
      atTop (𝓝 0)) :
    ∀ᶠ n : ℕ in atTop,
      (1 + M n) * (4 * Real.pi ^ 2 * ((d + 2 : ℕ) : ℝ) * (R : ℝ) ^ 2 /
        ((n + 1 : ℕ) : ℝ) ^ 2) < c := by
  have hlim := hsub.mul_const
    (4 * Real.pi ^ 2 * ((d + 2 : ℕ) : ℝ) * (R : ℝ) ^ 2)
  simp only [zero_mul] at hlim
  have hsmall := hlim.eventually (gt_mem_nhds hc)
  filter_upwards [hsmall] with n hn
  convert hn using 1 <;> ring

section ActualFamily
variable {d Nc : ℕ} [NeZero Nc]
variable (hNc : 2 ≤ Nc) (rho : SUNAdjointModel Nc)
variable (F : ℕ → Type*) [∀ n, NormedAddCommGroup (F n)]
  [∀ n, NormedSpace ℝ (F n)] [∀ n, FiniteDimensional ℝ (F n)]
variable (w : ∀ n : ℕ, PhysicalGradientIndex (d + 2) (n + 1) → ℝ)
  (M : ℕ → ℝ) (hM : ∀ n, 0 ≤ M n) (hw : ∀ n p, w n p ≤ M n)
variable (C : ∀ n : ℕ, PhysicalGaugeOneCochain (d + 2) (n + 1) Nc → F n)
  (L : ∀ n : ℕ, PhysicalGaugeOneCochain (d + 2) (n + 1) Nc →L[ℝ] F n)
  (hC : ∀ n, HasFDerivAt (C n) (L n) 0) (hC0 : ∀ n, C n 0 = 0)
variable (Phi : ∀ n, F n → ℝ) (K delta r : ℕ → ℝ) (c : ℝ)
  (hdelta : ∀ n, 0 < delta n) (hr : ∀ n, 0 < r n)
  (hPhi : ∀ n y, ‖y‖ < delta n → Phi n y ≤ K n * ‖y‖ ^ 2) (hc : 0 < c)
  (hsub : Tendsto (fun n : ℕ => (1 + M n) / ((n + 1 : ℕ) : ℝ) ^ 2)
    atTop (𝓝 0))
variable (hbound : ∀ n (x : PhysicalGaugeOneCochain (d + 2) (n + 1) Nc),
    gaugeConstraintQCLM rho (trivialPhysicalGaugeBackground (d + 2) (n + 1) Nc) x = 0 →
    ‖x‖ < r n → c * ‖x‖ ^ 2 ≤
      inner ℝ x (flatGaugeHodgeK0CLM (d + 2) (n + 1) Nc rho x) +
      inner ℝ x (componentwiseWeightedRepairCLM (w n) x) + Phi n (C n x))

include hNc rho w M hM hw C L hC hC0 Phi K delta r c hdelta hr hPhi hc hsub hbound

theorem coexactFlat_subquadratic_finrank_eventually_ge (R : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      2 * R * (2 * R + 1) ^ (d + 1) ≤ Module.finrank ℝ (F n) := by
  filter_upwards [coexact_subquadratic_cutoff_eventually R,
    coexact_subquadratic_threshold_eventually d R M c hc hsub] with n hcut hthreshold
  by_contra hbad
  have hdim : Module.finrank ℝ (F n) < 2 * R * (2 * R + 1) ^ (d + 1) :=
    Nat.lt_of_not_ge hbad
  exact (coexactFlat_local_coercivity_false hNc rho R hcut (w n) (M n)
    (hM n) (hw n) (C n) (L n) (hC n) (hC0 n) (Phi n) (K n) (delta n)
    (r n) c (hdelta n) (hr n) (hPhi n) hdim hthreshold) (hbound n)

theorem coexactFlat_subquadratic_finrank_tendsto :
    Tendsto (fun n : ℕ => Module.finrank ℝ (F n)) atTop atTop := by
  apply tendsto_atTop.2
  intro m
  have h := coexactFlat_subquadratic_finrank_eventually_ge hNc rho F w M hM hw
    C L hC hC0 Phi K delta r c hdelta hr hPhi hc hsub hbound (m + 1)
  filter_upwards [h] with n hn
  exact le_trans (Nat.le_of_lt (coexact_band_budget_dominates d m)) hn

theorem coexactFlat_subquadratic_no_bounded_output :
    ¬ ∃ m : ℕ, ∀ n, Module.finrank ℝ (F n) ≤ m := by
  rintro ⟨m, hm⟩
  have ht := coexactFlat_subquadratic_finrank_tendsto hNc rho F w M hM hw
    C L hC hC0 Phi K delta r c hdelta hr hPhi hc hsub hbound
  have he : ∀ᶠ n : ℕ in atTop, m + 1 ≤ Module.finrank ℝ (F n) :=
    (tendsto_atTop.1 ht) (m + 1)
  obtain ⟨n, hn⟩ := he.exists
  have := hm n
  omega
end ActualFamily
end YangMills.RG
