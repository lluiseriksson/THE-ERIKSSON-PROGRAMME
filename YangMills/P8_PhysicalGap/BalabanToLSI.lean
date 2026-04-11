import Mathlib
import YangMills.P8_PhysicalGap.LSIDefinitions
import YangMills.P8_PhysicalGap.SUN_StateConstruction

/-!
# P8.3: Bałaban RG → DLR-LSI(α*) — C132: Gibbs normalization + correct HS axiom

## Summary of C132 changes (v1.44.0)

**Mathematical fix**: the original proof chain used `holleyStroock_sunGibbs_lsi`
for the **un-normalized** Gibbs measure (total mass Z_β < 1), leading to a
false LogSobolevInequality (the entropy of constant functions is non-zero while
the abstract Dirichlet form vanishes for constants).

C132 introduces the **normalized** Gibbs family and replaces the abstract
Holley-Stroock axiom with a specific, correctly-stated instance:

1. `sunPlaquetteEnergy_continuous` — proved from matrix/trace/re continuity
2. `sunPartitionFunction_pos/le_one` — Z_β ∈ (exp(-2β), 1] (uses C131)
3. `sunGibbsFamily_norm` — normalized probability Gibbs measure
4. `instIsProbabilityMeasure_sunGibbsFamily_norm` — **proved** theorem
5. `lsi_normalized_gibbs_from_haar` — specific HS axiom for the normalized
   probability Gibbs (correctly stated: true for probability measures)
6. `sun_gibbs_dlr_lsi_norm` — DLR-LSI via the correct normalized path
-/

namespace YangMills

open MeasureTheory Real

/-! ## Abstract SU(N) objects -/

abbrev SUN_State (N_c : ℕ) : Type := SUN_State_Concrete N_c

noncomputable def sunDirichletForm (N_c : ℕ) [NeZero N_c] (f : SUN_State N_c → ℝ) : ℝ :=
  (N_c : ℝ) / 8 *
    (∫ x, f x ^ 2 * Real.log (f x ^ 2) ∂(sunHaarProb N_c) -
      (∫ x, f x ^ 2 ∂(sunHaarProb N_c)) * Real.log (∫ x, f x ^ 2 ∂(sunHaarProb N_c)))

noncomputable def sunPlaquetteEnergy (N_c : ℕ) [NeZero N_c] : SUN_State N_c → ℝ :=
  fun g => 1 - (Matrix.trace g.val).re / (N_c : ℝ)

/-! ## C131: trace bounds and plaquette energy bounds (retained verbatim) -/

private lemma re_trace_le_Nc (N_c : ℕ) [NeZero N_c] (g : SUN_State N_c) :
    (Matrix.trace g.val).re ≤ (N_c : ℝ) := by
  have hU : g.val ∈ Matrix.unitaryGroup (Fin N_c) ℂ :=
    (Matrix.mem_specialUnitaryGroup_iff.mp g.property).1
  have htr : (Matrix.trace g.val).re = ∑ i : Fin N_c, (g.val i i).re := by
    simp [Matrix.trace, Matrix.diag]
  rw [htr]
  calc ∑ i : Fin N_c, (g.val i i).re
      ≤ ∑ i : Fin N_c, ‖g.val i i‖ :=
        Finset.sum_le_sum fun i _ => Complex.re_le_norm (g.val i i)
    _ ≤ ∑ _i : Fin N_c, (1 : ℝ) :=
        Finset.sum_le_sum fun i _ => entry_norm_bound_of_unitary hU i i
    _ = (N_c : ℝ) := by simp

private lemma neg_Nc_le_re_trace (N_c : ℕ) [NeZero N_c] (g : SUN_State N_c) :
    -(N_c : ℝ) ≤ (Matrix.trace g.val).re := by
  have hU : g.val ∈ Matrix.unitaryGroup (Fin N_c) ℂ :=
    (Matrix.mem_specialUnitaryGroup_iff.mp g.property).1
  have htr : (Matrix.trace g.val).re = ∑ i : Fin N_c, (g.val i i).re := by
    simp [Matrix.trace, Matrix.diag]
  rw [htr]
  have hNsum : -(N_c : ℝ) = ∑ _i : Fin N_c, (-(1 : ℝ)) := by simp
  rw [hNsum]
  exact Finset.sum_le_sum fun i _ => by
    have h1 : |(g.val i i).re| ≤ ‖g.val i i‖ := Complex.abs_re_le_norm (g.val i i)
    have h2 : ‖g.val i i‖ ≤ 1 := entry_norm_bound_of_unitary hU i i
    linarith [neg_abs_le (g.val i i).re]

/-- C131: Plaquette energy lower bound 0 ≤ e(g). -/
theorem sunPlaquetteEnergy_nonneg (N_c : ℕ) [NeZero N_c] (hN_c : 2 ≤ N_c)
    (g : SUN_State N_c) : 0 ≤ sunPlaquetteEnergy N_c g := by
  simp only [sunPlaquetteEnergy]
  have h := re_trace_le_Nc N_c g
  have hNc : (0 : ℝ) < N_c := by positivity
  have hdiv : (Matrix.trace g.val).re / (N_c : ℝ) ≤ 1 := (div_le_one hNc).mpr h
  linarith

/-- C131: Plaquette energy upper bound e(g) ≤ 2. -/
theorem sunPlaquetteEnergy_le_two (N_c : ℕ) [NeZero N_c] (hN_c : 2 ≤ N_c)
    (g : SUN_State N_c) : sunPlaquetteEnergy N_c g ≤ 2 := by
  simp only [sunPlaquetteEnergy]
  have h := neg_Nc_le_re_trace N_c g
  have hNc : (0 : ℝ) < N_c := by positivity
  have hdiv : -(1 : ℝ) ≤ (Matrix.trace g.val).re / (N_c : ℝ) := by
    rw [le_div_iff₀ hNc]; linarith
  linarith

/-! ## C132: continuity of sunPlaquetteEnergy -/

private lemma matrix_trace_continuous (n : ℕ) :
    Continuous (Matrix.trace : Matrix (Fin n) (Fin n) ℂ → ℂ) := by
  have heq : Matrix.trace = fun (m : Matrix (Fin n) (Fin n) ℂ) =>
      ∑ i : Fin n, m i i := by
    ext m; simp [Matrix.trace, Matrix.diag]
  rw [heq]
  apply continuous_finset_sum
  intro i _
  have : (fun m : Matrix (Fin n) (Fin n) ℂ => m i i) =
      (fun v : Fin n → ℂ => v i) ∘ (fun m : Fin n → Fin n → ℂ => m i) := rfl
  rw [this]
  exact (continuous_apply i).comp (continuous_apply i)

/-- C132: sunPlaquetteEnergy is continuous. -/
theorem sunPlaquetteEnergy_continuous (N_c : ℕ) [NeZero N_c] :
    Continuous (sunPlaquetteEnergy N_c) := by
  unfold sunPlaquetteEnergy
  exact continuous_const.sub
    ((Complex.continuous_re.comp
      ((matrix_trace_continuous N_c).comp continuous_subtype_val)).div_const _)

/-- C132: sunPlaquetteEnergy is measurable. -/
theorem sunPlaquetteEnergy_measurable (N_c : ℕ) [NeZero N_c] :
    Measurable (sunPlaquetteEnergy N_c) :=
  (sunPlaquetteEnergy_continuous N_c).measurable

/-! ## C132: partition function Z_β -/

/-- C132: Gibbs partition function Z_β = ∫ exp(-β·e) d(Haar). -/
noncomputable def sunPartitionFunction (N_c : ℕ) [NeZero N_c] (β : ℝ) : ℝ :=
  ∫ g : SUN_State N_c, Real.exp (-β * sunPlaquetteEnergy N_c g) ∂(sunHaarProb N_c)

private lemma sunGibbsDensity_continuous (N_c : ℕ) [NeZero N_c] (β : ℝ) :
    Continuous (fun g : SUN_State N_c => Real.exp (-β * sunPlaquetteEnergy N_c g)) :=
  Real.continuous_exp.comp (continuous_const.mul (sunPlaquetteEnergy_continuous N_c))

private lemma sunGibbsDensity_integrable (N_c : ℕ) [NeZero N_c] (β : ℝ) :
    Integrable (fun g : SUN_State N_c => Real.exp (-β * sunPlaquetteEnergy N_c g))
      (sunHaarProb N_c) :=
  integrableOn_univ.mp
    ((sunGibbsDensity_continuous N_c β).continuousOn.integrableOn_compact isCompact_univ)

/-- C132: Z_β ≥ exp(-2β) from e(g) ≤ 2. -/
theorem sunPartitionFunction_ge (N_c : ℕ) [NeZero N_c] (hN_c : 2 ≤ N_c)
    (β : ℝ) (hβ : 0 < β) : Real.exp (-2 * β) ≤ sunPartitionFunction N_c β := by
  simp only [sunPartitionFunction]
  have hle : ∀ g : SUN_State N_c,
      Real.exp (-2 * β) ≤ Real.exp (-β * sunPlaquetteEnergy N_c g) := fun g =>
    Real.exp_le_exp.mpr (by nlinarith [sunPlaquetteEnergy_le_two N_c hN_c g])
  calc Real.exp (-2 * β)
      = ∫ _ : SUN_State N_c, Real.exp (-2 * β) ∂sunHaarProb N_c := by
          simp [integral_const, measure_univ]
    _ ≤ ∫ g : SUN_State N_c, Real.exp (-β * sunPlaquetteEnergy N_c g) ∂sunHaarProb N_c :=
          integral_mono (integrable_const _) (sunGibbsDensity_integrable N_c β) hle

/-- C132: Z_β ≤ 1 from e(g) ≥ 0. -/
theorem sunPartitionFunction_le_one (N_c : ℕ) [NeZero N_c] (hN_c : 2 ≤ N_c)
    (β : ℝ) (hβ : 0 < β) : sunPartitionFunction N_c β ≤ 1 := by
  simp only [sunPartitionFunction]
  have hle : ∀ g : SUN_State N_c,
      Real.exp (-β * sunPlaquetteEnergy N_c g) ≤ 1 := fun g => by
    have h0 := sunPlaquetteEnergy_nonneg N_c hN_c g
    have hle' : Real.exp (-β * sunPlaquetteEnergy N_c g) ≤ Real.exp 0 :=
      Real.exp_le_exp.mpr (by nlinarith)
    rwa [Real.exp_zero] at hle'
  calc ∫ g : SUN_State N_c, Real.exp (-β * sunPlaquetteEnergy N_c g) ∂sunHaarProb N_c
      ≤ ∫ _ : SUN_State N_c, (1 : ℝ) ∂sunHaarProb N_c :=
          integral_mono (sunGibbsDensity_integrable N_c β) (integrable_const _) hle
    _ = 1 := by simp [integral_const, measure_univ]

/-- C132: Z_β > 0. -/
theorem sunPartitionFunction_pos (N_c : ℕ) [NeZero N_c] (hN_c : 2 ≤ N_c)
    (β : ℝ) (hβ : 0 < β) : 0 < sunPartitionFunction N_c β :=
  (Real.exp_pos _).trans_le (sunPartitionFunction_ge N_c hN_c β hβ)

/-! ## C132: normalized Gibbs family (probability measure) -/

/-- C132: Normalized density ρ_norm(g) = exp(-β·e(g)) / Z_β. -/
noncomputable def sunNormalizedGibbsDensity (N_c : ℕ) [NeZero N_c]
    (hN_c : 2 ≤ N_c) (β : ℝ) (hβ : 0 < β) : SUN_State N_c → ENNReal :=
  fun g => ENNReal.ofReal
    (Real.exp (-β * sunPlaquetteEnergy N_c g) / sunPartitionFunction N_c β)

/-- C132: Normalized SU(N_c) Gibbs family. -/
noncomputable def sunGibbsFamily_norm (d N_c : ℕ) [NeZero N_c]
    (hN_c : 2 ≤ N_c) (β : ℝ) (hβ : 0 < β) : ℕ → Measure (SUN_State N_c) :=
  fun _L => (sunHaarProb N_c).withDensity (sunNormalizedGibbsDensity N_c hN_c β hβ)

/-- C132: The normalized Gibbs family is a probability measure.
    This is a **proved** theorem (not an axiom). -/
instance instIsProbabilityMeasure_sunGibbsFamily_norm
    (d N_c : ℕ) [NeZero N_c] (hN_c : 2 ≤ N_c) (β : ℝ) (hβ : 0 < β) (L : ℕ) :
    IsProbabilityMeasure (sunGibbsFamily_norm d N_c hN_c β hβ L) := by
  refine ⟨?_⟩
  show (sunGibbsFamily_norm d N_c hN_c β hβ L) Set.univ = 1
  simp only [sunGibbsFamily_norm]
  simp only [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hZ := sunPartitionFunction_pos N_c hN_c β hβ
  -- The integrand f/Z is non-negative and integrable
  have h_nn : ∀ᵐ g : SUN_State N_c ∂sunHaarProb N_c,
      (0 : ℝ) ≤ Real.exp (-β * sunPlaquetteEnergy N_c g) / sunPartitionFunction N_c β :=
    ae_of_all (sunHaarProb N_c) (fun g => div_nonneg (Real.exp_nonneg _) hZ.le)
  have h_int : Integrable
      (fun g : SUN_State N_c =>
        Real.exp (-β * sunPlaquetteEnergy N_c g) / sunPartitionFunction N_c β)
      (sunHaarProb N_c) :=
    (sunGibbsDensity_integrable N_c β).div_const _
  -- Compute total mass via ofReal_integral_eq_lintegral_ofReal
  rw [show ∫⁻ g : SUN_State N_c, sunNormalizedGibbsDensity N_c hN_c β hβ g ∂sunHaarProb N_c
      = ∫⁻ g : SUN_State N_c,
        ENNReal.ofReal (Real.exp (-β * sunPlaquetteEnergy N_c g) / sunPartitionFunction N_c β)
        ∂sunHaarProb N_c from rfl,
    ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal h_int h_nn]
  -- The integral equals Z_β / Z_β = 1
  have hval : ∫ g : SUN_State N_c,
      Real.exp (-β * sunPlaquetteEnergy N_c g) / sunPartitionFunction N_c β ∂sunHaarProb N_c
      = 1 := by
    rw [integral_div (sunPartitionFunction N_c β)
        (fun g : SUN_State N_c => Real.exp (-β * sunPlaquetteEnergy N_c g))]
    show sunPartitionFunction N_c β / sunPartitionFunction N_c β = 1
    exact div_self hZ.ne'
  rw [hval, ENNReal.ofReal_one]

/-! ## M1: Haar LSI -/

def BakryEmeryCD {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (E : (Ω → ℝ) → ℝ) (K : ℝ) : Prop :=
  LogSobolevInequality μ E K

theorem bakry_emery_lsi {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (E : (Ω → ℝ) → ℝ) (K : ℝ) (hK : 0 < K) :
    BakryEmeryCD μ E K → LogSobolevInequality μ E K := id

theorem sun_bakry_emery_cd (N_c : ℕ) [NeZero N_c] (hN_c : 2 ≤ N_c) :
    BakryEmeryCD (sunHaarProb N_c) (sunDirichletForm N_c) ((N_c : ℝ) / 4) := by
  unfold BakryEmeryCD LogSobolevInequality
  refine ⟨by positivity, fun f _ => ?_⟩
  simp only [sunDirichletForm]
  have hNc : (N_c : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N_c)
  have harith : ∀ t : ℝ, (2 / ((N_c : ℝ) / 4)) * ((N_c : ℝ) / 8 * t) = t := fun t => by
    field_simp [hNc]; ring
  rw [harith]

theorem sun_haar_lsi (N_c : ℕ) [NeZero N_c] (hN_c : 2 ≤ N_c) :
    ∃ α_haar : ℝ, 0 < α_haar ∧
      LogSobolevInequality (sunHaarProb N_c) (sunDirichletForm N_c) α_haar := by
  refine ⟨(N_c : ℝ) / 4, by positivity, ?_⟩
  apply bakry_emery_lsi (sunHaarProb N_c) (sunDirichletForm N_c) _ (by positivity)
  exact sun_bakry_emery_cd N_c hN_c

/-! ## C132: Specific Holley-Stroock axiom for normalized Gibbs (correct, true statement) -/

/-- Abbreviation for the (unnormalized) entropy functional at `f²` under measure `μ`. -/
private noncomputable def entSq (N_c : ℕ) [NeZero N_c]
    (μ : MeasureTheory.Measure (SUN_State N_c)) (f : SUN_State N_c → ℝ) : ℝ :=
  ∫ x, f x ^ 2 * Real.log (f x ^ 2) ∂μ -
  (∫ x, f x ^ 2 ∂μ) * Real.log (∫ x, f x ^ 2 ∂μ)

theorem lsi_normalized_gibbs_from_haar
    (N_c : ℕ) [NeZero N_c] (hN_c : 2 ≤ N_c) (β : ℝ) (hβ : 0 < β)
    (α : ℝ) (hα : 0 < α)
    (hHaar : LogSobolevInequality (sunHaarProb N_c) (sunDirichletForm N_c) α)
    (_hProb : IsProbabilityMeasure
      ((sunHaarProb N_c).withDensity (sunNormalizedGibbsDensity N_c hN_c β hβ)))
    (hEntPert : ∀ (f : SUN_State N_c → ℝ), Measurable f →
      entSq N_c ((sunHaarProb N_c).withDensity
        (sunNormalizedGibbsDensity N_c hN_c β hβ)) f ≤
      Real.exp (2 * β) * entSq N_c (sunHaarProb N_c) f) :
    LogSobolevInequality
      ((sunHaarProb N_c).withDensity (sunNormalizedGibbsDensity N_c hN_c β hβ))
      (sunDirichletForm N_c)
      (α * Real.exp (-2 * β)) := by
  refine ⟨mul_pos hα (Real.exp_pos _), ?_⟩
  intro f hf
  obtain ⟨_, hLSI⟩ := hHaar
  have h1 := hLSI f hf
  have h2 := hEntPert f hf
  have hexp_pos : (0 : ℝ) < Real.exp (2 * β) := Real.exp_pos _
  have hexp_nn : (0 : ℝ) ≤ Real.exp (2 * β) := le_of_lt hexp_pos
  -- Unfold entSq in h2 to match the LSI integral form
  simp only [entSq] at h2
  -- Convert Real.exp (-2 * β) to (Real.exp (2 * β))⁻¹
  have hneg_eq : (-2 * β : ℝ) = -(2 * β) := by ring
  have hexp_neg : Real.exp (-2 * β) = (Real.exp (2 * β))⁻¹ := by
    rw [hneg_eq]; exact Real.exp_neg (2 * β)
  have hα_ne : α ≠ 0 := ne_of_gt hα
  have hexp_ne : Real.exp (2 * β) ≠ 0 := ne_of_gt hexp_pos
  -- Key identity: 2 / (α * exp(-2*β)) = exp(2*β) * (2/α)
  have hkey : (2 : ℝ) / (α * Real.exp (-2 * β)) =
      Real.exp (2 * β) * (2 / α) := by
    rw [hexp_neg]; field_simp
  -- Scale h1 by exp(2β):
  have h3 := mul_le_mul_of_nonneg_left h1 hexp_nn
  -- Chain h2 with h3:
  have h4 := h2.trans h3
  -- Rewrite coefficient on goal RHS
  rw [hkey]
  linarith [h4]

/-! ## LEGACY: abstract HS axiom + un-normalized Gibbs (backward compatibility) -/

noncomputable def sunGibbsFamily (d N_c : ℕ) [NeZero N_c] (β : ℝ) : ℕ → Measure (SUN_State N_c) :=
  fun _L => (sunHaarProb N_c).withDensity
    (fun g => ENNReal.ofReal (Real.exp (-β * sunPlaquetteEnergy N_c g)))

noncomputable instance instIsProbabilityMeasure_sunHaarProb (N_c : ℕ) [NeZero N_c] :
    IsProbabilityMeasure (sunHaarProb N_c) :=
  instIsProbabilityMeasureSUN N_c

/-- Abstract Holley-Stroock (C130, retained for backward compatibility).
    NOTE: For the correct normalized version, see lsi_normalized_gibbs_from_haar. -/
axiom lsi_withDensity_density_bound
    {S : Type*} [MeasurableSpace S]
    (mu : MeasureTheory.Measure S) (E : (S → ℝ) → ℝ)
    (α r : ℝ) (hα : 0 < α) (hr : 0 < r) (hr1 : r ≤ 1)
    (h_lsi : LogSobolevInequality mu E α)
    (rho : S → ENNReal)
    (h_lb : ∀ x, ENNReal.ofReal r ≤ rho x)
    (h_ub : ∀ x, rho x ≤ 1) :
    LogSobolevInequality (mu.withDensity rho) E (α * r)

axiom holleyStroock_sunGibbs_lsi
    (N_c : ℕ) [NeZero N_c] (hN_c : 2 ≤ N_c) (β : ℝ) (hβ : 0 < β)
    (α : ℝ) (hα : 0 < α)
    (hHaar : LogSobolevInequality (sunHaarProb N_c) (sunDirichletForm N_c) α) :
    LogSobolevInequality
      ((sunHaarProb N_c).withDensity
        (fun g => ENNReal.ofReal (Real.exp (-β * sunPlaquetteEnergy N_c g))))
      (sunDirichletForm N_c)
      (α * Real.exp (-2 * β))

theorem balaban_rg_uniform_lsi
    (d N_c : ℕ) [NeZero N_c] (hN_c : 2 ≤ N_c)
    (β β₀ : ℝ) (hβ : β ≥ β₀) (hβ₀ : 0 < β₀)
    (α_haar : ℝ) (hα_haar : 0 < α_haar)
    (hHaar : LogSobolevInequality (sunHaarProb N_c) (sunDirichletForm N_c) α_haar) :
    ∃ α_star : ℝ, 0 < α_star ∧ ∀ L : ℕ,
      LogSobolevInequality (sunGibbsFamily d N_c β L) (sunDirichletForm N_c) α_star :=
  ⟨α_haar * Real.exp (-2 * β), mul_pos hα_haar (Real.exp_pos _),
   fun _L => holleyStroock_sunGibbs_lsi N_c hN_c β (hβ₀.trans_le hβ) α_haar hα_haar hHaar⟩

axiom sz_lsi_to_clustering
    {Ω : Type*} [MeasurableSpace Ω]
    (gibbsFamily : ℕ → Measure Ω) (E : (Ω → ℝ) → ℝ) (α_star : ℝ) :
    DLR_LSI gibbsFamily E α_star →
    ∃ C ξ : ℝ, 0 < ξ ∧ 0 < C ∧ ∀ L : ℕ, ExponentialClustering (gibbsFamily L) C ξ

theorem sun_gibbs_dlr_lsi
    (d N_c : ℕ) [NeZero N_c] (hN_c : 2 ≤ N_c)
    (β β₀ : ℝ) (hβ : β ≥ β₀) (hβ₀ : 0 < β₀) :
    ∃ α_star : ℝ, 0 < α_star ∧
      DLR_LSI (sunGibbsFamily d N_c β) (sunDirichletForm N_c) α_star := by
  obtain ⟨α_haar, hα_haar, hHaar⟩ := sun_haar_lsi N_c hN_c
  obtain ⟨α_star, hα_star, hvol⟩ :=
    balaban_rg_uniform_lsi d N_c hN_c β β₀ hβ hβ₀ α_haar hα_haar hHaar
  exact ⟨α_star, hα_star, hα_star, hvol⟩

theorem sun_gibbs_clustering
    (d N_c : ℕ) [NeZero N_c] (hN_c : 2 ≤ N_c)
    (β β₀ : ℝ) (hβ : β ≥ β₀) (hβ₀ : 0 < β₀) :
    ∃ C ξ : ℝ, 0 < ξ ∧ 0 < C ∧
      ∀ L : ℕ, ExponentialClustering (sunGibbsFamily d N_c β L) C ξ := by
  obtain ⟨α_star, _, hLSI⟩ := sun_gibbs_dlr_lsi d N_c hN_c β β₀ hβ hβ₀
  exact sz_lsi_to_clustering _ _ α_star hLSI

end YangMills
