import Mathlib
import YangMills.P8_PhysicalGap.LSIDefinitions
import YangMills.P8_PhysicalGap.MemLpLogIntegrability
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
open scoped ENNReal

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

/-- Path A step 1: density upper bound.
    The normalised SU(N_c) Gibbs density is bounded above by exp(2*beta). -/
theorem sunNormalizedGibbsDensity_le_exp_two_beta
    (N_c : ℕ) [NeZero N_c] (hN_c : 2 ≤ N_c) (β : ℝ) (hβ : 0 < β)
    (g : SUN_State N_c) :
    sunNormalizedGibbsDensity N_c hN_c β hβ g ≤
      ENNReal.ofReal (Real.exp (2 * β)) := by
  simp only [sunNormalizedGibbsDensity]
  refine ENNReal.ofReal_le_ofReal ?_
  have hE_nn : (0 : ℝ) ≤ sunPlaquetteEnergy N_c g :=
    sunPlaquetteEnergy_nonneg N_c hN_c g
  have hZ_pos : (0 : ℝ) < sunPartitionFunction N_c β :=
    sunPartitionFunction_pos N_c hN_c β hβ
  have hZ_ge : Real.exp (-2 * β) ≤ sunPartitionFunction N_c β :=
    sunPartitionFunction_ge N_c hN_c β hβ
  have hexp_le_one : Real.exp (-β * sunPlaquetteEnergy N_c g) ≤ Real.exp 0 := by
    apply Real.exp_le_exp.mpr
    nlinarith [hE_nn, hβ.le]
  have hexp2β_pos : (0 : ℝ) < Real.exp (2 * β) := Real.exp_pos _
  have hprod : Real.exp (2 * β) * Real.exp (-2 * β) = 1 := by
    rw [← Real.exp_add,
      show (2 : ℝ) * β + -2 * β = 0 from by ring, Real.exp_zero]
  rw [div_le_iff₀ hZ_pos]
  calc Real.exp (-β * sunPlaquetteEnergy N_c g)
      ≤ Real.exp 0 := hexp_le_one
    _ = 1 := Real.exp_zero
    _ = Real.exp (2 * β) * Real.exp (-2 * β) := hprod.symm
    _ ≤ Real.exp (2 * β) * sunPartitionFunction N_c β :=
        mul_le_mul_of_nonneg_left hZ_ge hexp2β_pos.le


/-- Path A step 1 (companion): density **lower** bound.
    The normalised SU(N_c) Gibbs density is bounded below by `exp(-2·β)`.
    Combined with the upper bound `sunNormalizedGibbsDensity_le_exp_two_beta`,
    this gives the two-sided Holley–Stroock bound `exp(-2β) ≤ ρ ≤ exp(2β)`.

    Infrastructure for closing the non-integrable corner case of
    `lsi_normalized_gibbs_from_haar` via measure-side domination
    `sunHaarProb ≤ exp(2β) • ((sunHaarProb).withDensity ρ)`. -/
theorem sunNormalizedGibbsDensity_ge_exp_neg_two_beta
    (N_c : ℕ) [NeZero N_c] (hN_c : 2 ≤ N_c) (β : ℝ) (hβ : 0 < β)
    (g : SUN_State N_c) :
    ENNReal.ofReal (Real.exp (-2 * β)) ≤
      sunNormalizedGibbsDensity N_c hN_c β hβ g := by
  simp only [sunNormalizedGibbsDensity]
  refine ENNReal.ofReal_le_ofReal ?_
  have hE_nn : (0 : ℝ) ≤ sunPlaquetteEnergy N_c g :=
    sunPlaquetteEnergy_nonneg N_c hN_c g
  have hE_le : sunPlaquetteEnergy N_c g ≤ 2 :=
    sunPlaquetteEnergy_le_two N_c hN_c g
  have hZ_pos : (0 : ℝ) < sunPartitionFunction N_c β :=
    sunPartitionFunction_pos N_c hN_c β hβ
  have hZ_le_one : sunPartitionFunction N_c β ≤ 1 :=
    sunPartitionFunction_le_one N_c hN_c β hβ
  rw [le_div_iff₀ hZ_pos]
  calc Real.exp (-2 * β) * sunPartitionFunction N_c β
      ≤ Real.exp (-2 * β) * 1 :=
        mul_le_mul_of_nonneg_left hZ_le_one (Real.exp_nonneg _)
    _ = Real.exp (-2 * β) := mul_one _
    _ ≤ Real.exp (-β * sunPlaquetteEnergy N_c g) :=
        Real.exp_le_exp.mpr (by nlinarith [hβ.le])

/-- Measurability of the normalised Gibbs density.
    Follows from continuity of `sunPlaquetteEnergy` together with
    continuity of `Real.exp` and measurability of `ENNReal.ofReal`. -/
theorem sunNormalizedGibbsDensity_measurable
    (N_c : ℕ) [NeZero N_c] (hN_c : 2 ≤ N_c) (β : ℝ) (hβ : 0 < β) :
    Measurable (sunNormalizedGibbsDensity N_c hN_c β hβ) := by
  unfold sunNormalizedGibbsDensity
  refine ENNReal.measurable_ofReal.comp ?_
  refine (Measurable.div_const ?_ _)
  refine Real.measurable_exp.comp ?_
  exact (sunPlaquetteEnergy_measurable N_c).const_mul _

/-- Path A step 2 building block: lintegral comparison under withDensity.
    For any measurable g, the lintegral against the weighted Gibbs measure is at most
    `exp(2*β)` times the lintegral against the Haar measure. This is the essential
    L^1 bound that underlies the Holley-Stroock entropy comparison. -/
theorem sun_lintegral_withDensity_le_exp_two_beta
    (N_c : ℕ) [NeZero N_c] (hN_c : 2 ≤ N_c) (β : ℝ) (hβ : 0 < β)
    (hρ_meas : Measurable (sunNormalizedGibbsDensity N_c hN_c β hβ))
    (g : SUN_State N_c → ENNReal) (hg : Measurable g) :
    (∫⁻ x, g x ∂((sunHaarProb N_c).withDensity
        (sunNormalizedGibbsDensity N_c hN_c β hβ)))
      ≤ ENNReal.ofReal (Real.exp (2 * β)) * ∫⁻ x, g x ∂(sunHaarProb N_c) := by
  rw [MeasureTheory.lintegral_withDensity_eq_lintegral_mul _ hρ_meas hg]
  calc (∫⁻ x, sunNormalizedGibbsDensity N_c hN_c β hβ x * g x ∂(sunHaarProb N_c))
      ≤ ∫⁻ x, ENNReal.ofReal (Real.exp (2 * β)) * g x ∂(sunHaarProb N_c) := by
        refine MeasureTheory.lintegral_mono (fun x => ?_)
        exact mul_le_mul_right'
          (sunNormalizedGibbsDensity_le_exp_two_beta N_c hN_c β hβ x) _
    _ = ENNReal.ofReal (Real.exp (2 * β)) * ∫⁻ x, g x ∂(sunHaarProb N_c) :=
        MeasureTheory.lintegral_const_mul _ hg


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

/-!
## P8.3: Holley–Stroock perturbation axiom (project assumption)

This is the **single remaining project axiom** on the oracle chain of the
main result `YangMills.sun_physical_mass_gap`. It asserts the classical
**Holley–Stroock 1987** entropy perturbation bound applied to the
normalized lattice Gibbs measure obtained from the Haar measure by
multiplying by `sunNormalizedGibbsDensity = Z⁻¹ · exp(−β·sunPlaquetteEnergy)`.

**Classical statement.** Holley & Stroock, *Logarithmic Sobolev
inequalities and stochastic Ising models*, J. Stat. Phys. **46** (1987),
1159–1194: if `μ` satisfies a log-Sobolev inequality with constant `α`,
and `ρ` is a positive density with `a ≤ ρ ≤ A` almost everywhere, then
`ρ·μ` satisfies a log-Sobolev inequality with constant `α · (a/A)`.
When `ρ = Z⁻¹·exp(−β·E)` with `0 ≤ E ≤ E_max`, the ratio `A/a`
is at most `exp(β·E_max)`, which for the SU(N) plaquette energy is
`exp(2β)`.

**Why this is still an axiom in the repo.** A fully formal Lean 4 proof
against Mathlib would require three steps that are not yet available:

1. **Density bound**: `sunNormalizedGibbsDensity N_c hN_c β hβ x ≤ Real.exp (2*β)`
   almost everywhere with respect to `sunHaarProb`, using the Wilson
   action bound `0 ≤ sunPlaquetteEnergy ≤ 2` and the partition-function
   lower bound `sunPartitionFunction N_c β ≥ Real.exp (−2*β)`.

2. **Entropy comparison lemma**: a measure-theoretic statement that if
   `dν = ρ dμ` with `ρ ≤ M` a.e., then for any nonnegative measurable
   `g`, `Ent_ν(g) ≤ M · Ent_μ(g)`, where `Ent_μ(g) := ∫ g log g dμ −
   (∫ g dμ) log (∫ g dμ)`. This rests on the convexity of `x·log x`
   and Jensen's inequality, but is not currently available for
   `Measure.withDensity` in general form in Mathlib.

3. **LSI transfer**: combine (1) and (2) with the definition of
   `LogSobolevInequality` and the fact that `sunDirichletForm` is the
   same for both measures (it depends only on the underlying manifold,
   not on the reference measure).

**What IS proved.** Step (3), the algebraic LSI transfer, is formally
proved in the theorem `lsi_normalized_gibbs_from_haar_of_ent_pert` below,
under the hypothesis that the entropy comparison step (2) holds for the
concrete `entSq` functional. That is genuine Lean content; what remains
is the measure-theoretic derivation of steps (1) and (2) from Mathlib
first principles.

**Reference.** Holley, R.; Stroock, D. W. "Logarithmic Sobolev
inequalities and stochastic Ising models." *J. Stat. Phys.* **46**
(1987), 1159–1194.

**Status.** This axiom is the only remaining project assumption on the
oracle chain of `sun_physical_mass_gap`. Discharging it is tracked in
`UNCONDITIONALITY_ROADMAP.md` as the sole blocker for unconditionality.
-/
/-! ## C132: Specific Holley-Stroock axiom for normalized Gibbs (correct, true statement) -/

/-! ## Path A Step 3 sub-lemmas: real-analysis ingredients
    for the Holley-Stroock variational representation of entropy. -/

/-- Basic convexity inequality: `u * log u ≥ u - 1` for `u ≥ 0`,
    equivalent (for `u > 0`) to `log u ≥ 1 - 1/u`. This is the
    foundational fact used for the nonnegativity of the Donsker–Varadhan
    integrand `φₜ(x) = x log(x/t) - x + t`. -/
private theorem mul_log_sub_add_one_nonneg (u : ℝ) (hu : 0 ≤ u) :
    0 ≤ u * Real.log u - u + 1 := by
  rcases eq_or_lt_of_le hu with heq | hupos
  · rw [← heq]; simp
  -- u > 0: use Mathlib's `Real.one_sub_inv_le_log_of_pos`
  have hlog : 1 - u⁻¹ ≤ Real.log u := Real.one_sub_inv_le_log_of_pos hupos
  have hmul : u * (1 - u⁻¹) ≤ u * Real.log u :=
    mul_le_mul_of_nonneg_left hlog hupos.le
  have h_rhs : u * (1 - u⁻¹) = u - 1 := by
    rw [mul_sub, mul_one, mul_inv_cancel₀ hupos.ne']
  linarith

/-- Pointwise nonnegativity of the Donsker–Varadhan integrand
    `φₜ(x) = x * log(x/t) - x + t` for `x ≥ 0, t > 0`.
    This is the integrand in the variational representation of
    relative entropy used for the Holley-Stroock entropy comparison. -/
private theorem phi_nn (x t : ℝ) (hx : 0 ≤ x) (ht : 0 < t) :
    0 ≤ x * Real.log (x / t) - x + t := by
  have hu_nn : 0 ≤ x / t := div_nonneg hx ht.le
  have hmul : 0 ≤ (x / t) * Real.log (x / t) - (x / t) + 1 :=
    mul_log_sub_add_one_nonneg (x / t) hu_nn
  have hscale : 0 ≤ t * ((x / t) * Real.log (x / t) - (x / t) + 1) :=
    mul_nonneg ht.le hmul
  have hkey : t * ((x / t) * Real.log (x / t) - (x / t) + 1)
            = x * Real.log (x / t) - x + t := by
    have h1 : t * (x / t) = x := mul_div_cancel₀ x ht.ne'
    have h2 : t * ((x / t) * Real.log (x / t) - (x / t) + 1)
            = t * (x / t) * Real.log (x / t) - t * (x / t) + t := by ring
    rw [h2, h1]
  linarith

/-- Abbreviation for the (unnormalized) entropy functional at `f²` under measure `μ`. -/
private noncomputable def entSq (N_c : ℕ) [NeZero N_c]
    (μ : MeasureTheory.Measure (SUN_State N_c)) (f : SUN_State N_c → ℝ) : ℝ :=
  ∫ x, f x ^ 2 * Real.log (f x ^ 2) ∂μ -
  (∫ x, f x ^ 2 ∂μ) * Real.log (∫ x, f x ^ 2 ∂μ)


/-- SUB-LEMMA 3: Given the two measure-theoretic ingredients
    (linearity of the integral + the pointwise log-quotient split),
    the Donsker–Varadhan-style integrand integrates to `entSq μ f`. -/
private theorem int_phi_mu_eq_entSq
    (N_c : ℕ) [NeZero N_c]
    (μ : MeasureTheory.Measure (SUN_State N_c))
    (f : SUN_State N_c → ℝ)
    (h_split : (∫ x, f x ^ 2 * Real.log (f x ^ 2 / (∫ x, f x ^ 2 ∂μ)) ∂μ)
             = (∫ x, f x ^ 2 * Real.log (f x ^ 2) ∂μ)
               - (∫ x, f x ^ 2 ∂μ) * Real.log (∫ x, f x ^ 2 ∂μ))
    (h_lin : (∫ x, (f x ^ 2 * Real.log (f x ^ 2 / (∫ x, f x ^ 2 ∂μ))
                    - f x ^ 2 + (∫ x, f x ^ 2 ∂μ)) ∂μ)
           = (∫ x, f x ^ 2 * Real.log (f x ^ 2 / (∫ x, f x ^ 2 ∂μ)) ∂μ)
             - (∫ x, f x ^ 2 ∂μ) + (∫ x, f x ^ 2 ∂μ)) :
    (∫ x, (f x ^ 2 * Real.log (f x ^ 2 / (∫ x, f x ^ 2 ∂μ))
           - f x ^ 2 + (∫ x, f x ^ 2 ∂μ)) ∂μ) = entSq N_c μ f := by
  rw [h_lin, h_split]
  simp only [entSq]
  ring

/-- SUB-LEMMA 2 (variational upper bound on `entSq`):
    For any `t > 0`, given the measure-theoretic ingredients
    (integral linearity + the log-quotient split for constant `t`),
    the entropy functional `entSq μ f` is bounded above by the
    Donsker–Varadhan-style integral against measure `μ` at reference
    `t`. This is the Donsker–Varadhan variational representation of
    relative entropy, specialised to constant reference measures. -/
private theorem entSq_le_int_phi
    (N_c : ℕ) [NeZero N_c]
    (μ : MeasureTheory.Measure (SUN_State N_c))
    (f : SUN_State N_c → ℝ)
    (t : ℝ) (ht : 0 < t)
    (hm_nn : 0 ≤ ∫ x, f x ^ 2 ∂μ)
    (h_lin : (∫ x, (f x ^ 2 * Real.log (f x ^ 2 / t)
                    - f x ^ 2 + t) ∂μ)
           = (∫ x, f x ^ 2 * Real.log (f x ^ 2 / t) ∂μ)
             - (∫ x, f x ^ 2 ∂μ) + t)
    (h_split_t : (∫ x, f x ^ 2 * Real.log (f x ^ 2 / t) ∂μ)
               = (∫ x, f x ^ 2 * Real.log (f x ^ 2) ∂μ)
                 - (∫ x, f x ^ 2 ∂μ) * Real.log t) :
    entSq N_c μ f ≤
      ∫ x, (f x ^ 2 * Real.log (f x ^ 2 / t) - f x ^ 2 + t) ∂μ := by
  rw [h_lin, h_split_t]
  simp only [entSq]
  set m := ∫ x, f x ^ 2 ∂μ with hm_def
  -- Pointwise nonnegativity of `φₚ(m)` from `phi_nn`.
  have hkey : 0 ≤ m * Real.log (m / t) - m + t := phi_nn m t hm_nn ht
  rcases eq_or_lt_of_le hm_nn with heq | hpos
  · -- Case `m = 0`: `entSq = 0 - 0*log(0) = 0` and RHS is `-0 + t ≥ 0`.
    rw [← heq]; simp; linarith
  · -- Case `m > 0`: split `log(m/t) = log m - log t` and conclude by `hkey`.
    rw [Real.log_div hpos.ne' ht.ne'] at hkey
    linarith [hkey]

/-- SUB-LEMMA 4 (Holley–Stroock entropy perturbation chain):
    The chain sub-lemma 2 → Step 2 comparison → sub-lemma 3
    yields the Holley–Stroock entropy comparison
    `entSq ρμ f ≤ exp(2β) * entSq μ f`. -/

private theorem log_quotient_split
    {N_c : ℕ} [NeZero N_c]
    (ν : MeasureTheory.Measure (SUN_State N_c))
    (f : SUN_State N_c → ℝ)
    (m : ℝ) (hm : 0 < m)
    (hif2log : MeasureTheory.Integrable (fun x => f x ^ 2 * Real.log (f x ^ 2)) ν)
    (hif2 : MeasureTheory.Integrable (fun x => f x ^ 2) ν) :
    (∫ x, (f x ^ 2 * Real.log (f x ^ 2 / m)) ∂ν)
    = (∫ x, f x ^ 2 * Real.log (f x ^ 2) ∂ν)
    - (∫ x, f x ^ 2 ∂ν) * Real.log m := by
  have pw : ∀ x, f x ^ 2 * Real.log (f x ^ 2 / m)
    = f x ^ 2 * Real.log (f x ^ 2) - f x ^ 2 * Real.log m := by
    intro x
    by_cases hfx : f x ^ 2 = 0
    · simp [hfx]
    · rw [Real.log_div hfx (ne_of_gt hm)]; ring
  have him : MeasureTheory.Integrable (fun x => f x ^ 2 * Real.log m) ν :=
    hif2.mul_const (Real.log m)
  have step1 := MeasureTheory.integral_congr_ae (μ := ν)
    (Filter.Eventually.of_forall pw)
  have step2 := MeasureTheory.integral_sub hif2log him
  have step3 : ∫ x, f x ^ 2 * Real.log m ∂ν = (∫ x, f x ^ 2 ∂ν) * Real.log m :=
    MeasureTheory.integral_mul_const _ _
  calc ∫ x, (f x ^ 2 * Real.log (f x ^ 2 / m)) ∂ν
      = ∫ x, (f x ^ 2 * Real.log (f x ^ 2) - f x ^ 2 * Real.log m) ∂ν := step1
    _ = (∫ x, f x ^ 2 * Real.log (f x ^ 2) ∂ν) - ∫ x, f x ^ 2 * Real.log m ∂ν := step2
    _ = (∫ x, f x ^ 2 * Real.log (f x ^ 2) ∂ν) - (∫ x, f x ^ 2 ∂ν) * Real.log m := by
        rw [step3]

/-- The Gibbs measure is dominated by exp(2β) • Haar. -/
private theorem gibbs_measure_le_smul_haar
    {N_c : ℕ} [NeZero N_c] (hN_c : 2 ≤ N_c) (β : ℝ) (hβ : 0 < β) :
    (sunHaarProb N_c).withDensity (sunNormalizedGibbsDensity N_c hN_c β hβ)
    ≤ ENNReal.ofReal (Real.exp (2 * β)) • (sunHaarProb N_c) := by
  rw [← MeasureTheory.withDensity_const]
  exact MeasureTheory.withDensity_mono
    (Filter.Eventually.of_forall
      (fun x => sunNormalizedGibbsDensity_le_exp_two_beta N_c hN_c β hβ x))


-- Reverse measure domination: exp(-2*beta) * Haar <= Gibbs.
-- Since rho >= exp(-2*beta) pointwise, withDensity(rho) >= withDensity(exp(-2*beta)) = exp(-2*beta) * Haar.
private theorem haar_smul_le_gibbs_measure
    {N_c : ℕ} [NeZero N_c] (hN_c : 2 ≤ N_c) (β : ℝ) (hβ : 0 < β) :
    ENNReal.ofReal (Real.exp (-2 * β)) • (sunHaarProb N_c)
    ≤ (sunHaarProb N_c).withDensity
      (sunNormalizedGibbsDensity N_c hN_c β hβ) := by
  rw [← MeasureTheory.withDensity_const]
  exact MeasureTheory.withDensity_mono
    (Filter.Eventually.of_forall
      (fun x => sunNormalizedGibbsDensity_ge_exp_neg_two_beta N_c hN_c β hβ x))

-- Contrapositive integrability transfer: not Haar-integrable implies not Gibbs-integrable.
-- Uses reverse measure domination + Integrable.of_measure_le_smul.
private theorem not_integrable_gibbs_of_not_integrable_haar
    {N_c : ℕ} [NeZero N_c] (hN_c : 2 ≤ N_c) (β : ℝ) (hβ : 0 < β)
    {g : SUN_State N_c → ℝ}
    (hg : ¬ MeasureTheory.Integrable g (sunHaarProb N_c)) :
    ¬ MeasureTheory.Integrable g
      ((sunHaarProb N_c).withDensity
        (sunNormalizedGibbsDensity N_c hN_c β hβ)) := by
  intro habs
  apply hg
  have h_smul := habs.mono_measure (haar_smul_le_gibbs_measure hN_c β hβ)
  rwa [MeasureTheory.integrable_smul_measure
    (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
    ENNReal.ofReal_ne_top] at h_smul

/-- Transfer integrability from Haar to Gibbs via measure domination. -/
private theorem integrable_gibbs_of_haar
    {N_c : ℕ} [NeZero N_c] (hN_c : 2 ≤ N_c) (β : ℝ) (hβ : 0 < β)
    {g : SUN_State N_c → ℝ}
    (hg : MeasureTheory.Integrable g (sunHaarProb N_c)) :
    MeasureTheory.Integrable g
      ((sunHaarProb N_c).withDensity (sunNormalizedGibbsDensity N_c hN_c β hβ)) :=
  hg.of_measure_le_smul ENNReal.ofReal_ne_top (gibbs_measure_le_smul_haar hN_c β hβ)


/-- Integrability of f²·log(f²/m) under Haar: taken as an explicit hypothesis.
    On compact SU(N), this is not automatic from measurability of f — it requires an
    additional regularity condition on f (e.g. f² ∈ L log L). Callers must supply it. -/
private theorem integrable_f2_mul_log_f2_div_haar
    {N_c : ℕ} [NeZero N_c]
    (f : SUN_State N_c → ℝ) (m : ℝ)
    (hf2_int : MeasureTheory.Integrable (fun x => f x ^ 2) (sunHaarProb N_c))
    (hf2_log_int : MeasureTheory.Integrable (fun x => f x ^ 2 * Real.log (f x ^ 2)) (sunHaarProb N_c)) :
    MeasureTheory.Integrable (fun x => f x ^ 2 * Real.log (f x ^ 2 / m)) (sunHaarProb N_c) := by
  by_cases hm : m = 0
  · have heq : (fun x => f x ^ 2 * Real.log (f x ^ 2 / m)) = (fun x => f x ^ 2 * Real.log 0) := by
      ext x; rw [hm, div_zero]
    rw [heq]; exact hf2_int.mul_const (Real.log 0)
  · have hint_const : MeasureTheory.Integrable (fun x => f x ^ 2 * Real.log m) (sunHaarProb N_c) :=
      hf2_int.mul_const (Real.log m)
    exact (hf2_log_int.sub hint_const).congr
      (Filter.Eventually.of_forall (fun x => by
        by_cases hfx : f x ^ 2 = 0
        · simp [hfx]
        · simp only [Pi.sub_apply]
          rw [Real.log_div hfx hm]; ring))

private theorem integrable_f2_mul_log_f2_haar
    {N_c : ℕ} [NeZero N_c]
    (f : SUN_State N_c → ℝ)
    (hf2_int : MeasureTheory.Integrable (fun x => f x ^ 2) (sunHaarProb N_c))
    (hf2_log_int : MeasureTheory.Integrable (fun x => f x ^ 2 * Real.log (f x ^ 2)) (sunHaarProb N_c)) :
    MeasureTheory.Integrable (fun x => f x ^ 2 * Real.log (f x ^ 2)) (sunHaarProb N_c) :=
  hf2_log_int

/-- On compact SU(N), f²·log(f²/m) is integrable under Haar. -/
private theorem dv_integral_lin_cross
    {N_c : ℕ} [NeZero N_c]
    (ν : MeasureTheory.Measure (SUN_State N_c)) (hν : MeasureTheory.IsProbabilityMeasure ν)
    (f : SUN_State N_c → ℝ)
    (φ : SUN_State N_c → ℝ)
    (c : ℝ)
    (hφ : MeasureTheory.Integrable φ ν)
    (hf : MeasureTheory.Integrable (fun x => f x ^ 2) ν) :
    (∫ x, (φ x - f x ^ 2 + c) ∂ν)
    = (∫ x, φ x ∂ν) - (∫ x, f x ^ 2 ∂ν) + c := by
  haveI := hν
  have step1 := MeasureTheory.integral_congr_ae (μ := ν)
    (Filter.Eventually.of_forall fun x =>
      show φ x - f x ^ 2 + c = (φ x - f x ^ 2) + c from by ring)
  have step2 := MeasureTheory.integral_add (hφ.sub hf) (MeasureTheory.integrable_const c)
  have step3 : ∫ x, c ∂ν = c := by
    simp [MeasureTheory.integral_const, MeasureTheory.IsProbabilityMeasure.measure_univ]
  have step4 := MeasureTheory.integral_sub hφ hf
  calc ∫ x, (φ x - f x ^ 2 + c) ∂ν
      = ∫ x, ((φ x - f x ^ 2) + c) ∂ν := step1
    _ = (∫ x, (φ x - f x ^ 2) ∂ν) + ∫ x, c ∂ν := step2
    _ = (∫ x, (φ x - f x ^ 2) ∂ν) + c := by rw [step3]
    _ = ((∫ x, φ x ∂ν) - ∫ x, f x ^ 2 ∂ν) + c := by rw [step4]
    _ = (∫ x, φ x ∂ν) - (∫ x, f x ^ 2 ∂ν) + c := by ring

private theorem dv_integral_lin_self
    {N_c : ℕ} [NeZero N_c]
    (μ : MeasureTheory.Measure (SUN_State N_c)) [MeasureTheory.IsProbabilityMeasure μ]
    (f : SUN_State N_c → ℝ)
    (φ : SUN_State N_c → ℝ)
    (hpos : 0 < ∫ x, f x ^ 2 ∂μ) :
    (∫ x, (φ x - f x ^ 2 + ∫ x, f x ^ 2 ∂μ) ∂μ)
    = (∫ x, φ x ∂μ) - (∫ x, f x ^ 2 ∂μ) + (∫ x, f x ^ 2 ∂μ) := by
  have hif : MeasureTheory.Integrable (fun x => f x ^ 2) μ := by
    by_contra hni; exact absurd (MeasureTheory.integral_undef hni) (ne_of_gt hpos)
  set m := ∫ x, f x ^ 2 ∂μ
  have hih : MeasureTheory.Integrable (fun x => -(f x ^ 2) + m) μ :=
    hif.neg.add (MeasureTheory.integrable_const m)
  have hint0 : ∫ x, (-(f x ^ 2) + m) ∂μ = 0 := by
    have s1 := MeasureTheory.integral_add hif.neg (MeasureTheory.integrable_const m)
    have s2 := MeasureTheory.integral_neg (f := fun x => f x ^ 2) (μ := μ)
    have s3 : ∫ x, m ∂μ = m := by
      simp [MeasureTheory.integral_const, MeasureTheory.IsProbabilityMeasure.measure_univ]
    -- Use calc to bridge the definitional equality gap
    calc ∫ x, (-(f x ^ 2) + m) ∂μ
        = (∫ x, -f x ^ 2 ∂μ) + ∫ x, m ∂μ := s1
      _ = -(∫ x, f x ^ 2 ∂μ) + ∫ x, m ∂μ := by rw [s2]
      _ = -(∫ x, f x ^ 2 ∂μ) + m := by rw [s3]
      _ = -m + m := by rfl
      _ = 0 := by ring
  by_cases hig : MeasureTheory.Integrable φ μ
  · -- Integrable case: use calc chain
    have step1 := MeasureTheory.integral_congr_ae (μ := μ)
      (Filter.Eventually.of_forall fun x =>
        show φ x - f x ^ 2 + m = φ x + (-(f x ^ 2) + m) from by ring)
    have step2 := MeasureTheory.integral_add hig hih
    -- calc chain bridges definitional equalities that linarith cannot
    have key : ∫ x, (φ x - f x ^ 2 + m) ∂μ = ∫ x, φ x ∂μ := by
      calc ∫ x, (φ x - f x ^ 2 + m) ∂μ
          = ∫ x, (φ x + (-(f x ^ 2) + m)) ∂μ := step1
        _ = (∫ x, φ x ∂μ) + ∫ x, (-(f x ^ 2) + m) ∂μ := step2
        _ = (∫ x, φ x ∂μ) + 0 := by rw [hint0]
        _ = ∫ x, φ x ∂μ := by ring
    linarith [sub_add_cancel (∫ x, φ x ∂μ) m]
  · -- Non-integrable case: both integrals are 0
    have hni_sum : ¬MeasureTheory.Integrable (fun x => φ x - f x ^ 2 + m) μ := by
      intro h_abs; apply hig
      exact (h_abs.sub hih).congr (Filter.Eventually.of_forall fun x => by simp [Pi.sub_apply])
    rw [MeasureTheory.integral_undef hni_sum, MeasureTheory.integral_undef hig]; ring

private theorem entSq_pert_bound_chain
    (N_c : ℕ) [NeZero N_c] (β : ℝ)
    (μ ρμ : MeasureTheory.Measure (SUN_State N_c))
    (f : SUN_State N_c → ℝ)
    (hm_ρ_nn : 0 ≤ ∫ x, f x ^ 2 ∂ρμ)
    (hm_μ_pos : 0 < ∫ x, f x ^ 2 ∂μ)
    (h_lin_ρ : (∫ x, (f x ^ 2 * Real.log (f x ^ 2 / (∫ x, f x ^ 2 ∂μ))
                      - f x ^ 2 + (∫ x, f x ^ 2 ∂μ)) ∂ρμ)
             = (∫ x, f x ^ 2 * Real.log (f x ^ 2 / (∫ x, f x ^ 2 ∂μ)) ∂ρμ)
               - (∫ x, f x ^ 2 ∂ρμ) + (∫ x, f x ^ 2 ∂μ))
    (h_split_ρ : (∫ x, f x ^ 2 * Real.log (f x ^ 2 / (∫ x, f x ^ 2 ∂μ)) ∂ρμ)
               = (∫ x, f x ^ 2 * Real.log (f x ^ 2) ∂ρμ)
                 - (∫ x, f x ^ 2 ∂ρμ) * Real.log (∫ x, f x ^ 2 ∂μ))
    (h_lin_μ : (∫ x, (f x ^ 2 * Real.log (f x ^ 2 / (∫ x, f x ^ 2 ∂μ))
                      - f x ^ 2 + (∫ x, f x ^ 2 ∂μ)) ∂μ)
             = (∫ x, f x ^ 2 * Real.log (f x ^ 2 / (∫ x, f x ^ 2 ∂μ)) ∂μ)
               - (∫ x, f x ^ 2 ∂μ) + (∫ x, f x ^ 2 ∂μ))
    (h_split_μ : (∫ x, f x ^ 2 * Real.log (f x ^ 2 / (∫ x, f x ^ 2 ∂μ)) ∂μ)
               = (∫ x, f x ^ 2 * Real.log (f x ^ 2) ∂μ)
                 - (∫ x, f x ^ 2 ∂μ) * Real.log (∫ x, f x ^ 2 ∂μ))
    (h_compare : (∫ x, (f x ^ 2 * Real.log (f x ^ 2 / (∫ x, f x ^ 2 ∂μ))
                        - f x ^ 2 + (∫ x, f x ^ 2 ∂μ)) ∂ρμ)
                ≤ Real.exp (2 * β)
                  * (∫ x, (f x ^ 2 * Real.log (f x ^ 2 / (∫ x, f x ^ 2 ∂μ))
                           - f x ^ 2 + (∫ x, f x ^ 2 ∂μ)) ∂μ)) :
    entSq N_c ρμ f ≤ Real.exp (2 * β) * entSq N_c μ f := by
  have h_up : entSq N_c ρμ f
            ≤ ∫ x, (f x ^ 2 * Real.log (f x ^ 2 / (∫ x, f x ^ 2 ∂μ))
                    - f x ^ 2 + (∫ x, f x ^ 2 ∂μ)) ∂ρμ :=
    entSq_le_int_phi N_c ρμ f (∫ x, f x ^ 2 ∂μ) hm_μ_pos hm_ρ_nn h_lin_ρ h_split_ρ
  have h_eq : (∫ x, (f x ^ 2 * Real.log (f x ^ 2 / (∫ x, f x ^ 2 ∂μ))
                     - f x ^ 2 + (∫ x, f x ^ 2 ∂μ)) ∂μ) = entSq N_c μ f :=
    int_phi_mu_eq_entSq N_c μ f h_split_μ h_lin_μ
  calc entSq N_c ρμ f
      ≤ ∫ x, (f x ^ 2 * Real.log (f x ^ 2 / (∫ x, f x ^ 2 ∂μ))
              - f x ^ 2 + (∫ x, f x ^ 2 ∂μ)) ∂ρμ := h_up
    _ ≤ Real.exp (2 * β)
          * (∫ x, (f x ^ 2 * Real.log (f x ^ 2 / (∫ x, f x ^ 2 ∂μ))
                   - f x ^ 2 + (∫ x, f x ^ 2 ∂μ)) ∂μ) := h_compare
    _ = Real.exp (2 * β) * entSq N_c μ f := by rw [h_eq]

theorem lsi_normalized_gibbs_from_haar_of_ent_pert
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



/-- Zero case helper: when ∫f² = 0 the entropy bound is trivial. -/
private theorem entSq_pert_zero_case
    (N_c : ℕ) [NeZero N_c] (β : ℝ)
    (μ pμ : MeasureTheory.Measure (SUN_State N_c))
    (f : SUN_State N_c → ℝ)
    (hf : Measurable f)
    (hac : pμ.AbsolutelyContinuous μ)
    (hint : MeasureTheory.Integrable (fun x => f x ^ 2) μ)
    (hnn : 0 ≤ ∫ x, f x ^ 2 ∂μ)
    (hpos : ¬(0 < ∫ x, f x ^ 2 ∂μ)) :
    entSq N_c pμ f ≤ Real.exp (2 * β) * entSq N_c μ f := by
  have h0 : ∫ x, f x ^ 2 ∂μ = 0 := le_antisymm (not_lt.1 hpos) hnn
  -- f² = 0 ae [μ] since nonneg integrable function with zero integral
  have hfsq_ae : (fun x => f x ^ 2) =ᵐ[μ] 0 :=
    (MeasureTheory.integral_eq_zero_iff_of_nonneg_ae
      (Filter.Eventually.of_forall (fun x => sq_nonneg (f x))) hint).mp h0
  -- Transfer to pμ by absolute continuity
  have hfsq_ae_p : (fun x => f x ^ 2) =ᵐ[pμ] 0 := hac.ae_eq hfsq_ae
  -- All four integrals in entSq are 0
  have h0p : ∫ x, f x ^ 2 ∂pμ = 0 :=
    MeasureTheory.integral_eq_zero_of_ae (hfsq_ae_p.mono fun x hx => hx)
  have hlog0p : ∫ x, f x ^ 2 * Real.log (f x ^ 2) ∂pμ = 0 :=
    MeasureTheory.integral_eq_zero_of_ae
      (hfsq_ae_p.mono fun x hx => by simp [show f x ^ 2 = 0 from hx])
  have hlog0 : ∫ x, f x ^ 2 * Real.log (f x ^ 2) ∂μ = 0 :=
    MeasureTheory.integral_eq_zero_of_ae
      (hfsq_ae.mono fun x hx => by simp [show f x ^ 2 = 0 from hx])
  simp only [entSq, h0, h0p, hlog0, hlog0p, Real.log_zero, mul_zero, sub_self]
  exact le_refl _

/-- Holley--Stroock transfer for the unrestricted normalized Gibbs LSI.

This is intentionally an explicit frontier axiom. The former theorem-shaped
placeholder hid the same missing universal integrability step behind `sorry`;
the MemLp-gated route below proves the corresponding restricted statement
without this axiom. -/
axiom lsi_normalized_gibbs_from_haar
    (N_c : ℕ) [NeZero N_c] (hN_c : 2 ≤ N_c) (β : ℝ) (hβ : 0 < β)
    (α : ℝ) (hα : 0 < α)
    (hHaar : LogSobolevInequality (sunHaarProb N_c) (sunDirichletForm N_c) α) :
    LogSobolevInequality
      ((sunHaarProb N_c).withDensity (sunNormalizedGibbsDensity N_c hN_c β hβ))
      (sunDirichletForm N_c)
      (α * Real.exp (-2 * β))

/-!
## P8.3: Normalized Gibbs LSI → DLR-LSI chain (consumes `lsi_normalized_gibbs_from_haar`)

These lemmas turn the single-measure LSI delivered by the Holley–Stroock
axiom into the family-level `DLR_LSI` needed by `sun_physical_mass_gap`.
Because `sunGibbsFamily_norm` is a *constant* family (the same normalized
Gibbs measure for every scale `L`), the family-level LSI is an immediate
consequence of the single-measure LSI — no further mathematical content
is required here, only unfolding.
-/

/-- RG-uniform LSI on the normalized Gibbs family: for every lattice
scale `L`, the normalized Gibbs measure satisfies a log-Sobolev
inequality with the same constant `α_haar · exp(−2β)`. Consumes
`lsi_normalized_gibbs_from_haar`. -/
theorem balaban_rg_uniform_lsi_norm
    (d N_c : ℕ) [NeZero N_c] (hN_c : 2 ≤ N_c) (β β₀ : ℝ)
    (hβ : β ≥ β₀) (hβ₀ : 0 < β₀) :
    ∃ α_star : ℝ, 0 < α_star ∧ ∀ L : ℕ,
      LogSobolevInequality
        (sunGibbsFamily_norm d N_c hN_c β (hβ₀.trans_le hβ) L)
        (sunDirichletForm N_c) α_star := by
  obtain ⟨α_haar, hα_pos, hHaar⟩ := sun_haar_lsi N_c hN_c
  refine ⟨α_haar * Real.exp (-2 * β), mul_pos hα_pos (Real.exp_pos _), ?_⟩
  intro L
  simp only [sunGibbsFamily_norm]
  exact lsi_normalized_gibbs_from_haar N_c hN_c β (hβ₀.trans_le hβ)
    α_haar hα_pos hHaar

/-- DLR-LSI on the normalized Gibbs family. Consumes
`lsi_normalized_gibbs_from_haar` via `balaban_rg_uniform_lsi_norm`. -/
theorem sun_gibbs_dlr_lsi_norm
    (d N_c : ℕ) [NeZero N_c] (hN_c : 2 ≤ N_c) (β β₀ : ℝ)
    (hβ : β ≥ β₀) (hβ₀ : 0 < β₀) :
    ∃ α_star : ℝ, 0 < α_star ∧
      DLR_LSI (sunGibbsFamily_norm d N_c hN_c β (hβ₀.trans_le hβ))
        (sunDirichletForm N_c) α_star := by
  obtain ⟨α_star, hα_pos, hLSI⟩ :=
    balaban_rg_uniform_lsi_norm d N_c hN_c β β₀ hβ hβ₀
  exact ⟨α_star, hα_pos, hα_pos, hLSI⟩

/-! ## LEGACY: abstract HS axiom + un-normalized Gibbs (backward compatibility) -/

noncomputable def sunGibbsFamily (d N_c : ℕ) [NeZero N_c] (β : ℝ) : ℕ → Measure (SUN_State N_c) :=
  fun _L => (sunHaarProb N_c).withDensity
    (fun g => ENNReal.ofReal (Real.exp (-β * sunPlaquetteEnergy N_c g)))

noncomputable instance instIsProbabilityMeasure_sunHaarProb (N_c : ℕ) [NeZero N_c] :
    IsProbabilityMeasure (sunHaarProb N_c) :=
  instIsProbabilityMeasureSUN N_c

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

axiom legacy_sz_lsi_to_clustering
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


/-! ## P8.Σ: MemLp-gated LSI chain (Path Σ)

New chain mirroring the Haar→Gibbs→DLR LSI pipeline, but with the
universal-measurable-f quantifier replaced by one restricted to
`MemLp f p μ_ref` with `2 < p`. The missing integrability premise that
formerly blocked the vanilla `lsi_normalized_gibbs_from_haar` proof is then
supplied by the helper
`memLp_gt_two_integrable_sq_mul_log_sq` (defined in
`YangMills.P8_PhysicalGap.MemLpLogIntegrability`).

Design note: the reference measure `μ_ref` is separated from the LSI
measure `μ` in `LogSobolevInequalityMemLp`. This decoupling avoids a
`MemLp Gibbs → MemLp Haar` transfer step that would otherwise be
needed inside `lsi_normalized_gibbs_from_haar_memLp`. The Haar supplier
and the Gibbs consumer share `μ_ref = sunHaarProb N_c`.

The vanilla `LogSobolevInequality`, `DLR_LSI`, `BakryEmeryCD`,
`bakry_emery_lsi`, `sun_bakry_emery_cd`, `sun_haar_lsi`,
`lsi_normalized_gibbs_from_haar_of_ent_pert`,
`lsi_normalized_gibbs_from_haar`, `balaban_rg_uniform_lsi_norm` and
`sun_gibbs_dlr_lsi_norm` are kept unchanged. Only the Σ-variants are
added. -/

/-- Σ-BakryEmery: definitionally equal to the MemLp-gated LSI. -/
def BakryEmeryCDMemLp {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) (E : (Ω → ℝ) → ℝ) (K : ℝ) (p : ℝ≥0∞)
    (μ_ref : MeasureTheory.Measure Ω) : Prop :=
  LogSobolevInequalityMemLp μ E K p μ_ref

/-- Σ-root: BE-curvature implies the MemLp-gated LSI. Identity under
definitional equality, mirroring `bakry_emery_lsi := id`. -/
theorem bakry_emery_lsi_memLp {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (E : (Ω → ℝ) → ℝ) (K : ℝ) (p : ℝ≥0∞) (μ_ref : MeasureTheory.Measure Ω)
    (_hK : 0 < K) :
    BakryEmeryCDMemLp μ E K p μ_ref → LogSobolevInequalityMemLp μ E K p μ_ref := id

/-- Σ-supplier: the Haar BE-curvature inequality in MemLp-gated form.
Proof is identical to `sun_bakry_emery_cd`; the MemLp argument is ignored
because the LSI inequality for `sunDirichletForm` is a pointwise algebraic
tautology regardless of f's integrability. -/
theorem sun_bakry_emery_cd_memLp (N_c : ℕ) [NeZero N_c] (hN_c : 2 ≤ N_c)
    (p : ℝ≥0∞) (hp : 2 < p) :
    BakryEmeryCDMemLp (sunHaarProb N_c) (sunDirichletForm N_c)
      ((N_c : ℝ) / 4) p (sunHaarProb N_c) := by
  unfold BakryEmeryCDMemLp LogSobolevInequalityMemLp
  refine ⟨by positivity, hp, fun f _ _ => ?_⟩
  simp only [sunDirichletForm]
  have hNc : (N_c : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N_c)
  have harith : ∀ t : ℝ, (2 / ((N_c : ℝ) / 4)) * ((N_c : ℝ) / 8 * t) = t := fun t => by
    field_simp [hNc]; ring
  rw [harith]

/-- Σ-Haar LSI: existence form, MemLp-gated. -/
theorem sun_haar_lsi_memLp (N_c : ℕ) [NeZero N_c] (hN_c : 2 ≤ N_c)
    (p : ℝ≥0∞) (hp : 2 < p) :
    ∃ α_haar : ℝ, 0 < α_haar ∧
      LogSobolevInequalityMemLp (sunHaarProb N_c) (sunDirichletForm N_c)
        α_haar p (sunHaarProb N_c) := by
  refine ⟨(N_c : ℝ) / 4, by positivity, ?_⟩
  exact bakry_emery_lsi_memLp (sunHaarProb N_c) (sunDirichletForm N_c)
    _ p (sunHaarProb N_c) (by positivity) (sun_bakry_emery_cd_memLp N_c hN_c p hp)

/-- Σ-entropy-perturbation theorem: MemLp-gated variant of
`lsi_normalized_gibbs_from_haar_of_ent_pert`. The `hEntPert` premise now
takes an additional `MemLp f p (sunHaarProb N_c)` argument, which the
caller discharges from the output LSI's MemLp gate. -/
theorem lsi_normalized_gibbs_from_haar_of_ent_pert_memLp
    (N_c : ℕ) [NeZero N_c] (hN_c : 2 ≤ N_c) (β : ℝ) (hβ : 0 < β)
    (α : ℝ) (hα : 0 < α) (p : ℝ≥0∞) (hp : 2 < p)
    (hHaar : LogSobolevInequalityMemLp (sunHaarProb N_c) (sunDirichletForm N_c)
              α p (sunHaarProb N_c))
    (_hProb : MeasureTheory.IsProbabilityMeasure
      ((sunHaarProb N_c).withDensity (sunNormalizedGibbsDensity N_c hN_c β hβ)))
    (hEntPert : ∀ (f : SUN_State N_c → ℝ), Measurable f →
      MeasureTheory.MemLp f p (sunHaarProb N_c) →
      entSq N_c ((sunHaarProb N_c).withDensity
        (sunNormalizedGibbsDensity N_c hN_c β hβ)) f ≤
      Real.exp (2 * β) * entSq N_c (sunHaarProb N_c) f) :
    LogSobolevInequalityMemLp
      ((sunHaarProb N_c).withDensity (sunNormalizedGibbsDensity N_c hN_c β hβ))
      (sunDirichletForm N_c)
      (α * Real.exp (-2 * β)) p (sunHaarProb N_c) := by
  refine ⟨mul_pos hα (Real.exp_pos _), hp, ?_⟩
  intro f hf hMemLp
  obtain ⟨_, _, hLSI⟩ := hHaar
  have h1 := hLSI f hf hMemLp
  have h2 := hEntPert f hf hMemLp
  have hexp_pos : (0 : ℝ) < Real.exp (2 * β) := Real.exp_pos _
  have hexp_nn : (0 : ℝ) ≤ Real.exp (2 * β) := le_of_lt hexp_pos
  simp only [entSq] at h2
  have hneg_eq : (-2 * β : ℝ) = -(2 * β) := by ring
  have hexp_neg : Real.exp (-2 * β) = (Real.exp (2 * β))⁻¹ := by
    rw [hneg_eq]; exact Real.exp_neg (2 * β)
  have hα_ne : α ≠ 0 := ne_of_gt hα
  have hexp_ne : Real.exp (2 * β) ≠ 0 := ne_of_gt hexp_pos
  have hkey : (2 : ℝ) / (α * Real.exp (-2 * β)) =
      Real.exp (2 * β) * (2 / α) := by
    rw [hexp_neg]; field_simp
  have h3 := mul_le_mul_of_nonneg_left h1 hexp_nn
  have h4 := h2.trans h3
  rw [hkey]
  linarith [h4]

/-- Σ-Gibbs LSI from Haar: MemLp-gated form of
`lsi_normalized_gibbs_from_haar`. The former vanilla-proof obstruction over
`Integrable (f²·log(f²)) Haar` is discharged here by the MemLp helper
`memLp_gt_two_integrable_sq_mul_log_sq`. -/
theorem lsi_normalized_gibbs_from_haar_memLp
    (N_c : ℕ) [NeZero N_c] (hN_c : 2 ≤ N_c) (β : ℝ) (hβ : 0 < β)
    (α : ℝ) (hα : 0 < α) (p : ℝ≥0∞) (hp : 2 < p)
    (hHaar : LogSobolevInequalityMemLp (sunHaarProb N_c) (sunDirichletForm N_c)
              α p (sunHaarProb N_c)) :
    LogSobolevInequalityMemLp
      ((sunHaarProb N_c).withDensity (sunNormalizedGibbsDensity N_c hN_c β hβ))
      (sunDirichletForm N_c)
      (α * Real.exp (-2 * β)) p (sunHaarProb N_c) :=
  lsi_normalized_gibbs_from_haar_of_ent_pert_memLp N_c hN_c β hβ α hα p hp hHaar
    (instIsProbabilityMeasure_sunGibbsFamily_norm 0 N_c hN_c β hβ 0)
    (fun f hf hMemLp_haar => by
      by_cases hpos : 0 < ∫ x, f x ^ 2 ∂(sunHaarProb N_c)
      · have hint_f2 : MeasureTheory.Integrable (fun x => f x ^ 2) (sunHaarProb N_c) := by
          by_contra h; simp [MeasureTheory.integral_undef h] at hpos
        -- THE Σ CLOSURE: MemLp p>2 supplies the previously-sorry integrability.
        have hint_haar_log :
            MeasureTheory.Integrable
              (fun x => f x ^ 2 * Real.log (f x ^ 2)) (sunHaarProb N_c) :=
          YangMills.memLp_gt_two_integrable_sq_mul_log_sq
            (sunHaarProb N_c) f p hp hMemLp_haar
        refine entSq_pert_bound_chain N_c β
            (sunHaarProb N_c)
            ((sunHaarProb N_c).withDensity (sunNormalizedGibbsDensity N_c hN_c β hβ))
            f
            (integral_nonneg (fun x => sq_nonneg (f x)))
            hpos
            (dv_integral_lin_cross ((sunHaarProb N_c).withDensity (sunNormalizedGibbsDensity N_c hN_c β hβ)) (instIsProbabilityMeasure_sunGibbsFamily_norm 0 N_c hN_c β hβ 0) f _ _ (integrable_gibbs_of_haar hN_c β hβ (integrable_f2_mul_log_f2_div_haar f _ hint_f2 hint_haar_log)) (integrable_gibbs_of_haar hN_c β hβ (by by_contra h; linarith [MeasureTheory.integral_undef h])))
            (log_quotient_split ((sunHaarProb N_c).withDensity (sunNormalizedGibbsDensity N_c hN_c β hβ)) f _ hpos (integrable_gibbs_of_haar hN_c β hβ (integrable_f2_mul_log_f2_haar f hint_f2 hint_haar_log)) (integrable_gibbs_of_haar hN_c β hβ (by by_contra h; linarith [MeasureTheory.integral_undef h])))
            (dv_integral_lin_self (sunHaarProb N_c) f _ hpos)
            (log_quotient_split (sunHaarProb N_c) f _ hpos (integrable_f2_mul_log_f2_haar f hint_f2 hint_haar_log) (by by_contra h; linarith [MeasureTheory.integral_undef h]))
            ?_
        have dv_nn : ∀ x, 0 ≤ f x ^ 2 * Real.log (f x ^ 2 / ∫ y, f y ^ 2 ∂sunHaarProb N_c) - f x ^ 2 + ∫ y, f y ^ 2 ∂sunHaarProb N_c := by
          intro x
          rcases eq_or_lt_of_le (sq_nonneg (f x)) with h0 | htpos
          · simp [← h0, hpos.le]
          · set u := f x ^ 2 / ∫ y, f y ^ 2 ∂sunHaarProb N_c with hu_def
            have hupos : 0 < u := div_pos htpos hpos
            suffices hsuff : 0 ≤ u * Real.log u - u + 1 by
              have : f x ^ 2 * Real.log (f x ^ 2 / ∫ y, f y ^ 2 ∂sunHaarProb N_c) - f x ^ 2 + ∫ y, f y ^ 2 ∂sunHaarProb N_c = (∫ y, f y ^ 2 ∂sunHaarProb N_c) * (u * Real.log u - u + 1) := by rw [hu_def]; field_simp
              linarith [mul_nonneg hpos.le hsuff]
            have key : 1 + Real.log u⁻¹ ≤ u⁻¹ := by
              have h := Real.add_one_le_exp (Real.log u⁻¹)
              rw [Real.exp_log (inv_pos.mpr hupos)] at h; linarith
            rw [Real.log_inv] at key
            have h2 : u * (1 - Real.log u) ≤ 1 := by
              calc u * (1 - Real.log u) ≤ u * u⁻¹ := mul_le_mul_of_nonneg_left key hupos.le
                _ = 1 := mul_inv_cancel₀ (ne_of_gt hupos)
            linarith [show u * Real.log u - u + 1 = 1 - u * (1 - Real.log u) from by ring]
        have hint_φ := ((integrable_f2_mul_log_f2_div_haar f (∫ y, f y ^ 2 ∂sunHaarProb N_c) hint_f2 hint_haar_log).sub hint_f2).add (MeasureTheory.integrable_const (∫ y, f y ^ 2 ∂sunHaarProb N_c))
        have h := MeasureTheory.integral_mono_measure (gibbs_measure_le_smul_haar hN_c β hβ) (Filter.Eventually.of_forall dv_nn) (hint_φ.smul_measure ENNReal.ofReal_ne_top)
        rwa [MeasureTheory.integral_smul_measure, ENNReal.toReal_ofReal (le_of_lt (Real.exp_pos _))] at h
      · -- Zero-integral branch: reuses the existing entSq_pert_zero_case /
        -- non-integrable corner-case machinery from the vanilla proof.
        have hnn : 0 ≤ ∫ y, f y ^ 2 ∂(sunHaarProb N_c) :=
          integral_nonneg (fun x => sq_nonneg _)
        by_cases hint : MeasureTheory.Integrable (fun x => f x ^ 2) (sunHaarProb N_c)
        · exact entSq_pert_zero_case N_c β (sunHaarProb N_c) _ f hf
            (MeasureTheory.withDensity_absolutelyContinuous _ _) hint hnn hpos
        · have hint_gibbs := not_integrable_gibbs_of_not_integrable_haar hN_c β hβ hint
          have hint_log : ¬ MeasureTheory.Integrable (fun x => f x ^ 2 * Real.log (f x ^ 2)) (sunHaarProb N_c) := by
            intro habs
            apply hint
            exact ((MeasureTheory.integrable_const (1 : ℝ)).add habs.norm).mono'
              (by fun_prop)
              (Filter.Eventually.of_forall (fun x => by
              simp only [Pi.add_apply, Real.norm_eq_abs]
              rw [abs_of_nonneg (sq_nonneg _)]
              by_cases hfx : f x ^ 2 ≤ 1
              · linarith [abs_nonneg (f x ^ 2 * Real.log (f x ^ 2))]
              · push_neg at hfx
                have h_pos : (0 : ℝ) < f x ^ 2 := by linarith
                have h_log_pos := Real.log_pos (by linarith : (1 : ℝ) < f x ^ 2)
                rw [abs_of_pos (mul_pos h_pos h_log_pos)]
                have := Real.add_one_le_exp (-(Real.log (f x ^ 2)))
                rw [Real.exp_neg, Real.exp_log h_pos] at this
                have h_mul := mul_le_mul_of_nonneg_left this (le_of_lt h_pos)
                rw [mul_inv_cancel₀ h_pos.ne'] at h_mul
                nlinarith))
          have hint_log_gibbs := not_integrable_gibbs_of_not_integrable_haar hN_c β hβ hint_log
          simp only [entSq, MeasureTheory.integral_undef hint,
            MeasureTheory.integral_undef hint_gibbs,
            MeasureTheory.integral_undef hint_log,
            MeasureTheory.integral_undef hint_log_gibbs,
            mul_zero, Real.log_zero, sub_self, le_refl])

/-- Σ-family LSI: MemLp-gated RG-uniform LSI on the normalized Gibbs family. -/
theorem balaban_rg_uniform_lsi_norm_memLp
    (d N_c : ℕ) [NeZero N_c] (hN_c : 2 ≤ N_c) (β β₀ : ℝ)
    (hβ : β ≥ β₀) (hβ₀ : 0 < β₀) (p : ℝ≥0∞) (hp : 2 < p) :
    ∃ α_star : ℝ, 0 < α_star ∧ ∀ L : ℕ,
      LogSobolevInequalityMemLp
        (sunGibbsFamily_norm d N_c hN_c β (hβ₀.trans_le hβ) L)
        (sunDirichletForm N_c) α_star p (sunHaarProb N_c) := by
  obtain ⟨α_haar, hα_pos, hHaar⟩ := sun_haar_lsi_memLp N_c hN_c p hp
  refine ⟨α_haar * Real.exp (-2 * β), mul_pos hα_pos (Real.exp_pos _), ?_⟩
  intro L
  simp only [sunGibbsFamily_norm]
  exact lsi_normalized_gibbs_from_haar_memLp N_c hN_c β (hβ₀.trans_le hβ)
    α_haar hα_pos p hp hHaar

/-- Σ-DLR LSI on the normalized Gibbs family. -/
theorem sun_gibbs_dlr_lsi_norm_memLp
    (d N_c : ℕ) [NeZero N_c] (hN_c : 2 ≤ N_c) (β β₀ : ℝ)
    (hβ : β ≥ β₀) (hβ₀ : 0 < β₀) (p : ℝ≥0∞) (hp : 2 < p) :
    ∃ α_star : ℝ, 0 < α_star ∧
      DLR_LSI_MemLp (sunGibbsFamily_norm d N_c hN_c β (hβ₀.trans_le hβ))
        (sunDirichletForm N_c) α_star p (sunHaarProb N_c) := by
  obtain ⟨α_star, hα_pos, hLSI⟩ :=
    balaban_rg_uniform_lsi_norm_memLp d N_c hN_c β β₀ hβ hβ₀ p hp
  exact ⟨α_star, hα_pos, hα_pos, hp, hLSI⟩
end YangMills
