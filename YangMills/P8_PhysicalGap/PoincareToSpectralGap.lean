import Mathlib
import YangMills.P8_PhysicalGap.LSIDefinitions
import YangMills.P8_PhysicalGap.MarkovSemigroupDef

namespace YangMills
open MeasureTheory Real

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## P8.5: One-Step Variance Contraction → n-Step Variance Decay (C79)

### What this proves (sorry-free)
Given the one-step hypothesis:
  hstep : ∀ f, Var(T₁ f) ≤ (1-λ) · Var(f)
we prove by induction:
  ∀ n f, Var(Tₙ f) ≤ (1-λ)ⁿ · Var(f)

This chain makes the single honest open problem explicit:
  hstep  ←  Poincaré inequality + Beurling-Deny/Hille-Yosida correspondence
           (the d/dt Var(Tₜf) = -2E(Tₜf) ≤ -2λ Var(Tₜf) argument)

Everything else in the chain is proved here without sorry.

### Corollary: HasVarianceDecay (discrete version)
From the n-step bound, using (1-λ)ⁿ ≤ exp(-λn) ≤ exp(-2γn) for γ = λ/2,
we derive HasVarianceDecay (at integer times t = n : ℕ).

### Live-path significance
- Connects lsi_implies_poincare (LSItoSpectralGap.lean) via hstep to HasVarianceDecay
- HasVarianceDecay is used by markov_variance_decay (MarkovVarianceDecay.lean)
- Replaces the poincare_to_covariance_decay axiom at the induction layer
- Oracle: [propext, Classical.choice, Quot.sound]  -/

/-- **C79-1 (sorry-free)**: n-step variance decay from one-step contraction.

If the Markov semigroup T₁ contracts variance by factor (1-λ) per step,
then Tₙ contracts variance by (1-λ)ⁿ.  Proved by induction on n
using T_add and T_stat (stationarity preserves the mean).

The hypothesis hstep is the Poincaré → Beurling-Deny bridge:
  Var(T₁ f) ≤ (1-λ) · Var(f)
follows from E(f) ≥ λ Var(f) and d/dt Var(Tₜ f)|_{t=0} = -2 E(f).
Oracle: [propext, Classical.choice, Quot.sound]. -/
theorem oneStep_implies_varianceDecay
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (sg : SymmetricMarkovTransport μ) (lam : ℝ) (hlam1 : 0 ≤ 1 - lam)
    (hstep : ∀ (f : Ω → ℝ), Integrable f μ →
        Integrable (fun x => f x ^ 2) μ →
        ∫ x, (sg.T 1 f x - ∫ y, f y ∂μ) ^ 2 ∂μ ≤
        (1 - lam) * ∫ x, (f x - ∫ y, f y ∂μ) ^ 2 ∂μ)
    (f : Ω → ℝ) (hf : Integrable f μ) (hf2 : Integrable (fun x => f x ^ 2) μ)
    (n : ℕ) :
    ∫ x, (sg.T (↑n) f x - ∫ y, f y ∂μ) ^ 2 ∂μ ≤
    (1 - lam) ^ n * ∫ x, (f x - ∫ y, f y ∂μ) ^ 2 ∂μ := by
  induction n with
  | zero => simp [sg.T_zero]
  | succ n ih =>
    -- Integrability of T_n f
    have hTn  : Integrable (sg.T (↑n) f) μ         := sg.T_integrable (↑n) f hf
    have hTn2 : Integrable (fun x => sg.T (↑n) f x ^ 2) μ := sg.T_sq_integrable (↑n) f hf2
    -- Stationarity: ⟨T_n f⟩ = ⟨f⟩
    have hmean : ∫ y, sg.T (↑n) f y ∂μ = ∫ y, f y ∂μ := sg.T_stat (↑n) f hf
    -- Semigroup composition: T_{n+1} = T_1 ∘ T_n
    have hcomp : sg.T (↑(n + 1)) f = sg.T 1 (sg.T (↑n) f) := by
      push_cast
      rw [show (n : ℝ) + 1 = 1 + (n : ℝ) from by ring]
      exact sg.T_add 1 (↑n) f
    -- Apply hstep to T_n f (after rewriting its mean as ⟨f⟩)
    have h1 : ∫ x, (sg.T 1 (sg.T (↑n) f) x - ∫ y, f y ∂μ) ^ 2 ∂μ ≤
        (1 - lam) * ∫ x, (sg.T (↑n) f x - ∫ y, f y ∂μ) ^ 2 ∂μ := by
      have := hstep (sg.T (↑n) f) hTn hTn2; rwa [hmean] at this
    -- Chain the estimates
    calc ∫ x, (sg.T (↑(n + 1)) f x - ∫ y, f y ∂μ) ^ 2 ∂μ
        = ∫ x, (sg.T 1 (sg.T (↑n) f) x - ∫ y, f y ∂μ) ^ 2 ∂μ := by simp_rw [hcomp]
      _ ≤ (1 - lam) * ∫ x, (sg.T (↑n) f x - ∫ y, f y ∂μ) ^ 2 ∂μ := h1
      _ ≤ (1 - lam) * ((1 - lam) ^ n * ∫ x, (f x - ∫ y, f y ∂μ) ^ 2 ∂μ) :=
          mul_le_mul_of_nonneg_left ih hlam1
      _ = (1 - lam) ^ (n + 1) * ∫ x, (f x - ∫ y, f y ∂μ) ^ 2 ∂μ := by ring

/-- **C79-2 (sorry-free)**: n-step bound → exponential bound using (1-λ)ⁿ ≤ exp(-λn).

From the polynomial decay (1-λ)ⁿ, we derive the exponential bound exp(-λ·n)
using the standard inequality 1 - x ≤ exp(-x).
Oracle: [propext, Classical.choice, Quot.sound]. -/
theorem varianceDecay_exp_bound
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (sg : SymmetricMarkovTransport μ) (lam : ℝ) (hlam : 0 < lam) (hlam1 : lam ≤ 1)
    (hvar : ∀ (f : Ω → ℝ), Integrable f μ →
        Integrable (fun x => f x ^ 2) μ → ∀ (n : ℕ),
        ∫ x, (sg.T (↑n) f x - ∫ y, f y ∂μ) ^ 2 ∂μ ≤
        (1 - lam) ^ n * ∫ x, (f x - ∫ y, f y ∂μ) ^ 2 ∂μ)
    (f : Ω → ℝ) (hf : Integrable f μ) (hf2 : Integrable (fun x => f x ^ 2) μ)
    (n : ℕ) :
    ∫ x, (sg.T (↑n) f x - ∫ y, f y ∂μ) ^ 2 ∂μ ≤
    Real.exp (-(lam / 2) * ↑n) * ∫ x, (f x - ∫ y, f y ∂μ) ^ 2 ∂μ := by
  have hnn : 0 ≤ ∫ x, (f x - ∫ y, f y ∂μ) ^ 2 ∂μ :=
    integral_nonneg fun x => sq_nonneg _
  have hpoly := hvar f hf hf2 n
  -- (1-lam)^n ≤ exp(-lam*n) since 1-x ≤ exp(-x)
  have hbase : 1 - lam ≤ Real.exp (-lam) :=
    by linarith [Real.add_one_le_exp (-lam)]
  have hpow : (1 - lam) ^ n ≤ Real.exp (-lam) ^ n := by
    clear hpoly
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, pow_succ]
      exact (mul_le_mul_of_nonneg_right ih (by linarith)).trans
        (mul_le_mul_of_nonneg_left hbase (by positivity))
  have hexp_pow : Real.exp (-lam) ^ n = Real.exp (-lam * ↑n) := by
    clear hpoly hpow
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, ih, ← Real.exp_add]
      apply congr_arg; push_cast; ring
  have hexp_half : Real.exp (-lam * ↑n) ≤ Real.exp (-(lam / 2) * ↑n) := by
    apply Real.exp_le_exp.mpr
    have hn : (0 : ℝ) ≤ ↑n := Nat.cast_nonneg n
    nlinarith
  calc ∫ x, (sg.T (↑n) f x - ∫ y, f y ∂μ) ^ 2 ∂μ
      ≤ (1 - lam) ^ n * ∫ x, (f x - ∫ y, f y ∂μ) ^ 2 ∂μ := hpoly
    _ ≤ Real.exp (-lam * ↑n) * ∫ x, (f x - ∫ y, f y ∂μ) ^ 2 ∂μ := by
        apply mul_le_mul_of_nonneg_right _ hnn
        exact hpow.trans hexp_pow.le
    _ ≤ Real.exp (-(lam / 2) * ↑n) * ∫ x, (f x - ∫ y, f y ∂μ) ^ 2 ∂μ :=
        mul_le_mul_of_nonneg_right hexp_half hnn

/-- **C79-CHAIN (sorry-free)**: Full chain from hstep to exponential variance decay.

Composition: C79-1 + C79-2.  The single open problem is hstep.
Oracle: [propext, Classical.choice, Quot.sound]. -/
theorem poincare_chain_to_varianceDecay
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (sg : SymmetricMarkovTransport μ) (lam : ℝ) (hlam : 0 < lam) (hlam1 : lam ≤ 1)
    (hstep : ∀ (f : Ω → ℝ), Integrable f μ →
        Integrable (fun x => f x ^ 2) μ →
        ∫ x, (sg.T 1 f x - ∫ y, f y ∂μ) ^ 2 ∂μ ≤
        (1 - lam) * ∫ x, (f x - ∫ y, f y ∂μ) ^ 2 ∂μ)
    (f : Ω → ℝ) (hf : Integrable f μ) (hf2 : Integrable (fun x => f x ^ 2) μ)
    (n : ℕ) :
    ∫ x, (sg.T (↑n) f x - ∫ y, f y ∂μ) ^ 2 ∂μ ≤
    Real.exp (-(lam / 2) * ↑n) * ∫ x, (f x - ∫ y, f y ∂μ) ^ 2 ∂μ :=
  varianceDecay_exp_bound sg lam hlam hlam1
    (fun g hg hg2 k => oneStep_implies_varianceDecay sg lam (by linarith) hstep g hg hg2 k)
    f hf hf2 n

end YangMills