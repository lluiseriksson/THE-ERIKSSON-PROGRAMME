import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# LSIDefinitions — shared definitions, no project imports
Extracted from LSItoSpectralGap.lean to break the import cycle.
-/

open MeasureTheory Real
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]

def IsDirichletForm (E : (Ω → ℝ) → ℝ) (μ : Measure Ω) : Prop :=
  (∀ f, 0 ≤ E f) ∧ (∀ f g : Ω → ℝ, E (f + g) ≤ 2 * E f + 2 * E g)

def LogSobolevInequality (μ : Measure Ω) (E : (Ω → ℝ) → ℝ) (α : ℝ) : Prop :=
  0 < α ∧ ∀ (f : Ω → ℝ) (_ : Measurable f),
    ∫ x, f x ^ 2 * Real.log (f x ^ 2) ∂μ -
    (∫ x, f x ^ 2 ∂μ) * Real.log (∫ x, f x ^ 2 ∂μ) ≤ (2 / α) * E f

/-- **Path Σ: MemLp-gated LSI** with an explicit reference measure for the
integrability gate. Quantifier restricted to `f` satisfying
`MemLp f p μ_ref` with `2 < p`.

The decoupling between `μ` (the LSI measure) and `μ_ref` (the measure against
which MemLp integrability is asserted) is what makes the gate survive the
Holley–Stroock density perturbation: the Haar supplier and the Gibbs consumer
can share the SAME `μ_ref = sunHaarProb N_c`, so no `MemLp` transfer across
measures is needed. Downstream, the only Clay-chain consumer
(`sun_physical_mass_gap_vacuous`) uses ONLY the `0 < α` conjunct, so the
extra `μ_ref` parameter has zero footprint on the oracle chain.

On a finite `μ_ref`, `2 < p` implies `Integrable (f²·log(f²)) μ_ref`
(lemma `memLp_gt_two_integrable_sq_mul_log_sq`), which is the missing
piece that forces the old `BalabanToLSI.lean:805 sorry` under the vanilla
universal predicate. -/
def LogSobolevInequalityMemLp
    (μ : Measure Ω) (E : (Ω → ℝ) → ℝ) (α : ℝ) (p : ℝ≥0∞) (μ_ref : Measure Ω) : Prop :=
  0 < α ∧ 2 < p ∧ ∀ (f : Ω → ℝ) (_ : Measurable f) (_ : MemLp f p μ_ref),
    ∫ x, f x ^ 2 * Real.log (f x ^ 2) ∂μ -
    (∫ x, f x ^ 2 ∂μ) * Real.log (∫ x, f x ^ 2 ∂μ) ≤ (2 / α) * E f

def DLR_LSI (gibbsFamily : ℕ → Measure Ω) (E : (Ω → ℝ) → ℝ) (α_star : ℝ) : Prop :=
  0 < α_star ∧ ∀ L : ℕ, LogSobolevInequality (gibbsFamily L) E α_star

/-- MemLp-gated DLR-LSI. Same reference-measure decoupling as
`LogSobolevInequalityMemLp`: the entire family shares one `μ_ref`. -/
def DLR_LSI_MemLp
    (gibbsFamily : ℕ → Measure Ω) (E : (Ω → ℝ) → ℝ)
    (α_star : ℝ) (p : ℝ≥0∞) (μ_ref : Measure Ω) : Prop :=
  0 < α_star ∧ 2 < p ∧
    ∀ L : ℕ, LogSobolevInequalityMemLp (gibbsFamily L) E α_star p μ_ref

def ExponentialClustering (μ : Measure Ω) (C ξ : ℝ) : Prop :=
  0 < ξ ∧ 0 < C ∧
  ∀ (F G_obs : Ω → ℝ),
    |∫ x, F x * G_obs x ∂μ - (∫ x, F x ∂μ) * (∫ x, G_obs x ∂μ)| ≤
    C * Real.sqrt (∫ x, F x ^ 2 ∂μ) * Real.sqrt (∫ x, G_obs x ^ 2 ∂μ) *
    Real.exp (-1 / ξ)

def PoincareInequality (μ : Measure Ω) (E : (Ω → ℝ) → ℝ) (lam : ℝ) : Prop :=
  0 < lam ∧ ∀ (f : Ω → ℝ) (_ : Measurable f),
    ∫ x, (f x - ∫ y, f y ∂μ) ^ 2 ∂μ ≤ (1 / lam) * E f

def IsDirichletFormStrong (E : (Ω → ℝ) → ℝ) (μ : Measure Ω) : Prop :=
  IsDirichletForm E μ ∧
  (∀ (c : ℝ) (f : Ω → ℝ), E (fun x => f x + c) = E f) ∧
  (∀ (c : ℝ) (f : Ω → ℝ), E (fun x => c * f x) = c ^ 2 * E f) ∧
  (∀ (f : Ω → ℝ) (n : ℝ), 0 < n →
    E (fun x => max (min (f x) n) (-n)) ≤ E f)
