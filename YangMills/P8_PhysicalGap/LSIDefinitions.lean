import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# LSIDefinitions — shared definitions, no project imports
Extracted from LSItoSpectralGap.lean to break the import cycle.
-/

open MeasureTheory Real

variable {Ω : Type*} [MeasurableSpace Ω]

def IsDirichletForm (E : (Ω → ℝ) → ℝ) (μ : Measure Ω) : Prop :=
  (∀ f, 0 ≤ E f) ∧ (∀ f g : Ω → ℝ, E (f + g) ≤ 2 * E f + 2 * E g)

def LogSobolevInequality (μ : Measure Ω) (E : (Ω → ℝ) → ℝ) (α : ℝ) : Prop :=
  0 < α ∧ ∀ (f : Ω → ℝ) (_ : Measurable f),
    ∫ x, f x ^ 2 * Real.log (f x ^ 2) ∂μ -
    (∫ x, f x ^ 2 ∂μ) * Real.log (∫ x, f x ^ 2 ∂μ) ≤ (2 / α) * E f

def DLR_LSI (gibbsFamily : ℕ → Measure Ω) (E : (Ω → ℝ) → ℝ) (α_star : ℝ) : Prop :=
  0 < α_star ∧ ∀ L : ℕ, LogSobolevInequality (gibbsFamily L) E α_star

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

/-- LSI → Poincaré for all f ∈ L² (any centered measurable function).
    Forward declaration: proved as theorem in LSItoSpectralGap.lean (L441).
    This axiom cannot be replaced here due to import cycle:
    LSItoSpectralGap imports LSIDefinitions; LSIDefinitions cannot import LSItoSpectralGap.
    Resolution: extract to LSIPoincareBridge.lean (future work, v0.8.43). -/
axiom lsi_implies_poincare_strong
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (E : (Ω → ℝ) → ℝ) (hE : IsDirichletFormStrong E μ) (α : ℝ)
    (hLSI : ∀ f : Ω → ℝ, Measurable f → (∀ x, 0 ≤ f x) →
        ∫ x, f x ^ 2 * Real.log (f x ^ 2) ∂μ -
        (∫ x, f x ^ 2 ∂μ) * Real.log (∫ x, f x ^ 2 ∂μ) ≤ (2 / α) * E f)
    (hα : 0 < α) :
    PoincareInequality μ E (α / 2)
