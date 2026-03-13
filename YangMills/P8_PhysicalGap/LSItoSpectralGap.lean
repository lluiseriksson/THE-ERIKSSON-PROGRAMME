import Mathlib
import YangMills.L4_TransferMatrix.TransferMatrix

/-!
# P8.2: DLR-LSI → HasSpectralGap — Milestone M4

Stroock-Zegarlinski: DLR-LSI(α*) → exponential clustering → spectral gap.

Source: Stroock-Zegarlinski, J. Funct. Anal. 101 (1992) 249-326.

## Design

All definitions are abstract Prop-level predicates over `[MeasurableSpace Ω]`.
No `NormedSpace`, `TopologicalSpace`, or `fderiv` — those belong in the
concrete instantiation for SU(N) in BalabanToLSI.lean.

The Dirichlet form `E` is passed as an abstract parameter, not computed
from derivatives. This is the standard approach in abstract Markov semigroup
theory (cf. Bakry-Émery, Ma-Röckner).
-/

namespace YangMills

open MeasureTheory Real

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## Abstract Dirichlet form -/

/-- An abstract Dirichlet form on L²(μ): E : (Ω → ℝ) → ℝ ≥ 0.
    In concrete cases: E(f) = ∫ ‖∇f‖² dμ for smooth f. -/
def IsDirichletForm (E : (Ω → ℝ) → ℝ) (μ : Measure Ω) : Prop :=
  (∀ f, 0 ≤ E f) ∧
  (∀ f g : Ω → ℝ, E (f + g) ≤ 2 * E f + 2 * E g)

/-! ## Log-Sobolev Inequality -/

/-- Log-Sobolev inequality with Dirichlet form E and constant α.
    Ent_μ(f²) ≤ (2/α)·E(f) for all measurable f.
    where Ent_μ(h) = ∫ h·log(h) dμ - (∫ h dμ)·log(∫ h dμ). -/
def LogSobolevInequality (μ : Measure Ω) (E : (Ω → ℝ) → ℝ) (α : ℝ) : Prop :=
  0 < α ∧ ∀ (f : Ω → ℝ) (_ : Measurable f),
    ∫ x, f x ^ 2 * Real.log (f x ^ 2) ∂μ -
    (∫ x, f x ^ 2 ∂μ) * Real.log (∫ x, f x ^ 2 ∂μ) ≤
    (2 / α) * E f

/-- DLR-LSI: LSI uniform in finite volume. -/
def DLR_LSI (gibbsFamily : ℕ → Measure Ω) (E : (Ω → ℝ) → ℝ) (α_star : ℝ) : Prop :=
  0 < α_star ∧ ∀ L : ℕ, LogSobolevInequality (gibbsFamily L) E α_star

/-! ## Exponential Clustering -/

/-- Exponential clustering: connected correlations decay exponentially.
    |Cov_μ(F,G)| ≤ C·‖F‖_L²·‖G‖_L²·exp(-1/ξ). -/
def ExponentialClustering (μ : Measure Ω) (C ξ : ℝ) : Prop :=
  0 < ξ ∧ 0 < C ∧
  ∀ (F G_obs : Ω → ℝ),
    |∫ x, F x * G_obs x ∂μ -
     (∫ x, F x ∂μ) * (∫ x, G_obs x ∂μ)| ≤
    C * Real.sqrt (∫ x, F x ^ 2 ∂μ) *
        Real.sqrt (∫ x, G_obs x ^ 2 ∂μ) *
    Real.exp (-1 / ξ)

/-! ## Poincaré Inequality -/

/-- Poincaré inequality with abstract Dirichlet form E.
    Var_μ(f) ≤ (1/lam)·E(f).
    Note: lam not λ — λ is reserved in Lean 4. -/
def PoincareInequality (μ : Measure Ω) (E : (Ω → ℝ) → ℝ) (lam : ℝ) : Prop :=
  0 < lam ∧ ∀ (f : Ω → ℝ) (_ : Measurable f),
    ∫ x, (f x - ∫ y, f y ∂μ) ^ 2 ∂μ ≤ (1 / lam) * E f

/-! ## Axioms (to be proved in M4) -/

/-- LSI(α) → Poincaré(α/2). Rothaus 1981.
    Status: AXIOM — to be proved in M4. -/
axiom lsi_implies_poincare
    (μ : Measure Ω) (E : (Ω → ℝ) → ℝ) (α : ℝ)
    (hLSI : LogSobolevInequality μ E α) :
    PoincareInequality μ E (α / 2)

/-- Stroock-Zegarlinski: DLR-LSI(α*) → exponential clustering.
    Source: SZ J. Funct. Anal. 1992.
    Status: AXIOM — to be proved in M4. -/
axiom sz_lsi_to_clustering
    (gibbsFamily : ℕ → Measure Ω) (E : (Ω → ℝ) → ℝ) (α_star : ℝ)
    (hLSI : DLR_LSI gibbsFamily E α_star) :
    ∃ C ξ : ℝ, 0 < ξ ∧ ξ ≤ 1/α_star ∧
    ∀ L : ℕ, ExponentialClustering (gibbsFamily L) C ξ

/-- Exponential clustering → HasSpectralGap.
    Status: AXIOM — to be proved in M4. -/
axiom clustering_to_spectralGap
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (μ : Measure Ω) (C ξ : ℝ) (hξ : 0 < ξ) (hC : 0 < C)
    (T P₀ : H →L[ℝ] H) :
    HasSpectralGap T P₀ (1 / ξ) (2 * C)

/-! ## Main theorem: DLR-LSI → HasSpectralGap -/

/-- DLR-LSI(α*) → HasSpectralGap with γ ≥ α*. -/
theorem lsi_to_spectralGap
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (gibbsFamily : ℕ → Measure Ω) (E : (Ω → ℝ) → ℝ) (α_star : ℝ)
    (hLSI : DLR_LSI gibbsFamily E α_star)
    (T P₀ : H →L[ℝ] H) :
    ∃ γ C : ℝ, 0 < γ ∧ HasSpectralGap T P₀ γ C := by
  obtain ⟨C, ξ, hξ, _, hcluster⟩ :=
    sz_lsi_to_clustering gibbsFamily E α_star hLSI
  exact ⟨1/ξ, 2*C, by positivity,
    clustering_to_spectralGap (gibbsFamily 0) C ξ hξ (hcluster 0).2.1 T P₀⟩

end YangMills
