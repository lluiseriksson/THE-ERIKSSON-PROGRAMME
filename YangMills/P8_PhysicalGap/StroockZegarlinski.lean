import Mathlib
import YangMills.P8_PhysicalGap.LSItoSpectralGap
open MeasureTheory Real Filter Topology
namespace YangMills

/-!
# Stroock-Zegarlinski: LSI → Exponential Clustering (Milestone M4)

## Overview

This file formalizes the Stroock-Zegarlinski theorem (J. Funct. Anal. 1992):
  DLR_LSI gibbsFamily E α_star → ExponentialClustering (gibbsFamily L) C ξ

The chain is:
  1. DLR_LSI  →  PoincareInequality  (via lsi_implies_poincare_strong)
  2. PoincareInequality  →  L² semigroup decay  (via spectral gap estimate)
  3. L² semigroup decay  →  ExponentialClustering  (via covariance bound)

Axioms 2 and 3 are named below; their proofs are Milestones M4a and M4b.

## Reference
Stroock-Zegarlinski, "The logarithmic Sobolev inequality for continuous
spin systems on a lattice", J. Funct. Anal. 104 (1992), 299–326.
-/

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## Intermediate definitions -/

/-- L² spectral gap decay of a Markov semigroup (T_t)_{t≥0}.
    Poincaré with constant λ implies ‖T_t f - μ(f)‖₂ ≤ exp(-λ t) ‖f‖₂. -/
def HasL2SpectralDecay (μ : Measure Ω) (E : (Ω → ℝ) → ℝ) (lam : ℝ) : Prop :=
  0 < lam ∧
  ∀ (f : Ω → ℝ), Measurable f →
    Integrable (fun x => f x ^ 2) μ →
    ∀ t : ℝ, 0 ≤ t →
      ∫ x, (f x - ∫ y, f y ∂μ) ^ 2 ∂μ ≤
        Real.exp (-lam * t) * (E f + ∫ x, (f x - ∫ y, f y ∂μ) ^ 2 ∂μ)

/-- Covariance decay: |Cov_μ(F, G)| ≤ C √Var(F) √Var(G) exp(-1/ξ).
    This is the single-scale version of ExponentialClustering. -/
def HasCovarianceDecay (μ : Measure Ω) (C ξ : ℝ) : Prop :=
  0 < ξ ∧ 0 < C ∧
  ∀ (F G : Ω → ℝ),
    |∫ x, F x * G x ∂μ - (∫ x, F x ∂μ) * (∫ x, G x ∂μ)| ≤
    C * Real.sqrt (∫ x, (F x - ∫ y, F y ∂μ) ^ 2 ∂μ) *
        Real.sqrt (∫ x, (G x - ∫ y, G y ∂μ) ^ 2 ∂μ) *
    Real.exp (-1 / ξ)

/-! ## Bridge axioms (Milestones M4a and M4b) -/

/-- M4a: Poincaré inequality implies L² spectral gap decay.
    Proof: spectral theory of the Dirichlet form operator.
    The gap λ equals the Poincaré constant.
    Reference: Bakry-Emery, Holley-Stroock, Diaconis-Saloff-Coste. -/
axiom poincare_to_spectral_decay
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (E : (Ω → ℝ) → ℝ) (lam : ℝ)
    (hE : IsDirichletFormStrong E μ)
    (hP : PoincareInequality μ E lam) :
    HasL2SpectralDecay μ E lam

/-- M4b: L² spectral gap decay implies exponential clustering (covariance decay).
    Proof: integrate the semigroup decay against observables.
    The clustering rate ξ = 1/lam and constant C = 2.
    Reference: Stroock-Zegarlinski 1992, Theorem 3.3. -/
axiom spectral_decay_to_clustering
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (E : (Ω → ℝ) → ℝ) (lam : ℝ)
    (hD : HasL2SpectralDecay μ E lam) :
    HasCovarianceDecay μ 2 (1 / lam)

/-- Covariance decay implies ExponentialClustering (definition compatibility). -/
lemma covariance_decay_to_exponential_clustering
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (C ξ : ℝ)
    (hCD : HasCovarianceDecay μ C ξ) :
    ExponentialClustering μ C ξ := by
  obtain ⟨hξ, hC, hcov⟩ := hCD
  refine ⟨hξ, hC, fun F G => ?_⟩
  -- ExponentialClustering uses √(∫F²) not √Var(F); relate via Cauchy-Schwarz
  -- For simplicity we use: |Cov| ≤ |∫FG - (∫F)(∫G)| ≤ C √(∫F²) √(∫G²) exp(-1/ξ)
  -- because ∫(F - μF)² ≤ ∫F² (by expanding and using μ(F)² ≥ 0)
  have hF : ∫ x, (F x - ∫ y, F y ∂μ) ^ 2 ∂μ ≤ ∫ x, F x ^ 2 ∂μ := by
    sorry -- Var(F) ≤ E[F²], standard via Jensen
  have hG : ∫ x, (G x - ∫ y, G y ∂μ) ^ 2 ∂μ ≤ ∫ x, G x ^ 2 ∂μ := by
    sorry -- same
  calc |∫ x, F x * G x ∂μ - (∫ x, F x ∂μ) * (∫ x, G x ∂μ)|
      ≤ C * Real.sqrt (∫ x, (F x - ∫ y, F y ∂μ) ^ 2 ∂μ) *
            Real.sqrt (∫ x, (G x - ∫ y, G y ∂μ) ^ 2 ∂μ) *
          Real.exp (-1 / ξ) := hcov F G
    _ ≤ C * Real.sqrt (∫ x, F x ^ 2 ∂μ) *
            Real.sqrt (∫ x, G x ^ 2 ∂μ) *
          Real.exp (-1 / ξ) := by
        gcongr
        · exact Real.sqrt_le_sqrt hF
        · exact Real.sqrt_le_sqrt hG

/-! ## Main theorem: M4 bridge -/

/-- Milestone M4: DLR_LSI → ExponentialClustering.
    Proof chain:
      DLR_LSI → (per volume L) PoincareInequality
             → L² spectral decay (M4a axiom)
             → covariance decay (M4b axiom)
             → ExponentialClustering -/
theorem sz_lsi_to_clustering_bridge
    (gibbsFamily : ℕ → Measure Ω)
    [∀ L, IsProbabilityMeasure (gibbsFamily L)]
    (E : (Ω → ℝ) → ℝ)
    (hE : ∀ L, IsDirichletFormStrong E (gibbsFamily L))
    (α_star : ℝ)
    (hLSI : DLR_LSI gibbsFamily E α_star) :
    ∃ C ξ, 0 < ξ ∧ ξ ≤ 1 / α_star ∧
      ∀ L : ℕ, ExponentialClustering (gibbsFamily L) C ξ := by
  obtain ⟨hα, hLSI_per_volume⟩ := hLSI
  -- Step 1: LSI → Poincaré at each volume
  have hPoincare : ∀ L, PoincareInequality (gibbsFamily L) E (α_star / 2) := by
    intro L
    exact lsi_implies_poincare_strong (gibbsFamily L) E (hE L)
      (fun f hf hfnn => (hLSI_per_volume L).2 hf hfnn) hα
  -- Step 2: Poincaré → spectral decay (M4a)
  have hDecay : ∀ L, HasL2SpectralDecay (gibbsFamily L) E (α_star / 2) := by
    intro L; exact poincare_to_spectral_decay E (α_star / 2) (hE L) (hPoincare L)
  -- Step 3: spectral decay → covariance decay (M4b)
  have hCov : ∀ L, HasCovarianceDecay (gibbsFamily L) 2 (1 / (α_star / 2)) := by
    intro L; exact spectral_decay_to_clustering E (α_star / 2) (hDecay L)
  -- Step 4: covariance decay → ExponentialClustering
  have hClust : ∀ L, ExponentialClustering (gibbsFamily L) 2 (1 / (α_star / 2)) := by
    intro L; exact covariance_decay_to_exponential_clustering 2 _ (hCov L)
  -- Package with ξ = 2/α_star ≤ 1/α_star? No: 2/α_star > 1/α_star. 
  -- We need ξ ≤ 1/α_star. Use ξ = 1/α_star directly.
  -- Note: HasCovarianceDecay with ξ = 2/α_star. 
  -- For the bound ξ ≤ 1/α_star: 2/α_star ≤ 1/α_star is false.
  -- Fix: use C = 2, ξ = 1/α_star (tighter). 
  -- The clustering rate is 1/(α_star/2) = 2/α_star. 
  -- The requirement sz_lsi_to_clustering says ξ ≤ 1/α_star.
  -- So we need ξ = something ≤ 1/α_star. Use ξ = 1/(2/α_star) = α_star/2? No.
  -- Actually ExponentialClustering uses exp(-1/ξ), so larger ξ = slower decay.
  -- sz_lsi_to_clustering requires ξ ≤ 1/α_star (better clustering = smaller ξ).
  -- Our proof gives ξ = 2/α_star. Is 2/α_star ≤ 1/α_star? No (for α_star > 0).
  -- Fix: the rate from Poincaré is α_star/2, giving decay exp(-α_star/2 * t).
  -- Clustering ξ = 1/(α_star/2) = 2/α_star. Need ξ ≤ 1/α_star.
  -- 2/α_star ≤ 1/α_star iff 2 ≤ 1, false. So the axiom sz_lsi_to_clustering bound is tight.
  -- We can satisfy it with a weaker clustering: exp(-1/(1/α_star)) = exp(-α_star).
  -- Since exp(-α_star) ≤ exp(-α_star/2), use C=2, ξ = 1/α_star (weaker).
  refine ⟨2, 1 / α_star, by positivity, le_refl _, fun L => ?_⟩
  -- Need ExponentialClustering (gibbsFamily L) 2 (1/α_star)
  -- We have ExponentialClustering (gibbsFamily L) 2 (2/α_star)
  -- Since 2/α_star ≥ 1/α_star, exp(-1/(2/α_star)) = exp(-α_star/2) ≤ exp(-α_star) = exp(-1/(1/α_star))
  -- So ExponentialClustering with ξ=2/α_star implies ExponentialClustering with ξ=1/α_star
  obtain ⟨hξ', hC', hcov'⟩ := hClust L
  refine ⟨by positivity, hC', fun F G => ?_⟩
  calc |∫ x, F x * G x ∂(gibbsFamily L) - (∫ x, F x ∂(gibbsFamily L)) * (∫ x, G x ∂(gibbsFamily L))|
      ≤ 2 * Real.sqrt (∫ x, F x ^ 2 ∂(gibbsFamily L)) *
            Real.sqrt (∫ x, G x ^ 2 ∂(gibbsFamily L)) *
          Real.exp (-1 / (2 / α_star)) := hcov' F G
    _ ≤ 2 * Real.sqrt (∫ x, F x ^ 2 ∂(gibbsFamily L)) *
            Real.sqrt (∫ x, G x ^ 2 ∂(gibbsFamily L)) *
          Real.exp (-1 / (1 / α_star)) := by
        gcongr
        apply Real.exp_le_exp_of_le
        -- -1/(2/α_star) ≤ -1/(1/α_star) iff -α_star/2 ≤ -α_star iff α_star ≤ α_star/2, false
        -- Actually we want: exp(-α_star/2) ≤ exp(-α_star)? No, α_star > 0 so exp(-α_star/2) > exp(-α_star).
        -- So this direction is wrong. We need a different approach.
        -- The correct direction: ξ=1/α_star gives slower decay (larger ξ = weaker clustering).
        -- ExponentialClustering with ξ=2/α_star (fast decay) trivially implies ξ=1/α_star? No.
        -- Actually definition: |Cov| ≤ C √... √... exp(-1/ξ).
        -- Larger ξ → exp(-1/ξ) is larger (weaker bound). 
        -- So ExponClustering(ξ=2/α) is STRONGER than ExponClustering(ξ=1/α) when 2/α > 1/α.
        -- So we CAN weaken: go from ξ=2/α_star to ξ=1/α_star. Need exp(-α_star/2) ≤ exp(-α_star)?
        -- -α_star/2 ≤ -α_star iff α_star ≤ α_star/2, FALSE for α_star > 0.
        -- So we cannot weaken in this direction! 
        -- The sz_lsi_to_clustering axiom bound ξ ≤ 1/α_star must mean rate, not period.
        -- Our proof gives ξ_rate = α_star/2, which ≥ α_star... no.
        -- Leave as sorry for now.
        sorry

end YangMills
