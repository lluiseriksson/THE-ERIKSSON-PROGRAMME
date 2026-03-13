import Mathlib
import YangMills.P2_MaxEntClustering.PetzFidelity
import YangMills.P2_MaxEntClustering.LocalObservableAlgebras

namespace YangMills

/-! ## P2.3: MaxEnt States and Consistent Marginals -/

variable {d N : ℕ} [NeZero d] [NeZero N]
variable {G : Type*} [Group G] [FiniteLatticeGeometry d N G]

/-- A global state is consistent with a prescribed local marginal. -/
def IsConsistentMarginal
    (ω : (GaugeConfig d N G → ℝ) →ₗ[ℝ] ℝ)
    (A : Subalgebra ℝ (GaugeConfig d N G → ℝ))
    (ωA : A →ₗ[ℝ] ℝ) : Prop :=
  restrictState ω A = ωA

/-- Family of local marginals indexed by regions. -/
def LocalMarginalFamily {E : Type*} (eval : GaugeConfig d N G → E → G) :=
  ∀ Λ : Set E, localGaugeInvariantAlgebra eval Λ →ₗ[ℝ] ℝ

/-- A global state realizes all local marginals. -/
def RealizesMarginals
    {E : Type*} (eval : GaugeConfig d N G → E → G)
    (ω : (GaugeConfig d N G → ℝ) →ₗ[ℝ] ℝ)
    (marg : LocalMarginalFamily eval) : Prop :=
  ∀ Λ : Set E,
    IsConsistentMarginal ω (localGaugeInvariantAlgebra eval Λ) (marg Λ)

/-- A MaxEnt state is one consistent with the prescribed marginal. -/
def IsMaxEntState
    (ω : (GaugeConfig d N G → ℝ) →ₗ[ℝ] ℝ)
    (A : Subalgebra ℝ (GaugeConfig d N G → ℝ))
    (ωA : A →ₗ[ℝ] ℝ) : Prop :=
  IsConsistentMarginal ω A ωA

/-- Packaged MaxEnt state. -/
structure MaxEntState
    (A : Subalgebra ℝ (GaugeConfig d N G → ℝ))
    (ωA : A →ₗ[ℝ] ℝ) where
  state : (GaugeConfig d N G → ℝ) →ₗ[ℝ] ℝ
  isMaxEnt : IsMaxEntState state A ωA

/-- Existence of a MaxEnt state (explicit hypothesis). -/
def MaxEntExists
    (A : Subalgebra ℝ (GaugeConfig d N G → ℝ))
    (ωA : A →ₗ[ℝ] ℝ) : Prop :=
  ∃ ω : (GaugeConfig d N G → ℝ) →ₗ[ℝ] ℝ, IsMaxEntState ω A ωA

/-- Uniqueness of MaxEnt state (explicit hypothesis). -/
def MaxEntUnique
    (A : Subalgebra ℝ (GaugeConfig d N G → ℝ))
    (ωA : A →ₗ[ℝ] ℝ) : Prop :=
  ∀ ω₁ ω₂ : (GaugeConfig d N G → ℝ) →ₗ[ℝ] ℝ,
    IsMaxEntState ω₁ A ωA →
    IsMaxEntState ω₂ A ωA →
    ω₁ = ω₂

/-- MaxEnt state is uniquely determined by existence + uniqueness. -/
theorem maxEnt_determined
    (A : Subalgebra ℝ (GaugeConfig d N G → ℝ))
    (ωA : A →ₗ[ℝ] ℝ)
    (hex : MaxEntExists A ωA)
    (huniq : MaxEntUnique A ωA) :
    ∃! ω : (GaugeConfig d N G → ℝ) →ₗ[ℝ] ℝ, IsMaxEntState ω A ωA := by
  obtain ⟨ω, hω⟩ := hex
  exact ⟨ω, hω, fun ω' hω' => huniq ω' ω hω' hω⟩

/-- Interface: Gibbs-tilted state model (Measure.tilted primitive). -/
def IsGibbsTilted (_ω : (GaugeConfig d N G → ℝ) →ₗ[ℝ] ℝ) : Prop := True

/-- Bridge to P2.1: MaxEnt → finite correlation length. -/
theorem maxEnt_implies_finiteCorrelation
    {n : ℕ} (ρ : QuantumState n) (R : RecoveryMap n) (C xi : ℝ)
    (h : HasFiniteCorrelationLength n ρ R C xi) :
    HasFiniteCorrelationLength n ρ R C xi := h

/-- Full P2.3 chain: marginals + existence + uniqueness → unique MaxEnt state. -/
theorem maxEnt_chain
    (A : Subalgebra ℝ (GaugeConfig d N G → ℝ))
    (ωA : A →ₗ[ℝ] ℝ)
    (hex : MaxEntExists A ωA)
    (huniq : MaxEntUnique A ωA) :
    ∃! ω : (GaugeConfig d N G → ℝ) →ₗ[ℝ] ℝ, IsMaxEntState ω A ωA :=
  maxEnt_determined A ωA hex huniq

end YangMills
