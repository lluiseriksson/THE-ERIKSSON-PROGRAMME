import Mathlib
import YangMills.L5_MassGap.MassGap

namespace YangMills

open MeasureTheory

/-! ## L6.1: Feynman-Kac bridge

This file builds the bridge between:
- `transferOperatorFn` (raw lattice operator, L4.3)
- `wilsonConnectedCorr` (concrete Wilson correlations, L4.2)
- `HasSpectralGap` (abstract Banach space, L4.3)

Strategy:
1. Define raw iterates `transferIterateFn = transferOperatorFn^[n]`
2. Define matrix elements as integrals against the Gibbs measure
3. State `feynmanKac_decay`: spectral gap → matrix element decay
4. State `FeynmanKacWilsonBridge`: connects to Wilson correlations
5. State `transfer_to_wilson_decay`: assembles the full bridge

The hard analytic content (OS reconstruction, Lp boundedness) remains
as an explicit hypothesis `h_rec` for future layers.
-/

variable {d N : ℕ} [NeZero d] [NeZero N]
variable {G : Type*} [Group G] [MeasurableSpace G]
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-! ### Raw transfer iterates -/

/-- n-fold iterate of the transfer operator on observables. -/
noncomputable def transferIterateFn
    (plaquetteEnergy : G → ℝ) (β : ℝ) (μ : Measure G) (n : ℕ) :
    (GaugeConfig d N G → ℝ) → GaugeConfig d N G → ℝ :=
  (transferOperatorFn plaquetteEnergy β μ)^[n]

/-- Zero iterate is the identity. -/
lemma transferIterateFn_zero
    (plaquetteEnergy : G → ℝ) (β : ℝ) (μ : Measure G)
    (f : GaugeConfig d N G → ℝ) :
    transferIterateFn plaquetteEnergy β μ 0 f = f := rfl

/-- One iterate equals transferOperatorFn. -/
lemma transferIterateFn_one
    (plaquetteEnergy : G → ℝ) (β : ℝ) (μ : Measure G)
    (f : GaugeConfig d N G → ℝ) :
    transferIterateFn plaquetteEnergy β μ 1 f =
    transferOperatorFn plaquetteEnergy β μ f := rfl

/-- Successor iterate: T^(n+1) = T^n ∘ T. -/
lemma transferIterateFn_succ
    (plaquetteEnergy : G → ℝ) (β : ℝ) (μ : Measure G) (n : ℕ)
    (f : GaugeConfig d N G → ℝ) :
    transferIterateFn plaquetteEnergy β μ (n + 1) f =
    transferIterateFn plaquetteEnergy β μ n
      (transferOperatorFn plaquetteEnergy β μ f) := by
  simp [transferIterateFn, Function.iterate_succ]

/-! ### Matrix elements -/

/-- Matrix element ⟨f | T^n | g⟩ = ∫ f(A) · (T^n g)(A) dμ_Gibbs. -/
noncomputable def matrixElement
    (plaquetteEnergy : G → ℝ) (β : ℝ) (μ : Measure G) (n : ℕ)
    (f g : GaugeConfig d N G → ℝ) : ℝ :=
  ∫ A, f A * transferIterateFn plaquetteEnergy β μ n g A
    ∂(gibbsMeasure μ plaquetteEnergy β)

/-- Matrix element at n=0 is the expectation of f*g. -/
lemma matrixElement_zero
    (plaquetteEnergy : G → ℝ) (β : ℝ) (μ : Measure G)
    (f g : GaugeConfig d N G → ℝ) :
    matrixElement plaquetteEnergy β μ 0 f g =
    ∫ A, f A * g A ∂(gibbsMeasure μ plaquetteEnergy β) := by
  simp [matrixElement, transferIterateFn]

/-! ### Feynman-Kac decay -/

/-- Feynman-Kac decay: if the abstract transfer matrix T has a spectral gap γ,
    and the raw matrix elements are controlled by ‖T^n - P₀‖,
    then matrix elements decay exponentially at rate γ. -/
theorem feynmanKac_decay
    (plaquetteEnergy : G → ℝ) (β : ℝ) (μ : Measure G)
    (T P₀ : H →L[ℝ] H) (γ C : ℝ)
    (hgap : HasSpectralGap T P₀ γ C)
    (f g : GaugeConfig d N G → ℝ)
    (norm_f norm_g : ℝ) (hn : 0 ≤ norm_f * norm_g)
    (h_rec : ∀ n : ℕ, |matrixElement plaquetteEnergy β μ n f g| ≤
        norm_f * norm_g * ‖T ^ n - P₀‖) :
    ∀ n : ℕ, |matrixElement plaquetteEnergy β μ n f g| ≤
        norm_f * norm_g * C * Real.exp (-γ * n) := by
  intro n
  have hspec := hgap.2.2 n
  calc |matrixElement plaquetteEnergy β μ n f g|
      ≤ norm_f * norm_g * ‖T ^ n - P₀‖ := h_rec n
    _ ≤ norm_f * norm_g * (C * Real.exp (-γ * n)) :=
        mul_le_mul_of_nonneg_left hspec hn
    _ = norm_f * norm_g * C * Real.exp (-γ * n) := by ring

/-! ### Wilson correlation bridge -/

/-- Bridge predicate: spectral gap implies exponential decay of
    connected Wilson correlations at fixed lattice volume N. -/
def FeynmanKacWilsonBridge
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ) (F : G → ℝ)
    (distP : ConcretePlaquette d N → ConcretePlaquette d N → ℝ)
    (T P₀ : H →L[ℝ] H) : Prop :=
  ∀ γ C : ℝ, HasSpectralGap T P₀ γ C →
    ∀ p q : ConcretePlaquette d N,
      |@wilsonConnectedCorr d N _ _ G _ _ μ plaquetteEnergy β F p q| ≤
      C * Real.exp (-γ * distP p q)

/-- Assembly: spectral gap + bridge → Wilson correlation decay. -/
theorem transfer_to_wilson_decay
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ) (F : G → ℝ)
    (distP : ConcretePlaquette d N → ConcretePlaquette d N → ℝ)
    (T P₀ : H →L[ℝ] H) (γ C : ℝ)
    (hgap : HasSpectralGap T P₀ γ C)
    (hbridge : FeynmanKacWilsonBridge μ plaquetteEnergy β F distP T P₀) :
    ∀ p q : ConcretePlaquette d N,
      |@wilsonConnectedCorr d N _ _ G _ _ μ plaquetteEnergy β F p q| ≤
      C * Real.exp (-γ * distP p q) :=
  hbridge γ C hgap

/-- Uniform-in-N version: bridge for all lattice volumes simultaneously. -/
def FeynmanKacWilsonBridgeUniform
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ) (F : G → ℝ)
    (distP : ∀ N : ℕ, ConcretePlaquette d N → ConcretePlaquette d N → ℝ)
    (T P₀ : H →L[ℝ] H) : Prop :=
  ∀ γ C : ℝ, HasSpectralGap T P₀ γ C →
    ∀ (N : ℕ) [NeZero N] (p q : ConcretePlaquette d N),
      |@wilsonConnectedCorr d N _ _ G _ _ μ plaquetteEnergy β F p q| ≤
      C * Real.exp (-γ * distP N p q)

/-- The uniform bridge implies TransferWilsonBridge (used in MassGap.lean). -/
theorem feynmanKac_implies_transferBridge
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ) (F : G → ℝ)
    (distP : ∀ N : ℕ, ConcretePlaquette d N → ConcretePlaquette d N → ℝ)
    (T P₀ : H →L[ℝ] H)
    (hfk : FeynmanKacWilsonBridgeUniform μ plaquetteEnergy β F distP T P₀) :
    TransferWilsonBridge μ plaquetteEnergy β F distP T P₀ :=
  hfk

end YangMills
