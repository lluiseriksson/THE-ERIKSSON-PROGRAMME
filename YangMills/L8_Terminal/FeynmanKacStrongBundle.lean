import YangMills.L8_Terminal.FeynmanKacToPhysical

namespace YangMills

variable {G : Type*} [Group G] [MeasurableSpace G] [TopologicalSpace G] [CompactSpace G]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {d : ℕ} [NeZero d]

open MeasureTheory Real
open scoped InnerProductSpace

/-- Packages FeynmanKacFormula + StateNormBound + HasSpectralGap + distP_nonneg
    into a single bundle that delivers `ClayYangMillsStrong` directly.

    This is the highest-level one-shot bundle in the L8 chain: callers who can
    supply a Feynman–Kac formula with a spectrally-gapped transfer matrix and a
    uniform observer-norm bound reach the Clay Millennium strong statement in
    one constructor application, with zero sorry and no new axioms. -/
structure FeynmanKacStrongBundle
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ) (F : G → ℝ)
    (distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ)
    (T P₀ : H →L[ℝ] H) (γ C C_ψ : ℝ)
    (ψ_obs : (N : ℕ) → ConcretePlaquette d N → H) where
  hgap   : HasSpectralGap T P₀ γ C
  hψ     : StateNormBound ψ_obs C_ψ
  hFK    : FeynmanKacFormula μ plaquetteEnergy β F distP T P₀ ψ_obs
  hdistP : ∀ (N : ℕ) [NeZero N] (p q : ConcretePlaquette d N), 0 ≤ distP N p q

theorem strong_of_feynmanKacStrongBundle
    {μ : Measure G} {plaquetteEnergy : G → ℝ} {β : ℝ} {F : G → ℝ}
    {distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ}
    {T P₀ : H →L[ℝ] H} {γ C C_ψ : ℝ}
    {ψ_obs : (N : ℕ) → ConcretePlaquette d N → H}
    (h : FeynmanKacStrongBundle μ plaquetteEnergy β F distP T P₀ γ C C_ψ ψ_obs) :
    ClayYangMillsStrong :=
  feynmanKac_to_strong μ plaquetteEnergy β F distP T P₀ γ C C_ψ
    h.hgap ψ_obs h.hψ h.hFK h.hdistP

end YangMills
