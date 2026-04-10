import YangMills.L8_Terminal.FeynmanKacStrongBundle
import YangMills.L7_Continuum.ContinuumLimit

namespace YangMills

variable {G : Type*} [Group G] [MeasurableSpace G] [TopologicalSpace G] [CompactSpace G]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {d : ℕ} [NeZero d]

open MeasureTheory Real
open scoped InnerProductSpace

structure FeynmanKacStrongTheoremBundle
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ) (F : G → ℝ)
    (distP : (Nn : ℕ) → ConcretePlaquette d Nn → ConcretePlaquette d Nn → ℝ)
    (T P₀ : H →L[ℝ] H) (γ C Cψ : ℝ)
    (ψ_obs : (Nn : ℕ) → ConcretePlaquette d Nn → H) where
  hFKSB : FeynmanKacStrongBundle μ plaquetteEnergy β F distP T P₀ γ C Cψ ψ_obs

theorem clay_theorem_of_feynmanKacStrongTheoremBundle
    {μ : Measure G} {plaquetteEnergy : G → ℝ} {β : ℝ} {F : G → ℝ}
    {distP : (Nn : ℕ) → ConcretePlaquette d Nn → ConcretePlaquette d Nn → ℝ}
    {T P₀ : H →L[ℝ] H} {γ C Cψ : ℝ}
    {ψ_obs : (Nn : ℕ) → ConcretePlaquette d Nn → H}
    (h : FeynmanKacStrongTheoremBundle μ plaquetteEnergy β F distP T P₀ γ C Cψ ψ_obs) :
    ClayYangMillsTheorem := by
  obtain ⟨m_lat, hcont⟩ := strong_of_feynmanKacStrongBundle h.hFKSB
  exact continuumMassGap_pos m_lat hcont

end YangMills
