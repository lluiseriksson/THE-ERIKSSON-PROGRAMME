import YangMills.L8_Terminal.ClayStrongFromFeynmanKac
import YangMills.L7_Continuum.ContinuumLimit

namespace YangMills

variable {G : Type*} [Group G] [TopologicalSpace G] [CompactSpace G] [T2Space G]
         [MeasurableSpace G] [BorelSpace G]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {d : ℕ} [NeZero d]

open MeasureTheory

structure ClayStrongFromFeynmanKacTheoremBundle
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ) (F : G → ℝ)
    (distP : (Nn : ℕ) → ConcretePlaquette d Nn → ConcretePlaquette d Nn → ℝ)
    (T P₀ : H →L[ℝ] H) (ψ_obs : (Nn : ℕ) → ConcretePlaquette d Nn → H)
    (γ C C_ψ : ℝ) where
  hCSFF : FeynmanKacBundle μ plaquetteEnergy β F distP T P₀ ψ_obs γ C C_ψ

theorem clay_theorem_of_clayStrongFromFeynmanKacTheoremBundle
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ) (F : G → ℝ)
    (distP : (Nn : ℕ) → ConcretePlaquette d Nn → ConcretePlaquette d Nn → ℝ)
    (T P₀ : H →L[ℝ] H) (ψ_obs : (Nn : ℕ) → ConcretePlaquette d Nn → H)
    (γ C C_ψ : ℝ)
    (h : ClayStrongFromFeynmanKacTheoremBundle μ plaquetteEnergy β F distP T P₀ ψ_obs γ C C_ψ)
    : ClayYangMillsTheorem := by
  obtain ⟨m_lat, hcont⟩ := clayStrong_of_feynmanKacBundle h.hCSFF
  exact continuumMassGap_pos m_lat hcont

end YangMills
