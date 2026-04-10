import YangMills.L8_Terminal.FeynmanKacToPhysical

namespace YangMills
variable {G : Type*} [Group G] [TopologicalSpace G] [CompactSpace G] [T2Space G]
         [MeasurableSpace G] [BorelSpace G]
         {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
         {d : ℕ} [NeZero d]
open MeasureTheory

def FeynmanKacBundle
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ) (F : G → ℝ)
    (distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ)
    (T P₀ : H →L[ℝ] H) (ψ_obs : (N : ℕ) → ConcretePlaquette d N → H)
    (γ C C_ψ : ℝ) : Prop :=
  FeynmanKacFormula μ plaquetteEnergy β F distP T P₀ ψ_obs ∧
  StateNormBound ψ_obs C_ψ ∧
  HasSpectralGap T P₀ γ C ∧
  ∀ (N : ℕ) [NeZero N] (p q : ConcretePlaquette d N), 0 ≤ distP N p q

theorem physicalStrong_of_feynmanKacBundle
    {μ : Measure G} {plaquetteEnergy : G → ℝ} {β : ℝ} {F : G → ℝ}
    {distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ}
    {T P₀ : H →L[ℝ] H} {ψ_obs : (N : ℕ) → ConcretePlaquette d N → H}
    {γ C C_ψ : ℝ}
    (h : FeynmanKacBundle μ plaquetteEnergy β F distP T P₀ ψ_obs γ C C_ψ) :
    ClayYangMillsPhysicalStrong μ plaquetteEnergy β F distP :=
  feynmanKac_to_physicalStrong μ plaquetteEnergy β F distP T P₀ γ C C_ψ
    h.2.2.1 ψ_obs h.2.1 h.1 h.2.2.2

end YangMills
