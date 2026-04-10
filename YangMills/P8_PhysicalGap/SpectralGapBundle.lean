import YangMills.P8_PhysicalGap.WeakContractionBundle

namespace YangMills
variable {G : Type*} [Group G] [TopologicalSpace G] [CompactSpace G] [T2Space G]
         [MeasurableSpace G] [BorelSpace G]
         {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
         {d : ℕ} [NeZero d]
open MeasureTheory

/-- PhysicalSpectralGapBundle: the most general direct path to ClayYangMillsPhysicalStrong.
    Packages PhysicalFeynmanKacFormula with an explicit spectral gap certificate
    (HasSpectralGap T P₀ γ C), bypassing all contraction conditions.
    Generalizes both PhysicalContractionBundle (C107) and
    WeakPhysicalContractionBundle (C108). -/
def PhysicalSpectralGapBundle
    (μ : MeasureTheory.Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ) (F : G → ℝ)
    (distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ)
    (T P₀ : H →L[ℝ] H) (ψ_obs : (N : ℕ) → ConcretePlaquette d N → H)
    (γ C : ℝ) : Prop :=
  PhysicalFeynmanKacFormula μ plaquetteEnergy β F distP T P₀ ψ_obs ∧
  HasSpectralGap T P₀ γ C

theorem physicalStrong_of_physicalSpectralGapBundle
    {μ : MeasureTheory.Measure G} {plaquetteEnergy : G → ℝ} {β : ℝ} {F : G → ℝ}
    {distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ}
    {T P₀ : H →L[ℝ] H} {ψ_obs : (N : ℕ) → ConcretePlaquette d N → H}
    {γ C : ℝ}
    (h : PhysicalSpectralGapBundle μ plaquetteEnergy β F distP T P₀ ψ_obs γ C) :
    ClayYangMillsPhysicalStrong μ plaquetteEnergy β F distP :=
  physicalStrong_of_physicalFormula_spectralGap h.1 h.2

end YangMills
