import YangMills.L8_Terminal.ClayPhysical

namespace YangMills
variable {G : Type*} [Group G] [TopologicalSpace G] [CompactSpace G] [T2Space G]
         [MeasurableSpace G] [BorelSpace G]
         {d : ℕ} [NeZero d]
open MeasureTheory

structure ConnectedCorrDecayBundle
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ) (F : G → ℝ)
    (distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ) where
  ccd : ConnectedCorrDecay μ plaquetteEnergy β F distP
  distP_nonneg : ∀ (N : ℕ) [NeZero N] (p q : ConcretePlaquette d N), 0 ≤ distP N p q

theorem physicalStrong_of_connectedCorrDecayBundle
    {μ : Measure G} {plaquetteEnergy : G → ℝ} {β : ℝ} {F : G → ℝ}
    {distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ}
    (h : ConnectedCorrDecayBundle μ plaquetteEnergy β F distP) :
    ClayYangMillsPhysicalStrong μ plaquetteEnergy β F distP :=
  connectedCorrDecay_implies_physicalStrong μ plaquetteEnergy β F distP h.ccd h.distP_nonneg

end YangMills
