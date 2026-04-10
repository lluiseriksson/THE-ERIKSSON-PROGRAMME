import YangMills.L8_Terminal.ConnectedCorrDecayDomBundle

namespace YangMills

variable {G : Type*} [Group G] [TopologicalSpace G] [CompactSpace G] [T2Space G]
         [MeasurableSpace G] [BorelSpace G]
         {d : ℕ} [NeZero d]

open MeasureTheory

structure ConnectedCorrDecayDomTheoremBundle
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ) (F : G → ℝ)
    (distP : (Nn : ℕ) → ConcretePlaquette d Nn → ConcretePlaquette d Nn → ℝ) where
  hCCDB : ConnectedCorrDecayDomBundle μ plaquetteEnergy β F distP

theorem clay_theorem_of_connectedCorrDecayDomTheoremBundle
    {μ : Measure G} {plaquetteEnergy : G → ℝ} {β : ℝ} {F : G → ℝ}
    {distP : (Nn : ℕ) → ConcretePlaquette d Nn → ConcretePlaquette d Nn → ℝ}
    (h : ConnectedCorrDecayDomTheoremBundle μ plaquetteEnergy β F distP) :
    ClayYangMillsTheorem :=
  physicalStrong_implies_theorem μ plaquetteEnergy β F distP
    (physicalStrong_of_connectedCorrDecayDomBundle h.hCCDB)

end YangMills
