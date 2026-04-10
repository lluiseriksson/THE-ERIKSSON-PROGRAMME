import YangMills.L8_Terminal.ClayPhysical
namespace YangMills
variable {G : Type*} [Group G] [TopologicalSpace G] [CompactSpace G] [T2Space G]
         [MeasurableSpace G] [BorelSpace G]
         {d : ℕ} [NeZero d]
open MeasureTheory
/-- Packages ConnectedCorrDecay with a dominated LatticeMassProfile witness
    for the generalised C74-GEN path to ClayYangMillsPhysicalStrong. -/
structure ConnectedCorrDecayDomBundle
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ) (F : G → ℝ)
    (distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ) where
  ccd        : ConnectedCorrDecay μ plaquetteEnergy β F distP
  distP_nonneg : ∀ (N : ℕ) [NeZero N] (p q : ConcretePlaquette d N), 0 ≤ distP N p q
  m_lat      : LatticeMassProfile
  hdom       : ∀ N, m_lat N ≤ ccd.m
  hcont      : HasContinuumMassGap m_lat
theorem physicalStrong_of_connectedCorrDecayDomBundle
    {μ : Measure G} {plaquetteEnergy : G → ℝ} {β : ℝ} {F : G → ℝ}
    {distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ}
    (h : ConnectedCorrDecayDomBundle μ plaquetteEnergy β F distP) :
    ClayYangMillsPhysicalStrong μ plaquetteEnergy β F distP :=
  connectedCorrDecay_implies_physicalStrong_of_dominated
    μ plaquetteEnergy β F distP h.ccd h.distP_nonneg h.m_lat h.hdom h.hcont
end YangMills
