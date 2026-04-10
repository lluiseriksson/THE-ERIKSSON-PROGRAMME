import YangMills.L8_Terminal.NdepGapBundle

namespace YangMills

variable {G : Type*} [Group G] [TopologicalSpace G] [CompactSpace G] [T2Space G]
         [MeasurableSpace G] [BorelSpace G]
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
variable {d : ℕ} [NeZero d]

open MeasureTheory

structure NdepGapTheoremBundle
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ) (F : G → ℝ)
    (distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ)
    (getT getP₀ : ℕ → H →L[ℝ] H) (getC : ℕ → ℝ)
    (y_lat : LatticeMassProfile) (nf ng C : ℝ) where
  hNGB : NdepGapBundle μ plaquetteEnergy β F distP getT getP₀ getC y_lat nf ng C

theorem clay_theorem_of_ndepGapTheoremBundle
    {μ : Measure G} {plaquetteEnergy : G → ℝ} {β : ℝ} {F : G → ℝ}
    {distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ}
    {getT getP₀ : ℕ → H →L[ℝ] H} {getC : ℕ → ℝ}
    {y_lat : LatticeMassProfile} {nf ng C : ℝ}
    (h : NdepGapTheoremBundle μ plaquetteEnergy β F distP getT getP₀ getC y_lat nf ng C) :
    ClayYangMillsTheorem :=
  physicalStrong_implies_theorem μ plaquetteEnergy β F distP
    (physicalStrong_of_nDepGapBundle h.hNGB)

end YangMills
