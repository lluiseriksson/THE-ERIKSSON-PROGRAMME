import YangMills.P8_PhysicalGap.NormContractionToPhysical

namespace YangMills

variable {G : Type*} [Group G] [TopologicalSpace G] [CompactSpace G] [T2Space G]
         [MeasurableSpace G] [BorelSpace G]
         {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
         {d : ℕ} [NeZero d]

open MeasureTheory

/-- PhysicalContractionBundle bundles the two remaining live hypotheses into one:
    - PhysicalFeynmanKacFormula (Feynman-Kac + unit-norm observables)
    - HasNormContraction (transfer matrix operator-norm contraction)
    This is the minimal single-hypothesis form of the C106 theorem. -/
def PhysicalContractionBundle
    (μ : MeasureTheory.Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ) (F : G → ℝ)
    (distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ)
    (T P₀ : H →L[ℝ] H) (ψ_obs : (N : ℕ) → ConcretePlaquette d N → H) : Prop :=
  PhysicalFeynmanKacFormula μ plaquetteEnergy β F distP T P₀ ψ_obs ∧
  HasNormContraction T P₀

/-- C107: Single-hypothesis theorem.
    ClayYangMillsPhysicalStrong follows from PhysicalContractionBundle alone.
    This is the sharpest current formulation: one bundled hypothesis implies
    exponential decay of Wilson loop correlators. -/
theorem physicalStrong_of_physicalContractionBundle
    {μ : MeasureTheory.Measure G} {plaquetteEnergy : G → ℝ} {β : ℝ} {F : G → ℝ}
    {distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ}
    {T P₀ : H →L[ℝ] H} {ψ_obs : (N : ℕ) → ConcretePlaquette d N → H}
    (h : PhysicalContractionBundle μ plaquetteEnergy β F distP T P₀ ψ_obs) :
    ClayYangMillsPhysicalStrong μ plaquetteEnergy β F distP :=
  physicalStrong_of_physicalFormula_normContraction h.1 h.2

end YangMills
