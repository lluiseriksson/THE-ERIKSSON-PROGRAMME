import YangMills.L8_Terminal.ClayPhysical
namespace YangMills
variable {G : Type*} [Group G] [TopologicalSpace G] [CompactSpace G] [T2Space G]
         [MeasurableSpace G] [BorelSpace G]
         {d : ℕ} [NeZero d]
open MeasureTheory

/-- **C116-BUNDLE**: Minimal certificate for `ClayYangMillsPhysicalStrong`
    via the constant-profile CCD path
    (`connectedCorrDecay_implies_physicalStrong_via_gen`).
    Fields:
    * `ccd`          : ConnectedCorrDecay certificate
    * `distP_nonneg` : non-negativity of plaquette distance -/
structure ConnectedCorrDecayBundle
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ) (F : G → ℝ)
    (distP : (Nn : ℕ) → ConcretePlaquette d Nn → ConcretePlaquette d Nn → ℝ) where
  ccd          : ConnectedCorrDecay μ plaquetteEnergy β F distP
  distP_nonneg : ∀ (Nn : ℕ) [NeZero Nn] (p q : ConcretePlaquette d Nn), 0 ≤ distP Nn p q

theorem physicalStrong_of_connectedCorrDecayBundle
    {μ : Measure G} {plaquetteEnergy : G → ℝ} {β : ℝ} {F : G → ℝ}
    {distP : (Nn : ℕ) → ConcretePlaquette d Nn → ConcretePlaquette d Nn → ℝ}
    (h : ConnectedCorrDecayBundle μ plaquetteEnergy β F distP) :
    ClayYangMillsPhysicalStrong μ plaquetteEnergy β F distP :=
  connectedCorrDecay_implies_physicalStrong_via_gen
    μ plaquetteEnergy β F distP h.ccd h.distP_nonneg

end YangMills
