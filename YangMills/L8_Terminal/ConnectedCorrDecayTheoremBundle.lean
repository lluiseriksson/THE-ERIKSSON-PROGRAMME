import YangMills.L8_Terminal.ClayPhysical
namespace YangMills
variable {G : Type*} [Group G] [TopologicalSpace G] [CompactSpace G] [T2Space G]
         [MeasurableSpace G] [BorelSpace G]
         {d : ℕ} [NeZero d]
open MeasureTheory

/-- **C118-BUNDLE**: CCD path to `ClayYangMillsTheorem`.
    Wraps `ConnectedCorrDecay` + non-negativity of `distP` and delivers the
    Clay Millennium Prize statement via the constant-profile path.
    Proof chain:
    `ConnectedCorrDecay` → `connectedCorrDecay_implies_physicalStrong_via_gen`
      → `ClayYangMillsPhysicalStrong` → `physicalStrong_implies_theorem`
      → `ClayYangMillsTheorem`. -/
structure ConnectedCorrDecayTheoremBundle
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ) (F : G → ℝ)
    (distP : (Nn : ℕ) → ConcretePlaquette d Nn → ConcretePlaquette d Nn → ℝ) where
  ccd          : ConnectedCorrDecay μ plaquetteEnergy β F distP
  distP_nonneg : ∀ (Nn : ℕ) [NeZero Nn] (p q : ConcretePlaquette d Nn), 0 ≤ distP Nn p q

theorem clay_theorem_of_connectedCorrDecayTheoremBundle
    {μ : Measure G} {plaquetteEnergy : G → ℝ} {β : ℝ} {F : G → ℝ}
    {distP : (Nn : ℕ) → ConcretePlaquette d Nn → ConcretePlaquette d Nn → ℝ}
    (h : ConnectedCorrDecayTheoremBundle μ plaquetteEnergy β F distP) :
    ClayYangMillsTheorem :=
  physicalStrong_implies_theorem μ plaquetteEnergy β F distP
    (connectedCorrDecay_implies_physicalStrong_via_gen μ plaquetteEnergy β F distP
      h.ccd h.distP_nonneg)

end YangMills
