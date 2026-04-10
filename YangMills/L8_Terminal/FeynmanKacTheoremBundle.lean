import YangMills.L8_Terminal.FeynmanKacBundle
namespace YangMills
variable {G : Type*} [Group G] [TopologicalSpace G] [CompactSpace G] [T2Space G]
         [MeasurableSpace G] [BorelSpace G]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {d : ℕ} [NeZero d]
open MeasureTheory

/-- **C117-BUNDLE**: Wraps a `FeynmanKacBundle` and delivers `ClayYangMillsTheorem`
    (the Clay Millennium Prize statement: existence of a positive physical mass gap).
    Proof chain:
    `FeynmanKacBundle` → `physicalStrong_of_feynmanKacBundle`
      → `ClayYangMillsPhysicalStrong` → `physicalStrong_implies_theorem`
      → `ClayYangMillsTheorem`. -/
structure FeynmanKacTheoremBundle
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ) (F : G → ℝ)
    (distP : (Nn : ℕ) → ConcretePlaquette d Nn → ConcretePlaquette d Nn → ℝ)
    (T P₀ : H →L[ℝ] H) (ψ_obs : (Nn : ℕ) → ConcretePlaquette d Nn → H)
    (γ C C_ψ : ℝ) where
  hFKB : FeynmanKacBundle μ plaquetteEnergy β F distP T P₀ ψ_obs γ C C_ψ

theorem clay_theorem_of_feynmanKacTheoremBundle
    {μ : Measure G} {plaquetteEnergy : G → ℝ} {β : ℝ} {F : G → ℝ}
    {distP : (Nn : ℕ) → ConcretePlaquette d Nn → ConcretePlaquette d Nn → ℝ}
    {T P₀ : H →L[ℝ] H} {ψ_obs : (Nn : ℕ) → ConcretePlaquette d Nn → H}
    {γ C C_ψ : ℝ}
    (bun : FeynmanKacTheoremBundle μ plaquetteEnergy β F distP T P₀ ψ_obs γ C C_ψ) :
    ClayYangMillsTheorem :=
  physicalStrong_implies_theorem μ plaquetteEnergy β F distP
    (physicalStrong_of_feynmanKacBundle bun.hFKB)

end YangMills
