import YangMills.L8_Terminal.ClayPhysical

namespace YangMills

variable {G : Type*} [Group G] [TopologicalSpace G] [CompactSpace G] [T2Space G]
         [MeasurableSpace G] [BorelSpace G]
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
variable {d : ℕ} [NeZero d]

open MeasureTheory

/-- Packages `physicalStrong_of_NdepGap` (C76-B) into a bundle structure.

    The N-dependent gap path to `ClayYangMillsPhysicalStrong`: uses the spectral
    gap `y_lat N` of the N-th transfer matrix directly as the lattice mass profile,
    bypassing `ConnectedCorrDecay` and `constantMassProfile`. Callers supply a
    family of N-dependent spectral gaps, a uniform amplitude bound, a
    distance-compatible correlator estimate, and `HasContinuumMassGap`. -/
structure NdepGapBundle
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ) (F : G → ℝ)
    (distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ)
    (getT getP₀ : ℕ → H →L[ℝ] H) (getC : ℕ → ℝ)
    (y_lat : LatticeMassProfile) (nf ng C : ℝ) where
  hng    : 0 ≤ nf * ng
  hgap   : ∀ Nn, HasSpectralGap (getT Nn) (getP₀ Nn) (y_lat Nn) (getC Nn)
  hy_pos : y_lat.IsPositive
  hC     : 0 < C
  hC_ub  : ∀ Nn, nf * ng * getC Nn ≤ C
  hdist  : ∀ (Nn : ℕ) [NeZero Nn] (p q : ConcretePlaquette d Nn),
      ∃ n : ℕ, distP Nn p q ≤ (n : ℝ) ∧
      |@wilsonConnectedCorr d Nn _ _ G _ _ μ plaquetteEnergy β F p q|
          ≤ nf * ng * ‖(getT Nn) ^ n - (getP₀ Nn)‖
  hcont  : HasContinuumMassGap y_lat

theorem physicalStrong_of_nDepGapBundle
    {μ : Measure G} {plaquetteEnergy : G → ℝ} {β : ℝ} {F : G → ℝ}
    {distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ}
    {getT getP₀ : ℕ → H →L[ℝ] H} {getC : ℕ → ℝ}
    {y_lat : LatticeMassProfile} {nf ng C : ℝ}
    (h : NdepGapBundle μ plaquetteEnergy β F distP getT getP₀ getC y_lat nf ng C) :
    ClayYangMillsPhysicalStrong μ plaquetteEnergy β F distP :=
  physicalStrong_of_NdepGap μ plaquetteEnergy β F distP getT getP₀ getC y_lat nf ng
    h.hng h.hgap h.hy_pos C h.hC h.hC_ub h.hdist h.hcont

end YangMills
