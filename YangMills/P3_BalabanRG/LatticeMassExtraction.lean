import Mathlib
import YangMills.P3_BalabanRG.MultiscaleDecay

namespace YangMills

open MeasureTheory

/-! ## P3.4: Lattice Mass Extraction

YangMillsMassGap = ∃ m, 0 < m ∧ UniformWilsonDecay
ExtractsLatticeMassProfile = ConnectedCorrDecay → IsPositive
-/

section LatticeMassExtraction

variable {d : ℕ} [NeZero d]
variable {G : Type*} [Group G] [MeasurableSpace G]

/-- UniformWilsonDecay → YangMillsMassGap via yangMills_massGap_of_decay -/
theorem yangMillsMassGap_of_uniformDecay
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ)
    (F : G → ℝ)
    (distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ)
    (h : UniformWilsonDecay μ plaquetteEnergy β F distP) :
    YangMillsMassGap μ plaquetteEnergy β F distP :=
  yangMills_massGap_of_decay μ plaquetteEnergy β F distP h

/-- ConnectedCorrDecay → YangMillsMassGap -/
theorem yangMillsMassGap_of_connectedDecay
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ)
    (F : G → ℝ)
    (distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ)
    (h : ConnectedCorrDecay μ plaquetteEnergy β F distP) :
    YangMillsMassGap μ plaquetteEnergy β F distP :=
  yangMills_massGap_of_decay μ plaquetteEnergy β F distP h.toUniformWilsonDecay

/-- ExtractsLatticeMassProfile + ConnectedCorrDecay → IsPositive -/
theorem latticeMassIsPositive_of_connectedDecay
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ)
    (F : G → ℝ)
    (distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ)
    (m_lat : LatticeMassProfile)
    (hext : ExtractsLatticeMassProfile μ plaquetteEnergy β F distP m_lat)
    (h : ConnectedCorrDecay μ plaquetteEnergy β F distP) :
    LatticeMassProfile.IsPositive m_lat :=
  hext h

/-- HasDecayIncrement + ConnectedCorrDecay → IsPositive -/
theorem latticeMassIsPositive_of_increment
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ)
    (F : G → ℝ)
    (distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ)
    (dm : ℝ) (hdm : 0 < dm)
    (h0 : ConnectedCorrDecay μ plaquetteEnergy β F distP)
    (hinc : HasDecayIncrement μ plaquetteEnergy β F distP dm)
    (m_lat : LatticeMassProfile)
    (hext : ExtractsLatticeMassProfile μ plaquetteEnergy β F distP m_lat) :
    LatticeMassProfile.IsPositive m_lat :=
  hext h0

/-- MultiscaleDecayBound at n steps → YangMillsMassGap -/
theorem yangMillsMassGap_of_multiscale
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ)
    (F : G → ℝ)
    (distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ)
    (n : ℕ) (hn : 0 < n)
    (hms : MultiscaleDecayBound μ plaquetteEnergy β F distP n) :
    YangMillsMassGap μ plaquetteEnergy β F distP :=
  yangMills_massGap_of_decay μ plaquetteEnergy β F distP
    (uniformWilsonDecay_of_multiscale μ plaquetteEnergy β F distP n hn hms)

/-- Full Phase 3 pipeline:
    ConnectedCorrDecay + ExtractsLatticeMassProfile → IsPositive ∧ YangMillsMassGap -/
theorem phase3_full_extraction
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ)
    (F : G → ℝ)
    (distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ)
    (m_lat : LatticeMassProfile)
    (hext : ExtractsLatticeMassProfile μ plaquetteEnergy β F distP m_lat)
    (h : ConnectedCorrDecay μ plaquetteEnergy β F distP) :
    LatticeMassProfile.IsPositive m_lat ∧ YangMillsMassGap μ plaquetteEnergy β F distP :=
  ⟨hext h, yangMills_massGap_of_decay μ plaquetteEnergy β F distP h.toUniformWilsonDecay⟩

end LatticeMassExtraction

end YangMills
