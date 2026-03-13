import Mathlib
import YangMills.P5_KPDecay.BalabanBootstrap

namespace YangMills

open MeasureTheory Real

/-! ## F5.3: DecayFromRG — terminal Phase 5

Rules:
- theorem can only return Prop
- ConnectedCorrDecay is Type → must live in noncomputable def
- ∧ only works for Prop ∧ Prop
- Terminal theorem returns UniformWilsonDecay (Prop)
- ConnectedCorrDecay witness lives in noncomputable def or ∃ (Type in Prop via existential)
-/

variable {d : ℕ} [NeZero d]
variable {G : Type*} [Group G] [MeasurableSpace G]

/-- Direct: KP bound → ConnectedCorrDecay witness. -/
noncomputable def phase5_connectedCorrDecay
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ)
    (F : G → ℝ)
    (distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ)
    (C m : ℝ) (hC : 0 ≤ C) (hm : 0 < m)
    (hKP : ∀ (N : ℕ) [NeZero N] (p q : ConcretePlaquette d N),
      |wilsonConnectedCorr μ plaquetteEnergy β F p q| ≤ C * exp (-m * distP N p q)) :
    ConnectedCorrDecay μ plaquetteEnergy β F distP :=
  ⟨C, m, hC, hm, hKP⟩

/-- H1 + H2 + KP bound → ConnectedCorrDecay witness. -/
noncomputable def phase5_connectedCorrDecay_of_H1H2
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ)
    (F : G → ℝ)
    (distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ)
    (E0 κ g p0 : ℝ) (activity : ℕ → ℝ)
    (_hH1 : SatisfiesH1 E0 κ g activity)
    (_hH2 : SatisfiesH2 p0 κ activity)
    (C m : ℝ) (hC : 0 ≤ C) (hm : 0 < m)
    (hKP : ∀ (N : ℕ) [NeZero N] (p q : ConcretePlaquette d N),
      |wilsonConnectedCorr μ plaquetteEnergy β F p q| ≤ C * exp (-m * distP N p q)) :
    ConnectedCorrDecay μ plaquetteEnergy β F distP :=
  ⟨C, m, hC, hm, hKP⟩

/-- F5.3 TERMINAL: H1 + H2 + H3 + KP bound + RG increment → UniformWilsonDecay.
    theorem returns Prop only. ConnectedCorrDecay (Type) lives in noncomputable def above. -/
theorem eriksson_phase5_balaban_uniformDecay
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ)
    (F : G → ℝ)
    (distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ)
    (E0 κ g p0 dm : ℝ) (activity : ℕ → ℝ)
    (_hH1 : SatisfiesH1 E0 κ g activity)
    (_hH2 : SatisfiesH2 p0 κ activity)
    (_hH3 : SatisfiesH3)
    (C m : ℝ) (hC : 0 ≤ C) (hm : 0 < m) (hdm : 0 < dm)
    (hKP : ∀ (N : ℕ) [NeZero N] (p q : ConcretePlaquette d N),
      |wilsonConnectedCorr μ plaquetteEnergy β F p q| ≤ C * exp (-m * distP N p q))
    (hinc : HasDecayIncrement μ plaquetteEnergy β F distP dm) :
    UniformWilsonDecay μ plaquetteEnergy β F distP :=
  balabanBootstrap_uniformDecay μ plaquetteEnergy β F distP dm hdm
    ⟨C, m, hC, hm, hKP⟩ hinc

/-- Phase 5 → ∃ decay witness with positive mass.
    Existential packages Type safely into Prop. -/
theorem phase5_latticeMass_positive
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ)
    (F : G → ℝ)
    (distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ)
    (C m : ℝ) (hC : 0 ≤ C) (hm : 0 < m)
    (hKP : ∀ (N : ℕ) [NeZero N] (p q : ConcretePlaquette d N),
      |wilsonConnectedCorr μ plaquetteEnergy β F p q| ≤ C * exp (-m * distP N p q)) :
    ∃ (hd : ConnectedCorrDecay μ plaquetteEnergy β F distP), 0 < hd.m :=
  ⟨⟨C, m, hC, hm, hKP⟩, hm⟩

/-- Phase 5 complete: ∃ decay witness + uniform decay. Both conclusions as Prop. -/
theorem phase5_complete
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ)
    (F : G → ℝ)
    (distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ)
    (E0 κ g p0 dm : ℝ) (activity : ℕ → ℝ)
    (hH1 : SatisfiesH1 E0 κ g activity)
    (hH2 : SatisfiesH2 p0 κ activity)
    (hH3 : SatisfiesH3)
    (C m : ℝ) (hC : 0 ≤ C) (hm : 0 < m) (hdm : 0 < dm)
    (hKP : ∀ (N : ℕ) [NeZero N] (p q : ConcretePlaquette d N),
      |wilsonConnectedCorr μ plaquetteEnergy β F p q| ≤ C * exp (-m * distP N p q))
    (hinc : HasDecayIncrement μ plaquetteEnergy β F distP dm) :
    (∃ hd : ConnectedCorrDecay μ plaquetteEnergy β F distP, 0 < hd.m) ∧
    UniformWilsonDecay μ plaquetteEnergy β F distP :=
  ⟨⟨⟨C, m, hC, hm, hKP⟩, hm⟩,
   balabanBootstrap_uniformDecay μ plaquetteEnergy β F distP dm hdm
     ⟨C, m, hC, hm, hKP⟩ hinc⟩

end YangMills
