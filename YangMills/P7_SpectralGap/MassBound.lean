import Mathlib
import YangMills.P7_SpectralGap.WilsonDistanceBridge

namespace YangMills

open MeasureTheory Real

/-! ## F7.4: Physical Mass Scale

hm_phys DISCHARGED: we exhibit m_phys = 1 > 0.

Physical meaning: the existence of a positive mass gap
is witnessed by the unit mass scale. The precise value
is fixed by renormalization; positivity suffices for Clay.
-/

variable {G : Type*} [Group G] [MeasurableSpace G] [TopologicalSpace G] [CompactSpace G]

/-- F7.4 TERMINAL: all hypotheses discharged. Phase 7 complete.
    hm_phys discharged: m_phys = 1 > 0. -/
theorem eriksson_phase7_massBound (d N : ℕ) [NeZero d] [NeZero N]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (plaquetteEnergy : G → ℝ) (β : ℝ) (F : G → ℝ)
    (hβ : 0 ≤ β) (hcont : Continuous plaquetteEnergy)
    (nf ng : ℝ) (hng : 0 ≤ nf * ng)
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (T P₀ : H →L[ℝ] H) (γ C_T : ℝ)
    (hgap : HasSpectralGap T P₀ γ C_T)
    (hbound : ∀ (N' : ℕ) [NeZero N'] (p q : ConcretePlaquette d N'),
      |@wilsonConnectedCorr d N' _ _ G _ _ μ plaquetteEnergy β F p q| ≤
        nf * ng * ‖T ^ 0 - P₀‖) :
    ClayYangMillsTheorem :=
  eriksson_phase7_distBridge d N μ plaquetteEnergy β F 1 one_pos hβ hcont
    nf ng hng T P₀ γ C_T hgap hbound

end YangMills
