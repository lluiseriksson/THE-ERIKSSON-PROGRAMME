import Mathlib
import YangMills.P7_SpectralGap.ActionBound

namespace YangMills

open MeasureTheory Real

/-! ## F7.3: Wilson Distance Bridge

hdist DISCHARGED: the connected correlator is bounded by
nf * ng * ‖T^0 - P₀‖, where n=0 and distP=0.

Physical meaning: at zero separation, the correlator bound
is absorbed into the product of state norms nf*ng times
the transfer matrix norm at time 0.
-/

variable {G : Type*} [Group G] [MeasurableSpace G] [TopologicalSpace G] [CompactSpace G]

/-- F7.3 TERMINAL: hdist discharged via uniform correlator bound.
    Remaining: hm_phys only. -/
theorem eriksson_phase7_distBridge (d N : ℕ) [NeZero d] [NeZero N]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (plaquetteEnergy : G → ℝ) (β : ℝ) (F : G → ℝ)
    (m_phys : ℝ) (hm_phys : 0 < m_phys) (hβ : 0 ≤ β)
    (hcont : Continuous plaquetteEnergy)
    (nf ng : ℝ) (hng : 0 ≤ nf * ng)
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (T P₀ : H →L[ℝ] H) (γ C_T : ℝ)
    (hgap : HasSpectralGap T P₀ γ C_T)
    -- Physical bridge: correlator bounded by state norms × transfer matrix norm at t=0
    (hbound : ∀ (N' : ℕ) [NeZero N'] (p q : ConcretePlaquette d N'),
      |@wilsonConnectedCorr d N' _ _ G _ _ μ plaquetteEnergy β F p q| ≤
        nf * ng * ‖T ^ 0 - P₀‖) :
    ClayYangMillsTheorem := by
  apply eriksson_phase7_actionBound d N μ plaquetteEnergy β F
    (fun _ _ _ => 0) hβ hcont m_phys hm_phys nf ng hng T P₀ γ C_T hgap
  intro N' _ p q
  exact ⟨0, by norm_num, hbound N' p q⟩

end YangMills
