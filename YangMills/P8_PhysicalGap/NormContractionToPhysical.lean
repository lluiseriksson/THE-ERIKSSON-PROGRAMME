import YangMills.P8_PhysicalGap.UnitObsToPhysicalStrong
import YangMills.P8_PhysicalGap.NormBoundToSpectralGap

namespace YangMills

variable {G : Type*} [Group G] [TopologicalSpace G] [CompactSpace G] [T2Space G]
         [MeasurableSpace G] [BorelSpace G]
         {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
         {d : ℕ} [NeZero d]

open MeasureTheory

/-- HasNormContraction T P₀: P₀ is idempotent, T and P₀ satisfy the projection
    identities T*P₀ = P₀ and P₀*T = P₀, and the contraction bound 0 < ‖T - P₀‖ < 1.
    This is a concrete operator-norm condition that implies HasSpectralGap
    via spectralGap_of_normContraction_via_le. It is strictly easier to verify
    than HasSpectralGap (which requires bounding all powers T^n). -/
def HasNormContraction (T P₀ : H →L[ℝ] H) : Prop :=
  P₀ * P₀ = P₀ ∧ T * P₀ = P₀ ∧ P₀ * T = P₀ ∧ 0 < ‖T - P₀‖ ∧ ‖T - P₀‖ < 1

/-- HasNormContraction implies HasSpectralGap with explicit gap and constant. -/
theorem spectralGap_of_hasNormContraction
    {T P₀ : H →L[ℝ] H}
    (h : HasNormContraction T P₀) :
    HasSpectralGap T P₀ (-Real.log ‖T - P₀‖) (‖(1 : H →L[ℝ] H) - P₀‖ + 1) :=
  spectralGap_of_normContraction_via_le T P₀ h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2

/-- Main C106 theorem: PhysicalFeynmanKacFormula + HasNormContraction imply
    ClayYangMillsPhysicalStrong. HasNormContraction replaces HasSpectralGap
    with a more concrete, directly checkable hypothesis. -/
theorem physicalStrong_of_physicalFormula_normContraction
    {μ : MeasureTheory.Measure G} {plaquetteEnergy : G → ℝ} {β : ℝ} {F : G → ℝ}
    {distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ}
    {T P₀ : H →L[ℝ] H} {ψ_obs : (N : ℕ) → ConcretePlaquette d N → H}
    (hpFK : PhysicalFeynmanKacFormula μ plaquetteEnergy β F distP T P₀ ψ_obs)
    (hnc : HasNormContraction T P₀) :
    ClayYangMillsPhysicalStrong μ plaquetteEnergy β F distP :=
  physicalStrong_of_physicalFormula_spectralGap hpFK
    (spectralGap_of_hasNormContraction hnc)

end YangMills
