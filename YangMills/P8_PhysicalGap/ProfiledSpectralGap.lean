/-
  C88: ProfiledSpectralGap -- spectral gap from lattice mass profile (exponential norm bound)
  Proved from C86 (spectralGap_of_norm_le) by substituting lam = exp(-m).
-/
import Mathlib
import YangMills.L8_Terminal.ClayPhysical
import YangMills.P8_PhysicalGap.NormBoundToSpectralGap
import YangMills.P8_PhysicalGap.OperatorNormBound

namespace YangMills
open ContinuousLinearMap Real MeasureTheory

variable {d : ℕ} [NeZero d]
variable {G : Type*} [Group G] [MeasurableSpace G] [TopologicalSpace G] [CompactSpace G]

section ProfiledGap
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- C88-1 (sorry-free): HasSpectralGap from exponential norm bound ‖T-P₀‖ ≤ exp(-m). -/
theorem spectralGap_of_expNormBound
    (T P₀ : H →L[ℝ] H)
    (hP₀_idem : P₀ * P₀ = P₀)
    (hTP : T * P₀ = P₀)
    (hPT : P₀ * T = P₀)
    (m : ℝ) (hm : 0 < m)
    (hbound : ‖T - P₀‖ ≤ Real.exp (-m)) :
    HasSpectralGap T P₀ m (‖(1 : H →L[ℝ] H) - P₀‖ + 1) := by
  have hlam0 : (0 : ℝ) < Real.exp (-m) := Real.exp_pos _
  have hlam1 : Real.exp (-m) < 1 := by
    rw [Real.exp_lt_one_iff]; linarith
  have hgap := spectralGap_of_norm_le T P₀ hP₀_idem hTP hPT
                 (Real.exp (-m)) hlam0 hlam1 hbound
  have hγ_eq : -Real.log (Real.exp (-m)) = m := by
    rw [Real.log_exp]; ring
  rwa [hγ_eq] at hgap

end ProfiledGap

section FullChain
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- C88-2 (sorry-free): ClayYangMillsPhysicalStrong from exponential norm bound + FeynmanKac. -/
theorem physicalStrong_of_profiledExpNormBound
    {μ : Measure G} {plaquetteEnergy : G → ℝ} {β : ℝ} {F : G → ℝ}
    {distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ}
    {T P₀ : H →L[ℝ] H} {C_fk : ℝ}
    (hP₀_idem : P₀ * P₀ = P₀)
    (hTP : T * P₀ = P₀)
    (hPT : P₀ * T = P₀)
    (m : ℝ) (hm : 0 < m)
    (hnorm : ‖T - P₀‖ ≤ Real.exp (-m))
    (hopnorm : FeynmanKacOpNormBound μ plaquetteEnergy β F distP T P₀ C_fk)
    (hdistP : ∀ (N : ℕ) [NeZero N] (p q : ConcretePlaquette d N), 0 ≤ distP N p q) :
    ClayYangMillsPhysicalStrong μ plaquetteEnergy β F distP :=
  opNormBound_to_physicalStrong hopnorm
    (spectralGap_of_expNormBound T P₀ hP₀_idem hTP hPT m hm hnorm) hdistP

end FullChain

end YangMills
