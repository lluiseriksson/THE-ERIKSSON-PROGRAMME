import Mathlib
import YangMills.P8_PhysicalGap.OperatorNormBound
import YangMills.P8_PhysicalGap.ProfiledSpectralGap

/-!
# PointwiseResidualContraction -- v1.05.0
C89: pointwise residual contraction → operator norm bound → physical strong.
-/

namespace YangMills
open ContinuousLinearMap Real MeasureTheory

variable {d : ℕ} [NeZero d]
variable {G : Type*} [Group G] [MeasurableSpace G] [TopologicalSpace G] [CompactSpace G]
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- **C89-1 (sorry-free)**: Pointwise residual contraction → operator norm bound.

If ∀ x, ‖A x‖ ≤ lam * ‖x‖ then ‖A‖ ≤ lam.
Proof: direct application of ContinuousLinearMap.opNorm_le_bound.
Oracle: [propext, Classical.choice, Quot.sound]. -/
theorem opNormBound_of_pointwiseResidualContraction
    (A : H →L[ℝ] H) (lam : ℝ) (hlam : 0 ≤ lam)
    (hA : ∀ x : H, ‖A x‖ ≤ lam * ‖x‖) : ‖A‖ ≤ lam :=
  ContinuousLinearMap.opNorm_le_bound A hlam hA

/-- **C89-2 (sorry-free)**: ClayYangMillsPhysicalStrong from pointwise residual contraction.

Chain: pointwise → op-norm (C89-1) → spectral gap from exp-norm (C88)
       → physical strong (C87).
Oracle: [propext, Classical.choice, Quot.sound]. -/
theorem physicalStrong_of_profiledPointwiseResidualContraction
    {μ : Measure G} {plaquetteEnergy : G → ℝ} {β : ℝ} {F : G → ℝ}
    {distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ}
    {T P₀ : H →L[ℝ] H} {C_fk : ℝ}
    (hP₀_idem : P₀ * P₀ = P₀) (hTP : T * P₀ = P₀) (hPT : P₀ * T = P₀)
    (m : ℝ) (hm : 0 < m)
    (hpw : ∀ x : H, ‖(T - P₀) x‖ ≤ Real.exp (-m) * ‖x‖)
    (hopnorm : FeynmanKacOpNormBound μ plaquetteEnergy β F distP T P₀ C_fk)
    (hdistP : ∀ (N : ℕ) [NeZero N] (p q : ConcretePlaquette d N),
        0 ≤ distP N p q) :
    ClayYangMillsPhysicalStrong μ plaquetteEnergy β F distP :=
  physicalStrong_of_profiledExpNormBound hP₀_idem hTP hPT m hm
    (opNormBound_of_pointwiseResidualContraction (T - P₀) (Real.exp (-m))
      (Real.exp_nonneg _) hpw)
    hopnorm hdistP

end YangMills
