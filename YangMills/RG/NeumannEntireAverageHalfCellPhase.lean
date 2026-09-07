import YangMills.RG.BalabanCMP89Eq251EntireAverageAmplitude
import YangMills.RG.NeumannHalfCellPhase

/-!
# PRE-VALIDATION: exact half-cell phase of the actual entire average

Source present; .olean not materialized; result not compiler-verified.
The Mathlib-only repro must compile first in the same scratch import path.
This statement concerns the literal finite average, not a supplied symbol.
It does not assert Green covariance, boundary identification, a regional
inverse or uniform B0. In particular conjugation is not used off the real
slice, and neither the central mode nor N=1 is excluded.
-/

namespace YangMills.RG

open scoped BigOperators

noncomputable section

theorem neumannEntireAverageFactor_halfCellPhase (N : ℕ) (z : ℂ) :
    cmp89Eq245EntireAverageFactor N (-z) =
      Complex.exp (Complex.I * ((N : ℂ)⁻¹ * z) * ((N - 1 : ℕ) : ℂ)) *
        cmp89Eq245EntireAverageFactor N z := by
  let c : ℂ := Complex.I * ((N : ℂ)⁻¹ * z)
  have hplus : cmp89Eq245EntireAverageFactor N (-z) =
      (N : ℂ)⁻¹ * ∑ k ∈ Finset.range N, Complex.exp (c * (k : ℂ)) := by
    unfold cmp89Eq245EntireAverageFactor
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    unfold cmp89Eq245EntireAverageBase
    rw [← Complex.exp_nat_mul]
    congr 1
    dsimp [c]
    ring
  have hminus : cmp89Eq245EntireAverageFactor N z =
      (N : ℂ)⁻¹ * ∑ k ∈ Finset.range N, Complex.exp (-(c * (k : ℂ))) := by
    unfold cmp89Eq245EntireAverageFactor
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    unfold cmp89Eq245EntireAverageBase
    rw [← Complex.exp_nat_mul]
    congr 1
    dsimp [c]
    ring
  rw [hplus, hminus, NeumannHalfCellPhaseRepro.finite_exp_reverse]
  change (N : ℂ)⁻¹ * (Complex.exp (c * ((N - 1 : ℕ) : ℂ)) * _) =
    Complex.exp (c * ((N - 1 : ℕ) : ℂ)) * ((N : ℂ)⁻¹ * _)
  ring


end
end YangMills.RG

