import YangMills.RG.NeumannActualCommonBlockTranslation
import Mathlib.Tactic.Ring

/-!
# Physical block translation moved between endpoints
Cold-compiled at 24dc691e451ab9b6684f950a3fdd5a78e913997f.
Independent preserved evidence: ledger Addendum 1205 (2026-09-07).
The full Green is literal. This uses the cold common-block translation law,
not arbitrary fine translation and not a supplied covariance hypothesis.
For periodic images, subtracting one full block-aligned period changes k
to k-1 without introducing a second branch. Convergence, the mixed-family
coverage and the regional point-source equation are NOT proved here.
-/

namespace YangMills.RG
noncomputable section

theorem neumannPhysicalGreen_blockShiftTransfer
    (L j : ℕ) [NeZero L] (mass a : ℝ)
    (target source shift : Fin 4 → ℤ) :
    cmp89Eq246NormalizedPhysicalFineToFineGreen L j mass a
      (fun mu => target mu + ((L ^ j : ℕ) : ℤ) * shift mu) source =
    cmp89Eq246NormalizedPhysicalFineToFineGreen L j mass a target
      (fun mu => source mu - ((L ^ j : ℕ) : ℤ) * shift mu) := by
  have h := neumannActualNormalizedFineGreen_commonBlockShift L j mass a
    target (fun mu => source mu - ((L ^ j : ℕ) : ℤ) * shift mu) shift
  have hrestore : (fun mu =>
      (source mu - ((L ^ j : ℕ) : ℤ) * shift mu) +
        ((L ^ j : ℕ) : ℤ) * shift mu) = source := by
    funext mu
    ring
  rw [hrestore] at h
  exact h

/-- A full-period shift changes the integer translate, not the branch count.
`blockCount` is measured in blocks and the fine period is L^j*blockCount. -/
theorem neumannPhysicalGreen_periodicImageTransfer
    (L j : ℕ) [NeZero L] (mass a : ℝ)
    (target source blockCount k : Fin 4 → ℤ) :
    cmp89Eq246NormalizedPhysicalFineToFineGreen L j mass a
      (fun mu => target mu + ((L ^ j : ℕ) : ℤ) * blockCount mu)
      (fun mu => source mu + k mu * (((L ^ j : ℕ) : ℤ) * blockCount mu)) =
    cmp89Eq246NormalizedPhysicalFineToFineGreen L j mass a target
      (fun mu => source mu + (k mu - 1) *
        (((L ^ j : ℕ) : ℤ) * blockCount mu)) := by
  have h := neumannPhysicalGreen_blockShiftTransfer L j mass a target
    (fun mu => source mu + k mu * (((L ^ j : ℕ) : ℤ) * blockCount mu))
    blockCount
  have himage : (fun mu =>
      (source mu + k mu * (((L ^ j : ℕ) : ℤ) * blockCount mu)) -
        ((L ^ j : ℕ) : ℤ) * blockCount mu) =
      (fun mu => source mu + (k mu - 1) *
        (((L ^ j : ℕ) : ℤ) * blockCount mu)) := by
    funext mu
    ring
  rw [himage] at h
  exact h

end
end YangMills.RG
