import YangMills.RG.NeumannPhysicalPeriodicTransfer
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic.Ring

/-!
# PRE-VALIDATION: integer-period source reindexing
Promoted source present; production .olean not materialized; this module is
not yet compiler-verified. Exact draft proofs passed HOT in ledger1208;
that evidence does not replace this module's pending cold gate.
This uses the literal physical endpoint transfer, not a supplied kernel law.
Only one periodic branch is summed. The tsum identity alone does not assert
summability, mixed-family coverage, a regional inverse, B0 or window15.
The preceding physical transfer is cold-sealed in ledger1205.
-/

namespace YangMills.RG
noncomputable section

def neumannPeriodicTranslateIndexEquiv {d : ℕ} (shift : Fin d → ℤ) :
    (Fin d → ℤ) ≃ (Fin d → ℤ) where
  toFun k i := k i - shift i
  invFun k i := k i + shift i
  left_inv := by intro k; funext i; simp
  right_inv := by intro k; funext i; simp

theorem neumannPeriodicTranslate_tsum_reindex
    {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    (shift : Fin d → ℤ) (f : (Fin d → ℤ) → E) :
    (∑' k : Fin d → ℤ, f (fun i => k i - shift i)) = ∑' k, f k := by
  exact (neumannPeriodicTranslateIndexEquiv shift).tsum_eq f

/-- Integer-period translation of the actual single-branch physical sum.
The fine period is L^j times blockCount; no arbitrary fine period is used.
This is an identity of totalized tsums, not a convergence certificate. -/
theorem neumannPhysicalGreen_periodicImage_tsum
    (L j : ℕ) [NeZero L] (mass a : ℝ)
    (target source blockCount : Fin 4 → ℤ) :
    (∑' k : Fin 4 → ℤ,
      cmp89Eq246NormalizedPhysicalFineToFineGreen L j mass a
        (fun mu => target mu + ((L ^ j : ℕ) : ℤ) * blockCount mu)
        (fun mu => source mu + k mu * (((L ^ j : ℕ) : ℤ) * blockCount mu))) =
    ∑' k : Fin 4 → ℤ,
      cmp89Eq246NormalizedPhysicalFineToFineGreen L j mass a target
        (fun mu => source mu + k mu * (((L ^ j : ℕ) : ℤ) * blockCount mu)) := by
  simp_rw [neumannPhysicalGreen_periodicImageTransfer]
  exact neumannPeriodicTranslate_tsum_reindex (fun _ : Fin 4 => 1)
    (fun k => cmp89Eq246NormalizedPhysicalFineToFineGreen L j mass a target
      (fun mu => source mu + k mu * (((L ^ j : ℕ) : ℤ) * blockCount mu)))

end
end YangMills.RG
