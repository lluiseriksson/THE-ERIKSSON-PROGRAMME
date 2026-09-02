import YangMills.RG.BalabanCMP89Eq246AliasCycleTransport

/-!
# PRE-VALIDATION: covariance of the finite CMP89 (2.46) precision under alias cycling

Source is present, its promoted `.olean` has not yet been materialized, and
the result has not yet been compiler-verified.

The physical `2*pi` shift of one coarse-momentum coordinate is transported
through the literal diagonal-plus-rank-one precision by the centered alias
permutation.  The vector identity is obtained by reindexing the finite dot
product; no matrix periodicity is postulated.
-/

namespace YangMills.RG

open Matrix

noncomputable section

private theorem cmp89Eq246AliasCycleCount_pos
    (L j : ℕ) [NeZero L] : 0 < L ^ j :=
  pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) j

/-- Entrywise covariance of the complete alias precision. -/
theorem cmp89Eq246EntireAliasPrecisionMatrix_physicalShift_eq_cycle
    (d L j : ℕ) [NeZero L] (mass a : ℝ) (mu : Fin d)
    (z : Fin d → ℂ) (m n : CMP89Eq246AliasIndex d L j) :
    cmp89Eq246EntireAliasPrecisionMatrix d L j mass a
        (cmp89Eq248PhysicalCoordinatePeriodShift mu z) m n =
      cmp89Eq246EntireAliasPrecisionMatrix d L j mass a z
        (cmp89Eq245CenteredAliasVectorCycle d (L ^ j)
          (cmp89Eq246AliasCycleCount_pos L j) mu m)
        (cmp89Eq245CenteredAliasVectorCycle d (L ^ j)
          (cmp89Eq246AliasCycleCount_pos L j) mu n) := by
  simp only [cmp89Eq246EntireAliasPrecisionMatrix,
    cmp89Eq246EntireAliasFineSymbol_physicalShift_eq_cycle,
    cmp89Eq246EntireAliasAverageColumn_physicalShift_eq_cycle,
    cmp89Eq246EntireAliasAverageRow_physicalShift_eq_cycle]
  simp

/-- The shifted precision action is the unshifted action on the vector
transported by the inverse centered-alias cycle. -/
theorem cmp89Eq246EntireAliasPrecisionMatrix_mulVec_physicalShift_eq_cycle
    (d L j : ℕ) [NeZero L] (mass a : ℝ) (mu : Fin d)
    (z : Fin d → ℂ) (phi : CMP89Eq246AliasIndex d L j → ℂ)
    (m : CMP89Eq246AliasIndex d L j) :
    (cmp89Eq246EntireAliasPrecisionMatrix d L j mass a
        (cmp89Eq248PhysicalCoordinatePeriodShift mu z)).mulVec phi m =
      (cmp89Eq246EntireAliasPrecisionMatrix d L j mass a z).mulVec
        (fun k => phi ((cmp89Eq245CenteredAliasVectorCycle d (L ^ j)
          (cmp89Eq246AliasCycleCount_pos L j) mu).symm k))
        (cmp89Eq245CenteredAliasVectorCycle d (L ^ j)
          (cmp89Eq246AliasCycleCount_pos L j) mu m) := by
  let cycle := cmp89Eq245CenteredAliasVectorCycle d (L ^ j)
    (cmp89Eq246AliasCycleCount_pos L j) mu
  let A := cmp89Eq246EntireAliasPrecisionMatrix d L j mass a z
  rw [Matrix.mulVec, dotProduct, Matrix.mulVec, dotProduct]
  calc
    (∑ n,
        cmp89Eq246EntireAliasPrecisionMatrix d L j mass a
            (cmp89Eq248PhysicalCoordinatePeriodShift mu z) m n * phi n) =
      ∑ n, A (cycle m) (cycle n) * phi n := by
        apply Finset.sum_congr rfl
        intro n _
        exact congrArg (fun c => c * phi n)
          (cmp89Eq246EntireAliasPrecisionMatrix_physicalShift_eq_cycle
            d L j mass a mu z m n)
    _ = ∑ n, (fun k => A (cycle m) k * phi (cycle.symm k)) (cycle n) := by
      simp
    _ = ∑ k, A (cycle m) k * phi (cycle.symm k) :=
      Equiv.sum_comp cycle (fun k => A (cycle m) k * phi (cycle.symm k))

end

end YangMills.RG
