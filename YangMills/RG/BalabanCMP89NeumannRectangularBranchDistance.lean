import YangMills.RG.BalabanCMP89NeumannRectangularAffineFibre
import YangMills.RG.BalabanCMP89SignedLatticeL1ExponentialSum

/-!
PRE-VALIDATION: source is present, its `.olean` has not yet been materialized,
and the result has not yet been verified by the Lean compiler.

Direct-distance retention across both CMP89 Neumann reflection branches.
This is the source-specific monotonicity bridge needed before the finite
`2^d` branch sum.  It does not sum image fibres, insert a Green bound, or
assert the regional representation (2.42).
-/

namespace YangMills.RG

noncomputable section

/-- In either reflection branch, the internally constructed centered
representative retains at least the direct source-site separation. -/
theorem cmp89Neumann_direct_natAbs_le_centeredBranchRepresentative
    {d : ℕ} {m x n : Fin d → ℤ}
    (hm : ∀ mu, 0 < m mu)
    (hx : x ∈ cmp89SourceNeumannBlockIntegerRectangle m)
    (hn : n ∈ cmp89SourceNeumannBlockIntegerRectangle m)
    (branch : CMP89NeumannReflectionBranch d) (mu : Fin d) :
    ((x mu - n mu).natAbs : ℤ) ≤
      ((cmp89NeumannCenteredRectangularRepresentative m hm
        (cmp89NeumannReflectionBaseResidue x n branch) mu).natAbs : ℤ) := by
  cases hbranch : branch mu with
  | false =>
      have h := cmp89NeumannCenteredRectangular_direct_natAbs_eq
        (hx mu) (hn mu)
      simpa [cmp89NeumannCenteredRectangularRepresentative,
        cmp89NeumannReflectionBaseResidue,
        cmp89NeumannReflectionPeriodNat,
        cmp89NeumannReflectionPeriod, hbranch] using le_of_eq h.symm
  | true =>
      have h := cmp89Neumann_direct_natAbs_le_centeredReflectedRepresentative
        (hx mu) (hn mu)
      simpa [cmp89NeumannCenteredRectangularRepresentative,
        cmp89NeumannReflectionBaseResidue,
        cmp89NeumannReflectionPeriodNat,
        cmp89NeumannReflectionPeriod, hbranch] using h

/-- Positive decay turns the preceding distance comparison into the required
upper bound on the literal signed-lattice `l1` exponential weight. -/
theorem cmp89Neumann_centeredBranchWeight_le_directWeight
    {d : ℕ} {delta : ℝ} (hdelta : 0 ≤ delta)
    {m x n : Fin d → ℤ}
    (hm : ∀ mu, 0 < m mu)
    (hx : x ∈ cmp89SourceNeumannBlockIntegerRectangle m)
    (hn : n ∈ cmp89SourceNeumannBlockIntegerRectangle m)
    (branch : CMP89NeumannReflectionBranch d) :
    cmp89SignedLatticeL1ExponentialWeight delta
        (cmp89NeumannCenteredRectangularRepresentative m hm
          (cmp89NeumannReflectionBaseResidue x n branch)) ≤
      cmp89SignedLatticeL1ExponentialWeight delta (x - n) := by
  rw [cmp89SignedLatticeL1ExponentialWeight_eq_exp_sum_natAbs,
    cmp89SignedLatticeL1ExponentialWeight_eq_exp_sum_natAbs]
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonpos_left _ (neg_nonpos.mpr hdelta)
  apply Finset.sum_le_sum
  intro mu _
  exact_mod_cast
    cmp89Neumann_direct_natAbs_le_centeredBranchRepresentative
      hm hx hn branch mu

end

end YangMills.RG
