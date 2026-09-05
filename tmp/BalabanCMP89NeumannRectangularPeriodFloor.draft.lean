import YangMills.RG.BalabanCMP89NeumannCenteredRectangularRepresentative

/-!
# CMP89 rectangular reflection period floor

Draft only.  This source has not been promoted or compiler-verified.

The physical side floor is kept distinct from mere side positivity.  No
common-period replacement is introduced.
-/

namespace YangMills.RG

/-- A coordinate side at least `ell` has literal reflection period at least
`ell`.  The factor two is retained through the source period `2*m_mu`. -/
theorem cmp89NeumannReflectionPeriodNat_ge_scale_of_side_floor_draft
    {d ell : ℕ} {m : Fin d → ℤ}
    (hm : ∀ mu, 0 < m mu)
    (hside : ∀ mu, (ell : ℤ) ≤ m mu)
    (mu : Fin d) :
    ell ≤ cmp89NeumannReflectionPeriodNat m mu := by
  have hperiodCast := cmp89NeumannReflectionPeriodNat_cast hm mu
  have hperiodLower :
      (ell : ℤ) ≤ cmp89NeumannReflectionPeriod m mu := by
    rw [cmp89NeumannReflectionPeriod]
    nlinarith [hm mu, hside mu]
  rw [← hperiodCast] at hperiodLower
  exact_mod_cast hperiodLower

end YangMills.RG
