import YangMills.RG.BalabanCMP99SourceFlatFullPointSourceOwnerCharacter

/-!
# Reversed-owner character below the reflected outer synthesis

This helper rewrites the already named target/source owner
coefficient in the exact orientation consumed by physical finite-grid
aliasing.  The half-open periodic negative is eliminated through its sealed
`ZMod` image; no equality of natural representatives is assumed.
-/

namespace YangMills.RG

noncomputable section

/-- The reflected owner coefficient is the negative physical DFT character
at the reversed owner difference. -/
theorem cmp99FlatFourierMode_target_mul_source_inv_eq_reversedOwnerDifferenceCharacter
    {d N : ℕ} [NeZero N]
    (ell targetOwner sourceOwner : FinBox d N) :
    cmp99FlatFourierMode ell targetOwner *
        (cmp99FlatFourierMode ell sourceOwner)⁻¹ =
      cmp99FlatZModFourierCharacter
        (-(cmp99FinBoxZModEquiv d N ell))
        (cmp99FinBoxZModEquiv d N sourceOwner -
          cmp99FinBoxZModEquiv d N targetOwner) := by
  rw [cmp99FlatFourierMode_target_mul_source_inv_eq_ownerDifferenceCharacter]
  rw [cmp99FinBoxZModEquiv_fourierNeg, neg_neg]
  calc
    cmp99FlatZModFourierCharacter
        (cmp99FinBoxZModEquiv d N ell)
        (cmp99FinBoxZModEquiv d N targetOwner -
          cmp99FinBoxZModEquiv d N sourceOwner) =
      cmp99FlatZModFourierCharacter
        (cmp99FinBoxZModEquiv d N targetOwner -
          cmp99FinBoxZModEquiv d N sourceOwner)
        (cmp99FinBoxZModEquiv d N ell) :=
      cmp99FlatZModFourierCharacter_comm _ _
    _ = cmp99FlatZModFourierCharacter
        (-(cmp99FinBoxZModEquiv d N sourceOwner -
          cmp99FinBoxZModEquiv d N targetOwner))
        (cmp99FinBoxZModEquiv d N ell) := by
      congr 1
      abel
    _ = cmp99FlatZModFourierCharacter
        (-(cmp99FinBoxZModEquiv d N ell))
        (cmp99FinBoxZModEquiv d N sourceOwner -
          cmp99FinBoxZModEquiv d N targetOwner) :=
      (cmp99FlatZModFourierCharacter_neg_swap _ _).symm

end

end YangMills.RG
