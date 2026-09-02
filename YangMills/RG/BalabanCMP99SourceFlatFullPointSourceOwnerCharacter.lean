import YangMills.RG.BalabanCMP99SourceSeparatedGeneratedFlatPhysicalZeroResidueAliasing

/-!
# PRE-VALIDATION: owner character for the reflected full-G synthesis

Source is present, its promoted `.olean` has not yet been materialized, and
the result has not yet been compiler-verified.

Periodic Fourier negation turns the product of the target coarse mode and
the inverse source coarse mode into the negative DFT character at the literal
owner difference.  No Green or periodization equality enters.
-/

namespace YangMills.RG

noncomputable section

/-- Exact finite-character orientation used after reindexing the reflected
outer Eq. (2.46) synthesis by periodic Fourier negation. -/
theorem cmp99FlatFourierMode_target_mul_source_inv_eq_ownerDifferenceCharacter
    {d N : ℕ} [NeZero N]
    (ell targetOwner sourceOwner : FinBox d N) :
    cmp99FlatFourierMode ell targetOwner *
        (cmp99FlatFourierMode ell sourceOwner)⁻¹ =
      cmp99FlatZModFourierCharacter
        (-(cmp99FinBoxZModEquiv d N (cmp99FinBoxFourierNeg ell)))
        (cmp99FinBoxZModEquiv d N targetOwner -
          cmp99FinBoxZModEquiv d N sourceOwner) := by
  rw [cmp99FinBoxZModEquiv_fourierNeg, neg_neg]
  rw [cmp99FlatFourierMode_eq_finBoxFourierCharacter,
    cmp99FlatFourierMode_eq_finBoxFourierCharacter]
  rw [sub_eq_add_neg, cmp99FlatZModFourierCharacter_add_right]
  congr 1
  calc
    (cmp99FlatZModFourierCharacter
        (cmp99FinBoxZModEquiv d N ell)
        (cmp99FinBoxZModEquiv d N sourceOwner))⁻¹ =
        cmp99FlatZModFourierCharacter
          (-(cmp99FinBoxZModEquiv d N ell))
          (cmp99FinBoxZModEquiv d N sourceOwner) :=
      (cmp99FlatZModFourierCharacter_neg_left _ _).symm
    _ = cmp99FlatZModFourierCharacter
          (-(cmp99FinBoxZModEquiv d N sourceOwner))
          (cmp99FinBoxZModEquiv d N ell) :=
      cmp99FlatZModFourierCharacter_neg_swap _ _
    _ = cmp99FlatZModFourierCharacter
          (cmp99FinBoxZModEquiv d N ell)
          (-(cmp99FinBoxZModEquiv d N sourceOwner)) :=
      cmp99FlatZModFourierCharacter_comm _ _

end

end YangMills.RG
