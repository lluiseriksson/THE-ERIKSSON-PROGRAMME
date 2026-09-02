import YangMills.RG.BalabanCMP99SourceFlatFullPointSourceCharacterDictionary

/-!
# PRE-VALIDATION: physical target character inside one reciprocal fibre

Source is present, its promoted `.olean` has not yet been materialized, and
the result has not yet been compiler-verified.

This is the target-side companion of the source-character dictionary. It
keeps the positive Eq. (2.46) output phase and the common coarse Fourier
character separate. It does not identify the outer coarse Fourier sum,
assert a Green bound, attain window 15, discharge a terminal field or inhabit
`TermSource`.
-/

namespace YangMills.RG

noncomputable section

/-- Inside one fixed coarse reciprocal fibre, the fine target character is
the literal positive Eq. (2.46) alias phase times one common coarse target
character. -/
theorem cmp99FlatFourierMode_eq_fineTargetAliasPhase_mul_coarseMode
    {d M N' : ℕ} [NeZero M] [NeZero N']
    (ell : FinBox d N')
    (k : CMP99SourceFlatQprimeFixedCoarseFibre d M N' ell)
    (x : FinBox d (M * N')) (y : FinBox d N') :
    cmp99FlatFourierMode k.1 x =
      Complex.exp (Complex.I * cmp89Eq251EntirePhase
          (cmp89Eq248EntireAliasMomentum
            (cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum ell)
            (cmp99SourceFlatQprimeFixedCoarseSignedAliasIndexEquiv
              d M N' ell k).1)
          (cmp89Eq249PhysicalFineLatticeDisplacement ((M : ℝ)⁻¹)
            (cmp99SourceFlatQprimeFineToCoarseEndpointDisplacement M x y))) *
        cmp99FlatFourierMode ell y := by
  have hphase :=
    cmp99FlatFourierMode_div_coarseMode_eq_exp_entireAlias_endpoint
      ell k x y
  have hcoarse : cmp99FlatFourierMode ell y ≠ 0 := by
    rw [cmp99FlatFourierMode_eq_exp_entirePhase_canonicalLift]
    exact Complex.exp_ne_zero _
  apply (mul_right_cancel₀ (inv_ne_zero hcoarse))
  rw [mul_assoc, hphase]
  rw [mul_inv_cancel₀ hcoarse, mul_one]

/-- Canonical target specialization: the coarse endpoint is the actual block
owner of the fine target site. -/
theorem cmp99FlatFourierMode_eq_owned_fineTargetAliasPhase_mul_coarseMode
    {d M N' : ℕ} [NeZero M] [NeZero N']
    (ell : FinBox d N')
    (k : CMP99SourceFlatQprimeFixedCoarseFibre d M N' ell)
    (x : FinBox d (M * N')) :
    cmp99FlatFourierMode k.1 x =
      Complex.exp (Complex.I * cmp89Eq251EntirePhase
          (cmp89Eq248EntireAliasMomentum
            (cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum ell)
            (cmp99SourceFlatQprimeFixedCoarseSignedAliasIndexEquiv
              d M N' ell k).1)
          (cmp89Eq249PhysicalFineLatticeDisplacement ((M : ℝ)⁻¹)
            (cmp99SourceFlatQprimeFineToCoarseEndpointDisplacement M x
              (blockSite M N' x)))) *
        cmp99FlatFourierMode ell (blockSite M N' x) := by
  exact
    cmp99FlatFourierMode_eq_fineTargetAliasPhase_mul_coarseMode
      ell k x (blockSite M N' x)

end

end YangMills.RG
