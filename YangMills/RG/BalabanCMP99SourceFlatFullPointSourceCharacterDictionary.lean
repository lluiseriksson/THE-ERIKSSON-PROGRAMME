import YangMills.RG.BalabanCMP89Eq246FinePointSourceFibreGreen
import YangMills.RG.BalabanCMP89Eq246StabilizedAliasTransposeFullSolutionLinearity
import YangMills.RG.BalabanCMP99SourceFlatFullComplexPrecisionPointSourceSolution
import YangMills.RG.BalabanCMP99SourceFlatQprimeEndpointAliasPhase

/-!
# PRE-VALIDATION: physical point-source character inside one reciprocal fibre

Source is present, its promoted `.olean` has not yet been materialized, and
the result has not yet been compiler-verified.

This module isolates the source-side dictionary needed to compare the
periodic point-source construction with the literal full Eq. (2.46)
integrand. The inverse fine Fourier character is not identified silently
with the Eq. (2.46) source vector: one common inverse coarse character remains
and is pulled outside the transposed solve only by the preceding linearity
theorem.

It does not identify the target character, finish the outer coarse Fourier
sum, produce a physical Green decay bound, attain window 15, discharge a
terminal field or inhabit `TermSource`.
-/

namespace YangMills.RG

noncomputable section

/-- Inside one fixed coarse reciprocal fibre, the inverse fine Fourier
character factors into the literal Eq. (2.46) point-source alias vector and
one common inverse coarse character. The endpoint is the signed displacement
from the fine site to the selected coarse site, in the exact `M^-1` physical
units used by the depth-one CMP89 dictionary. -/
theorem cmp99FlatFourierMode_inv_eq_finePointSourceAliasVector_mul_coarseMode_inv
    {d M N' : ℕ} [NeZero M] [NeZero N']
    (ell : FinBox d N')
    (k : CMP99SourceFlatQprimeFixedCoarseFibre d M N' ell)
    (x : FinBox d (M * N')) (y : FinBox d N') :
    (cmp99FlatFourierMode k.1 x)⁻¹ =
      cmp89Eq246FinePointSourceAliasVector d M 1
          (cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum ell)
          (cmp89Eq249PhysicalFineLatticeDisplacement ((M : ℝ)⁻¹)
            (cmp99SourceFlatQprimeFineToCoarseEndpointDisplacement M x y))
          (cmp99SourceFlatQprimeFixedCoarseSignedAliasIndexEquiv
            d M N' ell k) *
        (cmp99FlatFourierMode ell y)⁻¹ := by
  let sourceEndpoint :=
    cmp89Eq249PhysicalFineLatticeDisplacement ((M : ℝ)⁻¹)
      (cmp99SourceFlatQprimeFineToCoarseEndpointDisplacement M x y)
  let aliasIndex :=
    cmp99SourceFlatQprimeFixedCoarseSignedAliasIndexEquiv d M N' ell k
  have hphase :=
    cmp99FlatFourierMode_div_coarseMode_eq_exp_entireAlias_endpoint
      ell k x y
  have hcoarse : cmp99FlatFourierMode ell y ≠ 0 := by
    rw [cmp99FlatFourierMode_eq_exp_entirePhase_canonicalLift]
    exact Complex.exp_ne_zero _
  have hinv :
      (cmp99FlatFourierMode k.1 x)⁻¹ * cmp99FlatFourierMode ell y =
        cmp89Eq246FinePointSourceAliasVector d M 1
          (cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum ell)
          sourceEndpoint aliasIndex := by
    calc
      (cmp99FlatFourierMode k.1 x)⁻¹ * cmp99FlatFourierMode ell y =
          (cmp99FlatFourierMode k.1 x *
            (cmp99FlatFourierMode ell y)⁻¹)⁻¹ := by
              simp only [mul_inv_rev, inv_inv]
              ring
      _ = (Complex.exp (Complex.I * cmp89Eq251EntirePhase
          (cmp89Eq248EntireAliasMomentum
            (cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum ell) aliasIndex.1)
          sourceEndpoint))⁻¹ := by
            simpa only [sourceEndpoint, aliasIndex] using
              congrArg (fun w : ℂ => w⁻¹) hphase
      _ = cmp89Eq246FinePointSourceAliasVector d M 1
          (cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum ell)
          sourceEndpoint aliasIndex := by
            rw [← Complex.exp_neg]
            rfl
  apply (mul_right_cancel₀ hcoarse)
  rw [hinv, mul_assoc, inv_mul_cancel₀ hcoarse, mul_one]

/-- Canonical physical specialization: the coarse endpoint is the actual
block owner of the fine source site, not a freely supplied point. -/
theorem cmp99FlatFourierMode_inv_eq_owned_finePointSourceAliasVector_mul_coarseMode_inv
    {d M N' : ℕ} [NeZero M] [NeZero N']
    (ell : FinBox d N')
    (k : CMP99SourceFlatQprimeFixedCoarseFibre d M N' ell)
    (x : FinBox d (M * N')) :
    (cmp99FlatFourierMode k.1 x)⁻¹ =
      cmp89Eq246FinePointSourceAliasVector d M 1
          (cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum ell)
          (cmp89Eq249PhysicalFineLatticeDisplacement ((M : ℝ)⁻¹)
            (cmp99SourceFlatQprimeFineToCoarseEndpointDisplacement M x
              (blockSite M N' x)))
          (cmp99SourceFlatQprimeFixedCoarseSignedAliasIndexEquiv
            d M N' ell k) *
        (cmp99FlatFourierMode ell (blockSite M N' x))⁻¹ := by
  exact
    cmp99FlatFourierMode_inv_eq_finePointSourceAliasVector_mul_coarseMode_inv
      ell k x (blockSite M N' x)

/-- Coordinatewise factorization of the fixed-fibre point-source
coefficients. After the source endpoint is split into its coarse owner and
within-block displacement, the only remaining coarse dependence is one
common Fourier character. Both uses of scalar linearity are explicit: first
the coarse character, then the Lie-coordinate amplitude. -/
theorem cmp99SourceFlatFullComplexPrecisionPointSourceFibreCoefficients_apply_eq
    {d M N' Nc : ℕ} [NeZero M] [NeZero N'] [NeZero Nc]
    (ell : FinBox d N') (mass a : ℝ)
    (x : FinBox d (M * N')) (v : SUNLieComplexCoord Nc)
    (k : CMP99SourceFlatQprimeFixedCoarseFibre d M N' ell)
    (A : Fin (Nc ^ 2 - 1)) :
    cmp99SourceFlatFullComplexPrecisionPointSourceFibreCoefficients
        ell mass a x v k A =
      (cmp99FlatFourierMode ell (blockSite M N' x))⁻¹ *
        (cmp89Eq246StabilizedFinePointSourceSolution d M 1 mass a
            (cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum ell)
            (cmp89Eq249PhysicalFineLatticeDisplacement ((M : ℝ)⁻¹)
              (cmp99SourceFlatQprimeFineToCoarseEndpointDisplacement M x
                (blockSite M N' x)))
            (cmp99SourceFlatQprimeFixedCoarseSignedAliasIndexEquiv
              d M N' ell k) * v A) := by
  classical
  let e := cmp99SourceFlatQprimeFixedCoarseSignedAliasIndexEquiv d M N' ell
  let z := cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum ell
  let owner := blockSite M N' x
  let sourceEndpoint :=
    cmp89Eq249PhysicalFineLatticeDisplacement ((M : ℝ)⁻¹)
      (cmp99SourceFlatQprimeFineToCoarseEndpointDisplacement M x owner)
  let coarseCharacter := (cmp99FlatFourierMode ell owner)⁻¹
  let pointSource := cmp89Eq246FinePointSourceAliasVector d M 1 z sourceEndpoint
  have hsource :
      (fun n : CMP89Eq246AliasIndex d M 1 =>
        (((cmp99FlatFourierMode (e.symm n).1 x)⁻¹ • v) A)) =
        fun n => (pointSource n * v A) * coarseCharacter := by
    funext n
    have hcharacter :=
      cmp99FlatFourierMode_inv_eq_owned_finePointSourceAliasVector_mul_coarseMode_inv
        ell (e.symm n) x
    simp only [e, Equiv.apply_symm_apply] at hcharacter
    simp only [PiLp.smul_apply, smul_eq_mul]
    rw [hcharacter]
    ring
  change cmp89Eq246StabilizedAliasTransposeFullSolution
      d M 1 mass a z
        (fun n => (((cmp99FlatFourierMode (e.symm n).1 x)⁻¹ • v) A))
        (e k) = _
  rw [hsource]
  rw [cmp89Eq246StabilizedAliasTransposeFullSolution_mul_right
    d M 1 mass a z (fun n => pointSource n * v A) coarseCharacter (e k)]
  rw [cmp89Eq246StabilizedAliasTransposeFullSolution_mul_right
    d M 1 mass a z pointSource (v A) (e k)]
  simp only [cmp89Eq246StabilizedFinePointSourceSolution, pointSource,
    coarseCharacter, owner, z, sourceEndpoint, e]
  ring

end

end YangMills.RG
