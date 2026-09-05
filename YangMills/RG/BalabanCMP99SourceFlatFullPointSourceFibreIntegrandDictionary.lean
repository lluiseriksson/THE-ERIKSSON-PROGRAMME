import YangMills.RG.BalabanCMP99SourceFlatFullPointSourceTargetCharacterDictionary

/-!
# One-fibre dictionary for the literal full CMP89 (2.46) integrand

This module keeps the target and source coarse Fourier characters visible and
identifies only the finite alias sum inside one coarse reciprocal fibre.  The
reflected momentum and endpoints are explicit consequences of the transposed
physical DFT solve, not a same-momentum self-adjointness identification.
-/

namespace YangMills.RG

noncomputable section

/-- At a fixed coarse reciprocal momentum, the internally synthesized
point-source solution is the literal full Eq. (2.46) two-endpoint integrand
at the reflected base momentum and reflected physical endpoints, times the
inverse full-volume normalization and the two coarse endpoint characters.
No outer coarse sum or generated-Green identification occurs. -/
theorem cmp99SourceFlatFullComplexPrecisionPointSourceFibreSolution_apply_eq_integrand
    {d M N' Nc : ℕ} [NeZero M] [NeZero N'] [NeZero Nc]
    (ell : FinBox d N') (mass a : ℝ)
    (source target : FinBox d (M * N')) (v : SUNLieComplexCoord Nc)
    (A : Fin (Nc ^ 2 - 1)) :
    cmp99SourceFlatFullComplexPrecisionPointSourceFibreSolution
        ell mass a source v target A =
      (((((M * N' : ℕ) : ℂ) ^ d)⁻¹) *
          cmp99FlatFourierMode ell (blockSite M N' target) *
          (cmp99FlatFourierMode ell (blockSite M N' source))⁻¹) *
        cmp89Eq246StabilizedFineToFineGreenIntegrand d M 1 mass a
          (-cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum ell)
          (cmp89Eq249PhysicalFineLatticeDisplacement ((M : ℝ)⁻¹)
            (fun mu =>
              -cmp99SourceFlatQprimeFineToCoarseEndpointDisplacement M target
                (blockSite M N' target) mu))
          (cmp89Eq249PhysicalFineLatticeDisplacement ((M : ℝ)⁻¹)
            (fun mu =>
              -cmp99SourceFlatQprimeFineToCoarseEndpointDisplacement M source
                (blockSite M N' source) mu)) *
        v A := by
  classical
  let e := cmp99SourceFlatQprimeFixedCoarseSignedAliasIndexEquiv d M N' ell
  let reflect := cmp99SourceAliasIndexOneReflection d M
  let er := e.trans reflect.symm
  let z := cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum ell
  let targetOwner := blockSite M N' target
  let sourceOwner := blockSite M N' source
  let reflectedTargetEndpoint :=
    cmp89Eq249PhysicalFineLatticeDisplacement ((M : ℝ)⁻¹)
      (fun mu =>
        -cmp99SourceFlatQprimeFineToCoarseEndpointDisplacement M target
          targetOwner mu)
  let reflectedSourceEndpoint :=
    cmp89Eq249PhysicalFineLatticeDisplacement ((M : ℝ)⁻¹)
      (fun mu =>
        -cmp99SourceFlatQprimeFineToCoarseEndpointDisplacement M source
          sourceOwner mu)
  let common := (((((M * N' : ℕ) : ℂ) ^ d)⁻¹) *
    cmp99FlatFourierMode ell targetOwner *
    (cmp99FlatFourierMode ell sourceOwner)⁻¹)
  let term : CMP89Eq246AliasIndex d M 1 → ℂ := fun n =>
    Complex.exp (Complex.I * cmp89Eq251EntirePhase
        (cmp89Eq248EntireAliasMomentum (-z) n.1) reflectedTargetEndpoint) *
      cmp89Eq246StabilizedFinePointSourceSolution
        d M 1 mass a (-z) reflectedSourceEndpoint n
  rw [cmp99SourceFlatFullComplexPrecisionPointSourceFibreSolution,
    cmp99SourceFlatFixedCoarseFibreFourierSynthesis_eq_sum]
  simp only [WithLp.ofLp_sum, Finset.sum_apply]
  calc
    _ = ∑ k : CMP99SourceFlatQprimeFixedCoarseFibre d M N' ell,
        common * (term (er k) * v A) := by
      apply Finset.sum_congr rfl
      intro k _
      have htarget :=
        cmp99FlatFourierMode_eq_owned_fineTargetAliasPhase_mul_coarseMode
          ell k target
      have hsource :=
        cmp99SourceFlatFullComplexPrecisionPointSourceFibreCoefficients_apply_eq
          ell mass a source v k A
      have htargetReflection :=
        cmp99SourceAliasIndexOneReflection_endpointPhase_eq_negDisplacement
          (-z) (reflect.symm (e k))
          (cmp99SourceFlatQprimeFineToCoarseEndpointDisplacement
            M target targetOwner)
      have hreflect : reflect (reflect.symm (e k)) = e k :=
        Equiv.apply_symm_apply reflect (e k)
      have her : er k = reflect.symm (e k) := rfl
      rw [hreflect] at htargetReflection
      simp only [neg_neg] at htargetReflection
      simp only [cmp99FlatComplexFibreFourierMode, PiLp.smul_apply, smul_eq_mul]
      rw [htarget, hsource, htargetReflection]
      rw [her]
      simp only [common, term, e, reflect, z, targetOwner, sourceOwner,
        reflectedTargetEndpoint, reflectedSourceEndpoint]
      ring
    _ = ∑ n : CMP89Eq246AliasIndex d M 1,
        common * (term n * v A) := by
      exact Equiv.sum_comp er (fun n => common * (term n * v A))
    _ = common * ((∑ n : CMP89Eq246AliasIndex d M 1, term n) * v A) := by
      rw [← Finset.mul_sum, Finset.sum_mul]
    _ = common *
        (cmp89Eq246StabilizedFineToFineGreenIntegrand
          d M 1 mass a (-z) reflectedTargetEndpoint reflectedSourceEndpoint *
            v A) := by
      rfl
    _ = _ := by
      simp only [common, z, targetOwner, sourceOwner,
        reflectedTargetEndpoint, reflectedSourceEndpoint]
      ring

end

end YangMills.RG
