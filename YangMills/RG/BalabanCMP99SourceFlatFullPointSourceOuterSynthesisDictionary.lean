import YangMills.RG.BalabanCMP99SourceFlatFullPointSourceFibreIntegrandDictionary

/-!
# PRE-VALIDATION: reflected outer synthesis of the literal full CMP89 (2.46) kernel

Source is present, its promoted `.olean` has not yet been materialized, and
the result has not yet been compiler-verified.

This module sums the already separated one-fibre identity over the coarse
reciprocal box.  It preserves the opposite base momentum and the two
reflected physical endpoints forced by the transposed finite-fibre solve.
It does not identify this finite synthesis with a continuous integral, a
periodized infinite-volume Green, or the generated regional Green.
-/

namespace YangMills.RG

noncomputable section

/-- The internally constructed full-box point-source solution is the finite
coarse reciprocal synthesis of the reflected literal Eq. (2.46) integrand.
Both coarse endpoint characters and the inverse full-volume normalization
remain visible; no coarse-momentum reindexing or finite-grid aliasing theorem
is used in this equality. -/
theorem cmp99SourceFlatFullComplexPrecisionPointSourceSolution_apply_eq_outerIntegrandSum
    {d M N' Nc : ℕ} [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]
    (mass a : ℝ) (source target : FinBox d (M * N'))
    (v : SUNLieComplexCoord Nc) (A : Fin (Nc ^ 2 - 1)) :
    cmp99SourceFlatFullComplexPrecisionPointSourceSolution
        (d := d) (M := M) (N' := N') (Nc := Nc)
        mass a source v target A =
      ∑ ell : FinBox d N',
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
  rw [cmp99SourceFlatFullComplexPrecisionPointSourceSolution]
  simp only [WithLp.ofLp_sum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro ell _
  exact
    cmp99SourceFlatFullComplexPrecisionPointSourceFibreSolution_apply_eq_integrand
      ell mass a source target v A

end

end YangMills.RG
