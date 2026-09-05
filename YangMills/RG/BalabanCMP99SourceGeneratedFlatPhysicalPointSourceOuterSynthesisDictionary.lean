import YangMills.RG.BalabanCMP99SourceFlatFullPointSourceOuterSynthesisDictionary
import YangMills.RG.BalabanCMP99SourceGeneratedFlatPhysicalPointSourceGreenIdentification

/-!
# Generated full Green as the reflected CMP89 (2.46) outer synthesis

This is the exact composition gate after the four endpoint-character
dictionaries.  It rewrites the internally constructed periodic point-source
solution by inverse uniqueness and does not identify the remaining finite
coarse-momentum sum with a continuous integral or a periodized infinite-volume
Green.
-/

namespace YangMills.RG

open YangMills

noncomputable section

/-- The generated full periodic Green on a literal fine point source is the
reflected coarse reciprocal synthesis of the literal CMP89 (2.46) integrand.
Both endpoint owners and both reflected within-block displacements remain
visible. -/
theorem cmp99SourceGeneratedFlatPhysicalPointSourceGreen_apply_eq_outerIntegrandSum
    {M Q Nc : ℕ} [NeZero M] [NeZero Q] [NeZero Nc]
    (hM : 2 ≤ M) (depth : ℕ)
    (source target : FinBox 4 (M ^ (depth + 1) * (2 * (M * Q))))
    (v : SUNLieComplexCoord Nc) (A : Fin (Nc ^ 2 - 1)) :
    (cmp99SourceGeneratedFlatPhysicalStep7bGreenCLM
        (M := M) (Q := Q) (Nc := Nc) hM depth
        (cmp99FlatComplexFibrePointSource source v)) target A =
      ∑ ell : FinBox 4 (2 * (M * Q)),
        ((((((M ^ (depth + 1)) * (2 * (M * Q)) : ℕ) : ℂ) ^ 4)⁻¹) *
            cmp99FlatFourierMode ell
              (blockSite (M ^ (depth + 1)) (2 * (M * Q)) target) *
            (cmp99FlatFourierMode ell
              (blockSite (M ^ (depth + 1)) (2 * (M * Q)) source))⁻¹) *
          cmp89Eq246StabilizedFineToFineGreenIntegrand
            4 (M ^ (depth + 1)) 1 0
            (cmp99SourceGeneratedFullComplexA 4 M (depth + 1)
              (cmp99SourceGeneratedFullComplexSpacing M (depth + 1)) 0)
            (-cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum ell)
            (cmp89Eq249PhysicalFineLatticeDisplacement
              (((M ^ (depth + 1) : ℕ) : ℝ)⁻¹)
              (fun mu =>
                -cmp99SourceFlatQprimeFineToCoarseEndpointDisplacement
                  (M ^ (depth + 1)) target
                  (blockSite (M ^ (depth + 1)) (2 * (M * Q)) target) mu))
            (cmp89Eq249PhysicalFineLatticeDisplacement
              (((M ^ (depth + 1) : ℕ) : ℝ)⁻¹)
              (fun mu =>
                -cmp99SourceFlatQprimeFineToCoarseEndpointDisplacement
                  (M ^ (depth + 1)) source
                  (blockSite (M ^ (depth + 1)) (2 * (M * Q)) source) mu)) *
          v A := by
  rw [← cmp99SourceGeneratedFlatPhysicalPointSourceSolution_eq_green_apply
    (M := M) (Q := Q) (Nc := Nc) hM depth source v]
  exact
    cmp99SourceFlatFullComplexPrecisionPointSourceSolution_apply_eq_outerIntegrandSum
      (d := 4) (M := M ^ (depth + 1)) (N' := 2 * (M * Q)) (Nc := Nc)
      0
      (cmp99SourceGeneratedFullComplexA 4 M (depth + 1)
        (cmp99SourceGeneratedFullComplexSpacing M (depth + 1)) 0)
      source target v A

end

end YangMills.RG
