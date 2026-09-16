/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceFlatFullComplexPrecisionParticularSolution
import YangMills.RG.BalabanCMP99SourceFlatQprimePhysicalStabilizedAliasTransposeSolution

/-!
# Central-stabilized flat physical particular solution

The sealed physical central-stabilized alias vector is multiplied by the
literal fine volume and reconstructed through the physical inverse DFT.  The
literal full-box precision sends the resulting field exactly to the actual
coefficient-one weighted-adjoint coarse Fourier mode.  The proof treats the
selected reciprocal fibre and its complement separately and concludes by DFT
injectivity.

This constructs the source-shaped field `G Q'^*` on one coarse Fourier mode.
It is not called an inverse of the full precision: inverse uniqueness and the
operator dictionary remain separate downstream obligations.
-/

namespace YangMills.RG

open YangMills Matrix

noncomputable section

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

/-- Fixed-fibre coefficients of the central-stabilized physical particular
solution.  The fine volume is literal. -/
def cmp99SourceFlatFullComplexPrecisionStabilizedParticularCoefficients
    (ell : FinBox d N') (mass a : ℝ) (v : SUNLieComplexCoord Nc) :
    CMP99SourceFlatQprimeFixedCoarseFibre d M N' ell →
      SUNLieComplexCoord Nc :=
  fun k =>
    (((M * N' : ℕ) : ℂ) ^ d *
      cmp99SourceFlatQprimePhysicalStabilizedAliasTransposeSolution
        (d := d) (M := M) (N' := N') ell mass a k) • v

/-- Literal inverse-DFT reconstruction of the central-stabilized physical
particular solution on one coarse reciprocal fibre. -/
def cmp99SourceFlatFullComplexPrecisionStabilizedParticularSolution
    (ell : FinBox d N') (mass a : ℝ) (v : SUNLieComplexCoord Nc) :
    FinBox d (M * N') → SUNLieComplexCoord Nc :=
  cmp99SourceFlatFixedCoarseFibreFourierSynthesis ell
    (cmp99SourceFlatFullComplexPrecisionStabilizedParticularCoefficients
      ell mass a v)

omit [NeZero d] [NeZero Nc] in
/-- On the selected fibre, the DFT is the fine-volume multiple of the sealed
central-stabilized physical alias solution. -/
theorem cmp99FlatPhysicalFibreDFT_stabilizedParticularSolution_fixedCoarseFibre
    (ell : FinBox d N') (mass a : ℝ) (v : SUNLieComplexCoord Nc)
    (k : CMP99SourceFlatQprimeFixedCoarseFibre d M N' ell) :
    cmp99FlatPhysicalFibreDFT
        (cmp99SourceFlatFullComplexPrecisionStabilizedParticularSolution
          ell mass a v) k.1 =
      (((M * N' : ℕ) : ℂ) ^ d *
        cmp99SourceFlatQprimePhysicalStabilizedAliasTransposeSolution
          (d := d) (M := M) (N' := N') ell mass a k) • v := by
  exact cmp99FlatPhysicalFibreDFT_fixedCoarseFibreFourierSynthesis ell
    (cmp99SourceFlatFullComplexPrecisionStabilizedParticularCoefficients
      ell mass a v) k

omit [NeZero d] [NeZero Nc] in
/-- Outside the selected reciprocal fibre, the DFT of the stabilized field
vanishes by the literal zero extension. -/
theorem cmp99FlatPhysicalFibreDFT_stabilizedParticularSolution_eq_zero_of_coarseAlias_ne
    (ell : FinBox d N') (mass a : ℝ) (v : SUNLieComplexCoord Nc)
    (k : FinBox d (M * N'))
    (hk : cmp99SourceFlatQprimeCoarseAlias k ≠ ell) :
    cmp99FlatPhysicalFibreDFT
        (cmp99SourceFlatFullComplexPrecisionStabilizedParticularSolution
          ell mass a v) k = 0 := by
  rw [cmp99SourceFlatFullComplexPrecisionStabilizedParticularSolution,
    cmp99SourceFlatFixedCoarseFibreFourierSynthesis,
    cmp99FlatPhysicalFibreDFT_InvDFT]
  simp [cmp99SourceFlatFixedCoarseFibreCoefficientExtension, hk]

/-- The literal precision applied to the stabilized synthesis has zero DFT
outside its selected reciprocal fibre. -/
theorem cmp99FlatPhysicalFibreDFT_sourceFlatFullComplexPrecision_stabilizedParticularSolution_eq_zero_of_coarseAlias_ne
    (ell : FinBox d N') (mass a : ℝ) (v : SUNLieComplexCoord Nc)
    (output : FinBox d (M * N'))
    (houtput : cmp99SourceFlatQprimeCoarseAlias output ≠ ell) :
    cmp99FlatPhysicalFibreDFT
        (cmp99SourceFlatFullComplexPrecisionAction mass a
          (cmp99SourceFlatFullComplexPrecisionStabilizedParticularSolution
            ell mass a v)) output = 0 := by
  rw [cmp99SourceFlatFullComplexPrecisionStabilizedParticularSolution,
    cmp99SourceFlatFixedCoarseFibreFourierSynthesis_eq_sum]
  let term : CMP99SourceFlatQprimeFixedCoarseFibre d M N' ell →
      FinBox d (M * N') → SUNLieComplexCoord Nc :=
    fun input => cmp99FlatComplexFibreFourierMode input.1
      (((((M * N' : ℕ) : ℂ) ^ d)⁻¹) •
        cmp99SourceFlatFullComplexPrecisionStabilizedParticularCoefficients
          ell mass a v input)
  have hprecisionSum :
      cmp99SourceFlatFullComplexPrecisionAction mass a (∑ input, term input) =
        ∑ input,
          cmp99SourceFlatFullComplexPrecisionAction mass a (term input) := by
    simpa only using
      cmp99SourceFlatFullComplexPrecisionAction_finset_sum
        (d := d) (M := M) (N' := N') (Nc := Nc)
        mass a Finset.univ term
  have hterm : (fun x => ∑ input,
      cmp99FlatComplexFibreFourierMode input.1
        (((((M * N' : ℕ) : ℂ) ^ d)⁻¹) •
          cmp99SourceFlatFullComplexPrecisionStabilizedParticularCoefficients
            ell mass a v input) x) =
      ∑ input, term input := by
    funext x
    rw [Finset.sum_apply]
  rw [hterm, hprecisionSum]
  change cmp99FlatPhysicalFibreDFTLinearEquiv
      (∑ input : CMP99SourceFlatQprimeFixedCoarseFibre d M N' ell,
        cmp99SourceFlatFullComplexPrecisionAction mass a (term input))
      output = 0
  rw [map_sum]
  rw [Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro input _
  exact
    cmp99FlatPhysicalFibreDFT_sourceFlatFullComplexPrecision_fourierMode_eq_zero_of_coarseAlias_ne
      ell mass a input _ output houtput

/-- On the selected reciprocal fibre, the literal precision applied to the
stabilized field has the DFT of the actual weighted-adjoint coarse mode. -/
theorem cmp99FlatPhysicalFibreDFT_sourceFlatFullComplexPrecision_stabilizedParticularSolution_fixedCoarseFibre
    (ell : FinBox d N') (mass a : ℝ) (v : SUNLieComplexCoord Nc)
    (hfine : ∀ k : CMP99SourceFlatQprimeFixedCoarseFibre d M N' ell,
      k ≠ cmp99SourceFlatQprimePhysicalCentralAliasIndex
          (d := d) (M := M) (N' := N') ell →
        cmp99SourceFlatQprimePhysicalFineSymbol mass k.1 ≠ 0)
    (hstabilized :
      cmp89Eq249CentralStabilizedAliasDenominator d M 1 mass a
        (cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum ell) ≠ 0)
    (output : CMP99SourceFlatQprimeFixedCoarseFibre d M N' ell) :
    cmp99FlatPhysicalFibreDFT
        (cmp99SourceFlatFullComplexPrecisionAction mass a
          (cmp99SourceFlatFullComplexPrecisionStabilizedParticularSolution
            ell mass a v)) output.1 =
      cmp99FlatPhysicalFibreDFT
        (cmp99SourceFlatFullComplexWeightedAdjointCoarseMode ell v)
        output.1 := by
  rw [cmp99SourceFlatFullComplexPrecisionStabilizedParticularSolution,
    cmp99FlatPhysicalFibreDFT_sourceFlatFullComplexPrecision_fixedCoarseFibre,
    cmp99FlatPhysicalFibreDFT_sourceFlatWeightedAdjoint_fixedCoarse_eq_aliasRow]
  have hsolution := congrFun
    (cmp99SourceFlatQprimePhysicalAliasPrecisionMatrix_transpose_mulVec_stabilizedSolution
      ell mass a hfine hstabilized) output
  change
    (∑ input,
      (cmp99SourceFlatQprimePhysicalAliasPrecisionMatrix ell mass a).transpose
          output input •
        cmp99SourceFlatFullComplexPrecisionStabilizedParticularCoefficients
          ell mass a v input) = _
  simp only [cmp99SourceFlatFullComplexPrecisionStabilizedParticularCoefficients]
  calc
    _ = ∑ input,
        ((((M * N' : ℕ) : ℂ) ^ d *
          ((cmp99SourceFlatQprimePhysicalAliasPrecisionMatrix ell mass a).transpose
            output input *
            cmp99SourceFlatQprimePhysicalStabilizedAliasTransposeSolution
              (d := d) (M := M) (N' := N') ell mass a input)) • v) := by
        apply Finset.sum_congr rfl
        intro input _
        module
    _ = (((M * N' : ℕ) : ℂ) ^ d *
          (∑ input,
            (cmp99SourceFlatQprimePhysicalAliasPrecisionMatrix ell mass a).transpose
              output input *
              cmp99SourceFlatQprimePhysicalStabilizedAliasTransposeSolution
                (d := d) (M := M) (N' := N') ell mass a input)) • v := by
        rw [Finset.mul_sum, Finset.sum_smul]
    _ = (((M * N' : ℕ) : ℂ) ^ d *
          cmp89Eq245EntireAverageAmplitude d M
            (-cmp99SourceFlatQprimeAmplitudeMomentum output.1)) • v := by
        rw [show
          (∑ input,
              (cmp99SourceFlatQprimePhysicalAliasPrecisionMatrix ell mass a).transpose
                output input *
                cmp99SourceFlatQprimePhysicalStabilizedAliasTransposeSolution
                  (d := d) (M := M) (N' := N') ell mass a input) =
              cmp89Eq245EntireAverageAmplitude d M
                (-cmp99SourceFlatQprimeAmplitudeMomentum output.1) by
            simpa only [Matrix.mulVec, dotProduct] using hsolution]
    _ = _ := by
      rw [cmp99SourceFlatQprimeNegAmplitude_eq_entireAliasRow]

/-- Literal full-box equation for the internally constructed stabilized
physical field.  This is the exact one-mode realization of `G Q'^*`. -/
theorem cmp99SourceFlatFullComplexPrecisionAction_stabilizedParticularSolution
    (ell : FinBox d N') (mass a : ℝ) (v : SUNLieComplexCoord Nc)
    (hfine : ∀ k : CMP99SourceFlatQprimeFixedCoarseFibre d M N' ell,
      k ≠ cmp99SourceFlatQprimePhysicalCentralAliasIndex
          (d := d) (M := M) (N' := N') ell →
        cmp99SourceFlatQprimePhysicalFineSymbol mass k.1 ≠ 0)
    (hstabilized :
      cmp89Eq249CentralStabilizedAliasDenominator d M 1 mass a
        (cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum ell) ≠ 0) :
    cmp99SourceFlatFullComplexPrecisionAction mass a
        (cmp99SourceFlatFullComplexPrecisionStabilizedParticularSolution
          ell mass a v) =
      cmp99SourceFlatFullComplexWeightedAdjointCoarseMode
        (d := d) (M := M) (N' := N') (Nc := Nc) ell v := by
  apply (cmp99FlatPhysicalFibreDFTLinearEquiv
    (d := d) (N := M * N') (Nc := Nc)).injective
  funext k
  change cmp99FlatPhysicalFibreDFT
      (cmp99SourceFlatFullComplexPrecisionAction mass a
        (cmp99SourceFlatFullComplexPrecisionStabilizedParticularSolution
          ell mass a v)) k =
    cmp99FlatPhysicalFibreDFT
      (cmp99SourceFlatFullComplexWeightedAdjointCoarseMode
        (d := d) (M := M) (N' := N') (Nc := Nc) ell v) k
  by_cases hk : cmp99SourceFlatQprimeCoarseAlias k = ell
  · let output : CMP99SourceFlatQprimeFixedCoarseFibre d M N' ell := ⟨k, hk⟩
    exact
      cmp99FlatPhysicalFibreDFT_sourceFlatFullComplexPrecision_stabilizedParticularSolution_fixedCoarseFibre
        ell mass a v hfine hstabilized output
  · rw [cmp99FlatPhysicalFibreDFT_sourceFlatFullComplexPrecision_stabilizedParticularSolution_eq_zero_of_coarseAlias_ne
      ell mass a v k hk]
    rw [cmp99FlatPhysicalFibreDFT_sourceFlatFullComplexWeightedAdjointCoarseMode,
      if_neg hk]

end

end YangMills.RG
