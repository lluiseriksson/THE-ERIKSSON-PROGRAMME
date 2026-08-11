/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceFlatFullComplexPrecisionFibreAction
import YangMills.RG.BalabanCMP99SourceFlatQprimePhysicalAliasTransposeSolution

/-!
# Flat physical particular solution on one reciprocal fibre

PRE-VALIDATION: source is present, its `.olean` has not yet been materialized,
and the result has not yet been verified by the Lean compiler.

The sealed transpose alias solution is multiplied by the literal fine volume
and reconstructed through the sealed physical inverse DFT.  The volume is not
absorbed into a free normalization: it cancels the inverse-transform factor
and makes the literal full-box precision send the resulting field to the
actual coefficient-one weighted-adjoint coarse Fourier mode.

The proof treats the complement of the chosen reciprocal fibre explicitly.
On the fibre it consumes the internally constructed transposed matrix
solution; off the fibre both the precision output and the weighted-adjoint
source have zero forward DFT.  DFT injectivity then gives the physical field
equation, without a synthetic Fourier operator or a supplied solution field.

Honest scope: the printed quotients are used only under their named
nonvanishing assumptions.  The central removable zero, a global inverse CLM,
the stabilized-kernel dictionary, interacting/regional transport and the
uniform physical `B0` estimate remain open.
-/

namespace YangMills.RG

open YangMills Matrix

noncomputable section

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

/-- Fixed-fibre Fourier coefficients of the physical particular solution.
The fine volume is literal and is not hidden in the alias solution. -/
def cmp99SourceFlatFullComplexPrecisionParticularCoefficients
    (ell : FinBox d N') (mass a : ℝ) (v : SUNLieComplexCoord Nc) :
    CMP99SourceFlatQprimeFixedCoarseFibre d M N' ell →
      SUNLieComplexCoord Nc :=
  fun k =>
    (((M * N' : ℕ) : ℂ) ^ d *
      cmp99SourceFlatQprimePhysicalAliasTransposeSolution ell mass a k) • v

/-- Literal inverse-DFT reconstruction of the physical particular solution
on one coarse reciprocal fibre. -/
def cmp99SourceFlatFullComplexPrecisionParticularSolution
    (ell : FinBox d N') (mass a : ℝ) (v : SUNLieComplexCoord Nc) :
    FinBox d (M * N') → SUNLieComplexCoord Nc :=
  cmp99SourceFlatFixedCoarseFibreFourierSynthesis ell
    (cmp99SourceFlatFullComplexPrecisionParticularCoefficients ell mass a v)

/-- On the selected reciprocal fibre, the DFT of the particular solution is
the fine-volume multiple of the printed transposed alias solution. -/
omit [NeZero d] [NeZero Nc] in
theorem cmp99FlatPhysicalFibreDFT_particularSolution_fixedCoarseFibre
    (ell : FinBox d N') (mass a : ℝ) (v : SUNLieComplexCoord Nc)
    (k : CMP99SourceFlatQprimeFixedCoarseFibre d M N' ell) :
    cmp99FlatPhysicalFibreDFT
        (cmp99SourceFlatFullComplexPrecisionParticularSolution ell mass a v)
        k.1 =
      (((M * N' : ℕ) : ℂ) ^ d *
        cmp99SourceFlatQprimePhysicalAliasTransposeSolution ell mass a k) • v := by
  exact cmp99FlatPhysicalFibreDFT_fixedCoarseFibreFourierSynthesis ell
    (cmp99SourceFlatFullComplexPrecisionParticularCoefficients ell mass a v) k

/-- Outside the selected reciprocal fibre, the DFT of the particular
solution vanishes by its literal zero extension. -/
omit [NeZero d] [NeZero Nc] in
theorem cmp99FlatPhysicalFibreDFT_particularSolution_eq_zero_of_coarseAlias_ne
    (ell : FinBox d N') (mass a : ℝ) (v : SUNLieComplexCoord Nc)
    (k : FinBox d (M * N'))
    (hk : cmp99SourceFlatQprimeCoarseAlias k ≠ ell) :
    cmp99FlatPhysicalFibreDFT
        (cmp99SourceFlatFullComplexPrecisionParticularSolution ell mass a v)
        k = 0 := by
  rw [cmp99SourceFlatFullComplexPrecisionParticularSolution,
    cmp99SourceFlatFixedCoarseFibreFourierSynthesis,
    cmp99FlatPhysicalFibreDFT_InvDFT]
  simp [cmp99SourceFlatFixedCoarseFibreCoefficientExtension, hk]

/-- One input mode from the selected fibre cannot produce a precision-output
mode in a different coarse reciprocal fibre. -/
theorem cmp99FlatPhysicalFibreDFT_sourceFlatFullComplexPrecision_fourierMode_eq_zero_of_coarseAlias_ne
    (ell : FinBox d N') (mass a : ℝ)
    (input : CMP99SourceFlatQprimeFixedCoarseFibre d M N' ell)
    (w : SUNLieComplexCoord Nc) (output : FinBox d (M * N'))
    (houtput : cmp99SourceFlatQprimeCoarseAlias output ≠ ell) :
    cmp99FlatPhysicalFibreDFT
        (cmp99SourceFlatFullComplexPrecisionAction mass a
          (cmp99FlatComplexFibreFourierMode input.1 w)) output = 0 := by
  rw [cmp99SourceFlatFullComplexPrecisionAction_fourierMode]
  rw [input.property]
  change cmp99FlatPhysicalFibreDFTLinearEquiv
      (cmp99SourceFlatQprimePhysicalFineSymbol mass input.1 •
          cmp99FlatComplexFibreFourierMode input.1 w +
        (((a : ℂ) * cmp89Eq245EntireAverageAmplitude d M
          (cmp99SourceFlatQprimeAmplitudeMomentum input.1)) •
            cmp99SourceFlatFullComplexWeightedAdjointCoarseMode ell w))
        output = 0
  rw [map_add, map_smul, map_smul]
  change
    cmp99SourceFlatQprimePhysicalFineSymbol mass input.1 •
          cmp99FlatPhysicalFibreDFT
            (cmp99FlatComplexFibreFourierMode input.1 w) output +
        (((a : ℂ) * cmp89Eq245EntireAverageAmplitude d M
          (cmp99SourceFlatQprimeAmplitudeMomentum input.1)) •
            cmp99FlatPhysicalFibreDFT
              (cmp99SourceFlatFullComplexWeightedAdjointCoarseMode ell w)
              output) = 0
  have hinput : input.1 ≠ output := by
    intro h
    apply houtput
    simpa [h] using input.property
  rw [cmp99FlatPhysicalFibreDFT_fourierMode, if_neg hinput,
    cmp99FlatPhysicalFibreDFT_sourceFlatFullComplexWeightedAdjointCoarseMode,
    if_neg houtput]
  simp

/-- The precision applied to the synthesized particular solution also has
zero DFT outside the selected reciprocal fibre. -/
theorem cmp99FlatPhysicalFibreDFT_sourceFlatFullComplexPrecision_particularSolution_eq_zero_of_coarseAlias_ne
    (ell : FinBox d N') (mass a : ℝ) (v : SUNLieComplexCoord Nc)
    (output : FinBox d (M * N'))
    (houtput : cmp99SourceFlatQprimeCoarseAlias output ≠ ell) :
    cmp99FlatPhysicalFibreDFT
        (cmp99SourceFlatFullComplexPrecisionAction mass a
          (cmp99SourceFlatFullComplexPrecisionParticularSolution ell mass a v))
        output = 0 := by
  rw [cmp99SourceFlatFullComplexPrecisionParticularSolution,
    cmp99SourceFlatFixedCoarseFibreFourierSynthesis_eq_sum]
  let term : CMP99SourceFlatQprimeFixedCoarseFibre d M N' ell →
      FinBox d (M * N') → SUNLieComplexCoord Nc :=
    fun input => cmp99FlatComplexFibreFourierMode input.1
      (((((M * N' : ℕ) : ℂ) ^ d)⁻¹) •
        cmp99SourceFlatFullComplexPrecisionParticularCoefficients
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
          cmp99SourceFlatFullComplexPrecisionParticularCoefficients
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
particular solution has the same DFT as the actual weighted-adjoint coarse
Fourier mode. -/
theorem cmp99FlatPhysicalFibreDFT_sourceFlatFullComplexPrecision_particularSolution_fixedCoarseFibre
    (ell : FinBox d N') (mass a : ℝ) (v : SUNLieComplexCoord Nc)
    (hfine : ∀ k : CMP99SourceFlatQprimeFixedCoarseFibre d M N' ell,
      cmp99SourceFlatQprimePhysicalFineSymbol mass k.1 ≠ 0)
    (hreduced : cmp89Eq247ComplexReducedAliasDenominator d M 1 mass a
      (cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum ell) ≠ 0)
    (output : CMP99SourceFlatQprimeFixedCoarseFibre d M N' ell) :
    cmp99FlatPhysicalFibreDFT
        (cmp99SourceFlatFullComplexPrecisionAction mass a
          (cmp99SourceFlatFullComplexPrecisionParticularSolution ell mass a v))
        output.1 =
      cmp99FlatPhysicalFibreDFT
        (cmp99SourceFlatFullComplexWeightedAdjointCoarseMode ell v) output.1 := by
  rw [cmp99SourceFlatFullComplexPrecisionParticularSolution,
    cmp99FlatPhysicalFibreDFT_sourceFlatFullComplexPrecision_fixedCoarseFibre,
    cmp99FlatPhysicalFibreDFT_sourceFlatWeightedAdjoint_fixedCoarse_eq_aliasRow]
  have hsolution := congrFun
    (cmp99SourceFlatQprimePhysicalAliasPrecisionMatrix_transpose_mulVec_solution
      ell mass a hfine hreduced) output
  change
    (∑ input,
      (cmp99SourceFlatQprimePhysicalAliasPrecisionMatrix ell mass a).transpose
          output input •
        cmp99SourceFlatFullComplexPrecisionParticularCoefficients
          ell mass a v input) = _
  ext b
  rw [Finset.sum_apply]
  simp only [cmp99SourceFlatFullComplexPrecisionParticularCoefficients,
    PiLp.smul_apply, smul_eq_mul]
  change
    (∑ input,
      (cmp99SourceFlatQprimePhysicalAliasPrecisionMatrix ell mass a).transpose
          output input *
        ((((M * N' : ℕ) : ℂ) ^ d *
          cmp99SourceFlatQprimePhysicalAliasTransposeSolution ell mass a input) *
          v b)) = _
  calc
    _ = ∑ input,
        (((M * N' : ℕ) : ℂ) ^ d *
          ((cmp99SourceFlatQprimePhysicalAliasPrecisionMatrix ell mass a).transpose
            output input *
            cmp99SourceFlatQprimePhysicalAliasTransposeSolution ell mass a input)) *
          v b := by
        apply Finset.sum_congr rfl
        intro input _
        ring
    _ = (((M * N' : ℕ) : ℂ) ^ d *
          (∑ input,
            (cmp99SourceFlatQprimePhysicalAliasPrecisionMatrix ell mass a).transpose
              output input *
              cmp99SourceFlatQprimePhysicalAliasTransposeSolution ell mass a input)) *
          v b := by
        rw [Finset.mul_sum, Finset.sum_mul]
    _ = (((M * N' : ℕ) : ℂ) ^ d *
          cmp89Eq245EntireAverageAmplitude d M
            (-cmp99SourceFlatQprimeAmplitudeMomentum output.1)) * v b := by
        rw [show
          (∑ input,
            (cmp99SourceFlatQprimePhysicalAliasPrecisionMatrix ell mass a).transpose
              output input *
              cmp99SourceFlatQprimePhysicalAliasTransposeSolution ell mass a input) =
            cmp89Eq245EntireAverageAmplitude d M
              (-cmp99SourceFlatQprimeAmplitudeMomentum output.1) by
            simpa only [Matrix.mulVec, dotProduct] using hsolution]
    _ = _ := by
      rw [cmp99SourceFlatQprimeNegAmplitude_eq_entireAliasRow]

/-- Literal full-box physical equation for the internally constructed
particular solution.  DFT injectivity combines the on-fibre matrix solution
with the separately proved off-fibre vanishing. -/
theorem cmp99SourceFlatFullComplexPrecisionAction_particularSolution
    (ell : FinBox d N') (mass a : ℝ) (v : SUNLieComplexCoord Nc)
    (hfine : ∀ k : CMP99SourceFlatQprimeFixedCoarseFibre d M N' ell,
      cmp99SourceFlatQprimePhysicalFineSymbol mass k.1 ≠ 0)
    (hreduced : cmp89Eq247ComplexReducedAliasDenominator d M 1 mass a
      (cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum ell) ≠ 0) :
    cmp99SourceFlatFullComplexPrecisionAction mass a
        (cmp99SourceFlatFullComplexPrecisionParticularSolution ell mass a v) =
      cmp99SourceFlatFullComplexWeightedAdjointCoarseMode
        (d := d) (M := M) (N' := N') (Nc := Nc) ell v := by
  apply (cmp99FlatPhysicalFibreDFTLinearEquiv
    (d := d) (N := M * N') (Nc := Nc)).injective
  funext k
  by_cases hk : cmp99SourceFlatQprimeCoarseAlias k = ell
  · let output : CMP99SourceFlatQprimeFixedCoarseFibre d M N' ell := ⟨k, hk⟩
    exact
      cmp99FlatPhysicalFibreDFT_sourceFlatFullComplexPrecision_particularSolution_fixedCoarseFibre
        ell mass a v hfine hreduced output
  · rw [cmp99FlatPhysicalFibreDFT_sourceFlatFullComplexPrecision_particularSolution_eq_zero_of_coarseAlias_ne
      ell mass a v k hk]
    rw [cmp99FlatPhysicalFibreDFT_sourceFlatFullComplexWeightedAdjointCoarseMode,
      if_neg hk]

end

end YangMills.RG
