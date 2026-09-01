/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99FlatPhysicalFibrePointSourceDFT
import YangMills.RG.BalabanCMP99SourceFlatFullComplexPrecisionFibreAction
import YangMills.RG.BalabanCMP99SourceFlatFullComplexPrecisionParticularSolution
import YangMills.RG.BalabanCMP99SourceFlatQprimePhysicalStabilizedAliasTransposeFullSolution

/-!
# PRE-VALIDATION: full periodic Eq. (2.46) solution on a physical point source

Each coarse reciprocal fibre consumes the exact point-source DFT through the
arbitrary-source transposed Eq. (2.46) solution. The fibre fields are then
summed and the literal full-box precision equation is proved by DFT
injectivity. This is the finite full-`G` lane; it does not insert `Q'^*`, use
the particular Eq. (2.48) solution, or assume an inverse equality.

Source is present, its `.olean` has not yet been materialized, and the result
has not yet been verified by the compiler. It remains outside the project
import graph until its own compiler and axiom gates pass.
-/

namespace YangMills.RG

open YangMills Matrix

noncomputable section

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

/-- Exact fixed-fibre frequency coefficients for the periodic point-source
solution. The source character remains visible inside the transposed solve. -/
def cmp99SourceFlatFullComplexPrecisionPointSourceFibreCoefficients
    (ell : FinBox d N') (mass a : ℝ)
    (y : FinBox d (M * N')) (v : SUNLieComplexCoord Nc) :
    CMP99SourceFlatQprimeFixedCoarseFibre d M N' ell →
      SUNLieComplexCoord Nc :=
  cmp99SourceFlatQprimePhysicalStabilizedAliasTransposeFullVectorSolution
    ell mass a (fun k => (cmp99FlatFourierMode k.1 y)⁻¹ • v)

/-- Inverse-DFT synthesis of the point-source solution on one coarse
reciprocal fibre. -/
def cmp99SourceFlatFullComplexPrecisionPointSourceFibreSolution
    (ell : FinBox d N') (mass a : ℝ)
    (y : FinBox d (M * N')) (v : SUNLieComplexCoord Nc) :
    FinBox d (M * N') → SUNLieComplexCoord Nc :=
  cmp99SourceFlatFixedCoarseFibreFourierSynthesis ell
    (cmp99SourceFlatFullComplexPrecisionPointSourceFibreCoefficients
      ell mass a y v)

/-- A precision-applied fixed-fibre synthesis has zero DFT outside its
literal coarse reciprocal fibre. This support statement is independent of
the chosen coefficients. -/
theorem cmp99FlatPhysicalFibreDFT_sourceFlatFullComplexPrecision_fixedCoarseFibreSolution_eq_zero_of_coarseAlias_ne
    (ell : FinBox d N') (mass a : ℝ)
    (coeff : CMP99SourceFlatQprimeFixedCoarseFibre d M N' ell →
      SUNLieComplexCoord Nc)
    (output : FinBox d (M * N'))
    (houtput : cmp99SourceFlatQprimeCoarseAlias output ≠ ell) :
    cmp99FlatPhysicalFibreDFT
        (cmp99SourceFlatFullComplexPrecisionAction mass a
          (cmp99SourceFlatFixedCoarseFibreFourierSynthesis ell coeff))
        output = 0 := by
  rw [cmp99SourceFlatFixedCoarseFibreFourierSynthesis_eq_sum]
  let term : CMP99SourceFlatQprimeFixedCoarseFibre d M N' ell →
      FinBox d (M * N') → SUNLieComplexCoord Nc :=
    fun input => cmp99FlatComplexFibreFourierMode input.1
      (((((M * N' : ℕ) : ℂ) ^ d)⁻¹) • coeff input)
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
        (((((M * N' : ℕ) : ℂ) ^ d)⁻¹) • coeff input) x) =
      ∑ input, term input := by
    funext x
    rw [Finset.sum_apply]
  rw [hterm, hprecisionSum]
  change cmp99FlatPhysicalFibreDFTLinearEquiv
      (∑ input : CMP99SourceFlatQprimeFixedCoarseFibre d M N' ell,
        cmp99SourceFlatFullComplexPrecisionAction mass a (term input))
      output = 0
  rw [map_sum, Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro input _
  exact
    cmp99FlatPhysicalFibreDFT_sourceFlatFullComplexPrecision_fourierMode_eq_zero_of_coarseAlias_ne
      ell mass a input _ output houtput

/-- On its selected reciprocal fibre, the literal precision applied to the
internally synthesized solution has exactly the DFT of the physical point
source. -/
theorem cmp99FlatPhysicalFibreDFT_sourceFlatFullComplexPrecision_pointSourceFibreSolution
    (ell : FinBox d N') (mass a : ℝ)
    (y : FinBox d (M * N')) (v : SUNLieComplexCoord Nc)
    (hfine : ∀ k : CMP99SourceFlatQprimeFixedCoarseFibre d M N' ell,
      k ≠ cmp99SourceFlatQprimePhysicalCentralAliasIndex
          (d := d) (M := M) (N' := N') ell →
        cmp99SourceFlatQprimePhysicalFineSymbol mass k.1 ≠ 0)
    (hstabilized :
      cmp89Eq249CentralStabilizedAliasDenominator d M 1 mass a
        (cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum ell) ≠ 0)
    (hpair :
      cmp89Eq249CentralEntireAveragePair d M 1
        (cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum ell) ≠ 0)
    (output : CMP99SourceFlatQprimeFixedCoarseFibre d M N' ell) :
    cmp99FlatPhysicalFibreDFT
        (cmp99SourceFlatFullComplexPrecisionAction mass a
          (cmp99SourceFlatFullComplexPrecisionPointSourceFibreSolution
            ell mass a y v)) output.1 =
      cmp99FlatPhysicalFibreDFT
        (cmp99FlatComplexFibrePointSource y v) output.1 := by
  rw [cmp99SourceFlatFullComplexPrecisionPointSourceFibreSolution]
  rw [cmp99FlatPhysicalFibreDFT_sourceFlatFullComplexPrecision_fixedCoarseFibre]
  unfold cmp99SourceFlatFullComplexPrecisionPointSourceFibreCoefficients
  rw [cmp99SourceFlatQprimePhysicalAliasPrecisionMatrix_transpose_sum_smul_fullVectorSolution
    ell mass a (fun k => (cmp99FlatFourierMode k.1 y)⁻¹ • v)
    hfine hstabilized hpair output]
  rw [cmp99FlatPhysicalFibreDFT_pointSource]

/-- Sum of the internally constructed fibre solutions over every coarse
reciprocal momentum. -/
def cmp99SourceFlatFullComplexPrecisionPointSourceSolution
    (mass a : ℝ) (y : FinBox d (M * N')) (v : SUNLieComplexCoord Nc) :
    FinBox d (M * N') → SUNLieComplexCoord Nc :=
  ∑ ell : FinBox d N',
    cmp99SourceFlatFullComplexPrecisionPointSourceFibreSolution
      ell mass a y v

/-- Literal full-box precision equation for the internally constructed
periodic point-source solution. The conclusion is the finite full `G` column
before inverse uniqueness; no periodization or regional compression occurs. -/
theorem cmp99SourceFlatFullComplexPrecisionAction_pointSourceSolution
    (mass a : ℝ) (y : FinBox d (M * N')) (v : SUNLieComplexCoord Nc)
    (hfine : ∀ ell : FinBox d N',
      ∀ k : CMP99SourceFlatQprimeFixedCoarseFibre d M N' ell,
        k ≠ cmp99SourceFlatQprimePhysicalCentralAliasIndex
            (d := d) (M := M) (N' := N') ell →
          cmp99SourceFlatQprimePhysicalFineSymbol mass k.1 ≠ 0)
    (hstabilized : ∀ ell : FinBox d N',
      cmp89Eq249CentralStabilizedAliasDenominator d M 1 mass a
        (cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum ell) ≠ 0)
    (hpair : ∀ ell : FinBox d N',
      cmp89Eq249CentralEntireAveragePair d M 1
        (cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum ell) ≠ 0) :
    cmp99SourceFlatFullComplexPrecisionAction mass a
        (cmp99SourceFlatFullComplexPrecisionPointSourceSolution mass a y v) =
      cmp99FlatComplexFibrePointSource y v := by
  apply (cmp99FlatPhysicalFibreDFTLinearEquiv
    (d := d) (N := M * N') (Nc := Nc)).injective
  funext output
  have hprecisionSum :
      cmp99SourceFlatFullComplexPrecisionAction mass a
          (∑ ell : FinBox d N',
            cmp99SourceFlatFullComplexPrecisionPointSourceFibreSolution
              ell mass a y v) =
        ∑ ell : FinBox d N',
          cmp99SourceFlatFullComplexPrecisionAction mass a
            (cmp99SourceFlatFullComplexPrecisionPointSourceFibreSolution
              ell mass a y v) := by
    simpa only using
      cmp99SourceFlatFullComplexPrecisionAction_finset_sum
        (d := d) (M := M) (N' := N') (Nc := Nc)
        mass a Finset.univ
        (fun ell =>
          cmp99SourceFlatFullComplexPrecisionPointSourceFibreSolution
            ell mass a y v)
  change cmp99FlatPhysicalFibreDFT
      (cmp99SourceFlatFullComplexPrecisionAction mass a
        (cmp99SourceFlatFullComplexPrecisionPointSourceSolution mass a y v))
      output =
    cmp99FlatPhysicalFibreDFT (cmp99FlatComplexFibrePointSource y v) output
  rw [cmp99SourceFlatFullComplexPrecisionPointSourceSolution, hprecisionSum]
  change cmp99FlatPhysicalFibreDFTLinearEquiv
      (∑ ell : FinBox d N',
        cmp99SourceFlatFullComplexPrecisionAction mass a
          (cmp99SourceFlatFullComplexPrecisionPointSourceFibreSolution
            ell mass a y v)) output = _
  rw [map_sum, Finset.sum_apply]
  rw [Finset.sum_eq_single (cmp99SourceFlatQprimeCoarseAlias output)]
  · let selected : CMP99SourceFlatQprimeFixedCoarseFibre d M N'
        (cmp99SourceFlatQprimeCoarseAlias output) := ⟨output, rfl⟩
    exact
      cmp99FlatPhysicalFibreDFT_sourceFlatFullComplexPrecision_pointSourceFibreSolution
        (cmp99SourceFlatQprimeCoarseAlias output) mass a y v
        (hfine _) (hstabilized _) (hpair _) selected
  · intro ell _ hell
    exact
      cmp99FlatPhysicalFibreDFT_sourceFlatFullComplexPrecision_fixedCoarseFibreSolution_eq_zero_of_coarseAlias_ne
        ell mass a
        (cmp99SourceFlatFullComplexPrecisionPointSourceFibreCoefficients
          ell mass a y v)
        output (Ne.symm hell)
  · intro hmem
    exact (hmem (Finset.mem_univ _)).elim

end

end YangMills.RG
