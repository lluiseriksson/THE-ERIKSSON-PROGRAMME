/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceSeparatedGeneratedFlatPhysicalStep7bPrecisionDictionary
import YangMills.RG.BalabanCMP99SourceFlatQprimePhysicalFineSymbolMassZeroNoncentral
import YangMills.RG.BalabanCMP99SourceFlatQprimePhysicalStabilizedDenominatorNonvanishing

/-!
# Source-separated generated flat physical Green identification

This is Step 8b.24/S3.  The source-separated ambient Green is transported
through the exact Step-7b carrier equivalence.  Its inverse law and the
physical scalar nonvanishing families are constructed internally, so inverse
uniqueness identifies the literal stabilized field with `G Q'^*`.

The generic noncentral fine-symbol lemma has been extracted into a neutral
source module.  No diagonal endpoint, carrier cast or `K=L` theorem is
consumed.
-/

namespace YangMills.RG

open YangMills

noncomputable section

variable {L K Q Nc : ℕ}
variable [NeZero L] [NeZero K] [NeZero Q] [NeZero Nc]

/-- The internally generated separated ambient Green in the exact Step-7b
full-box coordinates. -/
noncomputable def cmp99SourceSeparatedGeneratedFlatPhysicalStep7bGreenCLM
    (hL : 2 ≤ L) (depth : ℕ) :
    (FinBox 4 (L ^ (depth + 1) * (2 * (K * Q))) →
      SUNLieComplexCoord Nc) →L[ℂ]
    (FinBox 4 (L ^ (depth + 1) * (2 * (K * Q))) →
      SUNLieComplexCoord Nc) :=
  let U :=
    cmp99SourceSeparatedGeneratedPhysicalStep7bFieldEquiv L K Q Nc depth
  U.toContinuousLinearMap.comp
    ((cmp99SourceSeparatedGeneratedFlatPhysicalAmbientGreenComplex
      (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth).comp
        U.symm.toContinuousLinearMap)

/-- The separated generated Step-7b Green is a literal left inverse of the
literal full-box precision. -/
theorem cmp99SourceSeparatedGeneratedFlatPhysicalStep7bGreenCLM_comp_precision
    (hL : 2 ≤ L) (depth : ℕ) :
    (cmp99SourceSeparatedGeneratedFlatPhysicalStep7bGreenCLM
      (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth).comp
        (cmp99SourceFlatFullComplexPrecisionCLM
          (d := 4) (M := L ^ (depth + 1)) (N' := 2 * (K * Q))
          (Nc := Nc) 0
          (cmp99SourceGeneratedFullComplexA 4 L (depth + 1)
            (cmp99SourceGeneratedFullComplexSpacing L (depth + 1)) 0)) =
      ContinuousLinearMap.id ℂ
        (FinBox 4 (L ^ (depth + 1) * (2 * (K * Q))) →
          SUNLieComplexCoord Nc) := by
  let U :=
    cmp99SourceSeparatedGeneratedPhysicalStep7bFieldEquiv L K Q Nc depth
  let P := cmp99SourceFlatFullComplexPrecisionCLM
    (d := 4) (M := L ^ (depth + 1)) (N' := 2 * (K * Q))
    (Nc := Nc) 0
    (cmp99SourceGeneratedFullComplexA 4 L (depth + 1)
      (cmp99SourceGeneratedFullComplexSpacing L (depth + 1)) 0)
  let A :=
    cmp99SourceSeparatedGeneratedFlatPhysicalAmbientPrecisionComplex
      (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth
  let G := cmp99SourceSeparatedGeneratedFlatPhysicalAmbientGreenComplex
    (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth
  have hdict : A =
      cmp99SourceSeparatedGeneratedFlatPhysicalStep7bAmbientPrecisionCLM
        (L := L) (K := K) (Q := Q) (Nc := Nc) depth :=
    cmp99SourceSeparatedGeneratedFlatPhysicalAmbientPrecisionComplex_eq_step7b
      (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth
  have hGA : G.comp A = ContinuousLinearMap.id ℂ _ :=
    cmp99SourceSeparatedGeneratedFlatPhysicalAmbientGreenComplex_comp_precision
      (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth
  apply ContinuousLinearMap.ext
  intro z
  have hdictz : A (U.symm z) = U.symm (P z) := by
    have h := congrArg (fun T => T (U.symm z)) hdict
    simpa [
      cmp99SourceSeparatedGeneratedFlatPhysicalStep7bAmbientPrecisionCLM,
      U, P] using h
  have hGAz : G (A (U.symm z)) = U.symm z := by
    have h := congrArg (fun T => T (U.symm z)) hGA
    simpa [G, A] using h
  change U (G (U.symm (P z))) = z
  rw [← hdictz, hGAz]
  exact U.apply_symm_apply z

/-- The physical central denominator remains nonzero at the independent
source scales.  Positivity of the generated coefficient is internal. -/
theorem
    cmp99SourceSeparatedGeneratedFlatPhysicalStabilizedAliasDenominator_ne_zero
    (L K Q depth : ℕ) [NeZero L] [NeZero K] [NeZero Q] :
    ∀ ell : FinBox 4 (2 * (K * Q)),
      cmp89Eq249CentralStabilizedAliasDenominator
          4 (L ^ (depth + 1)) 1 0
          (cmp99SourceGeneratedFullComplexA 4 L (depth + 1)
            (cmp99SourceGeneratedFullComplexSpacing L (depth + 1)) 0)
          (cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum ell) ≠ 0 := by
  intro ell
  exact
    cmp89Eq249CentralStabilizedAliasDenominator_massZero_ne_zero_physical
      (d := 4) (M := L ^ (depth + 1)) (N' := 2 * (K * Q))
      (a := cmp99SourceGeneratedFullComplexA 4 L (depth + 1)
        (cmp99SourceGeneratedFullComplexSpacing L (depth + 1)) 0)
      (cmp99SourceGeneratedFullComplexA_pos_physical L depth) ell

/-- Source-separated physical endpoint: the literal stabilized Step-7b field
is the internally generated Green applied to the literal coefficient-one
`Q'^*`. -/
theorem cmp99SourceSeparatedGeneratedFlatPhysicalStabilizedFieldCLM_eq_green_comp
    (hL : 2 ≤ L) (depth : ℕ) :
    cmp99SourceFlatFullComplexPrecisionStabilizedQprimeStarFieldCLM
        (d := 4) (M := L ^ (depth + 1)) (N' := 2 * (K * Q))
        (Nc := Nc) 0
        (cmp99SourceGeneratedFullComplexA 4 L (depth + 1)
          (cmp99SourceGeneratedFullComplexSpacing L (depth + 1)) 0) =
      (cmp99SourceSeparatedGeneratedFlatPhysicalStep7bGreenCLM
        (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth).comp
        (cmp99SourceFlatFullComplexWeightedAdjointCLM
          (d := 4) (M := L ^ (depth + 1)) (N' := 2 * (K * Q))
          (Nc := Nc)) := by
  apply cmp99SourceFlatFullComplexPrecisionStabilizedFieldCLM_eq_inverse_comp
    (d := 4) (M := L ^ (depth + 1)) (N' := 2 * (K * Q))
    (Nc := Nc)
  · exact
      cmp99SourceSeparatedGeneratedFlatPhysicalStep7bGreenCLM_comp_precision
        (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth
  · intro ell k hk
    exact cmp99SourceFlatQprimePhysicalFineSymbol_massZero_ne_zero_noncentral
      ell k hk
  · exact
      cmp99SourceSeparatedGeneratedFlatPhysicalStabilizedAliasDenominator_ne_zero
        L K Q depth

end

end YangMills.RG
