/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceSeparatedSourceFlowFlatPhysicalStep7bPrecisionDictionary
import YangMills.RG.BalabanCMP99SourceFlatQprimePhysicalFineSymbolMassZeroNoncentral
import YangMills.RG.BalabanCMP99SourceFlatQprimePhysicalStabilizedDenominatorNonvanishing

/-!
# Source-flow separated flat physical Green identification

The internally constructed source-flow Green is transported to the exact
Step-7b carrier and identified by inverse uniqueness with the literal
full-complex inverse.  Positivity of the literal source coefficient is
derived from `ha : 0 < a`; no generated Poincare coefficient is used.
-/

namespace YangMills.RG

open YangMills

noncomputable section

variable {L K Q Nc : ℕ}
variable [NeZero L] [NeZero K] [NeZero Q] [NeZero Nc]

/-- The internally constructed source-flow Green in exact Step-7b full-box
coordinates. -/
noncomputable def cmp99SourceSeparatedSourceFlowFlatPhysicalStep7bGreenCLM
    (hL : 2 ≤ L) (depth : ℕ) {a : ℝ} (ha : 0 < a) :
    (FinBox 4 (L ^ (depth + 1) * (2 * (K * Q))) →
      SUNLieComplexCoord Nc) →L[ℂ]
    (FinBox 4 (L ^ (depth + 1) * (2 * (K * Q))) →
      SUNLieComplexCoord Nc) :=
  let U :=
    cmp99SourceSeparatedGeneratedPhysicalStep7bFieldEquiv L K Q Nc depth
  U.toContinuousLinearMap.comp
    ((cmp99SourceSeparatedSourceFlowFlatAmbientGreenComplex
      (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth ha).comp
        U.symm.toContinuousLinearMap)

/-- The source-flow Step-7b Green is a literal left inverse of the literal
source-flow full-box precision. -/
theorem cmp99SourceSeparatedSourceFlowFlatPhysicalStep7bGreenCLM_comp_precision
    (hL : 2 ≤ L) (depth : ℕ) {a : ℝ} (ha : 0 < a) :
    (cmp99SourceSeparatedSourceFlowFlatPhysicalStep7bGreenCLM
      (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth ha).comp
        (cmp99SourceFlatFullComplexPrecisionCLM
          (d := 4) (M := L ^ (depth + 1)) (N' := 2 * (K * Q))
          (Nc := Nc) 0 (cmp99SourceFlowFlatFullComplexA a L depth)) =
      ContinuousLinearMap.id ℂ
        (FinBox 4 (L ^ (depth + 1) * (2 * (K * Q))) →
          SUNLieComplexCoord Nc) := by
  let U :=
    cmp99SourceSeparatedGeneratedPhysicalStep7bFieldEquiv L K Q Nc depth
  let P := cmp99SourceFlatFullComplexPrecisionCLM
    (d := 4) (M := L ^ (depth + 1)) (N' := 2 * (K * Q))
    (Nc := Nc) 0 (cmp99SourceFlowFlatFullComplexA a L depth)
  let A := cmp99SourceSeparatedSourceFlowFlatAmbientPrecisionComplex
    (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth a
  let G := cmp99SourceSeparatedSourceFlowFlatAmbientGreenComplex
    (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth ha
  have hdict : A =
      cmp99SourceSeparatedSourceFlowFlatPhysicalStep7bAmbientPrecisionCLM
        (L := L) (K := K) (Q := Q) (Nc := Nc) depth a :=
    cmp99SourceSeparatedSourceFlowFlatAmbientPrecisionComplex_eq_step7b
      (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth a
  have hGA : G.comp A = ContinuousLinearMap.id ℂ _ :=
    cmp99SourceSeparatedSourceFlowFlatAmbientGreenComplex_comp_precision
      (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth ha
  apply ContinuousLinearMap.ext
  intro z
  have hdictz : A (U.symm z) = U.symm (P z) := by
    have h := congrArg (fun T => T (U.symm z)) hdict
    simpa [
      cmp99SourceSeparatedSourceFlowFlatPhysicalStep7bAmbientPrecisionCLM,
      U, P] using h
  have hGAz : G (A (U.symm z)) = U.symm z := by
    have h := congrArg (fun T => T (U.symm z)) hGA
    simpa [G, A] using h
  change U (G (U.symm (P z))) = z
  rw [← hdictz, hGAz]
  exact U.apply_symm_apply z

/-- The literal positive source-flow coefficient makes every central
stabilized denominator nonzero. -/
theorem cmp99SourceSeparatedSourceFlowFlatPhysicalStabilizedAliasDenominator_ne_zero
    (L K Q depth : ℕ) [NeZero L] [NeZero K] [NeZero Q]
    {a : ℝ} (ha : 0 < a) :
    ∀ ell : FinBox 4 (2 * (K * Q)),
      cmp89Eq249CentralStabilizedAliasDenominator
          4 (L ^ (depth + 1)) 1 0
          (cmp99SourceFlowFlatFullComplexA a L depth)
          (cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum ell) ≠ 0 := by
  have hA : 0 < cmp99SourceFlowFlatFullComplexA a L depth := by
    simpa [cmp99SourceFlowFlatFullComplexA] using
      (cmp99SourceMassParameter_pos ha
        (by exact_mod_cast (NeZero.pos L)) depth)
  intro ell
  exact
    cmp89Eq249CentralStabilizedAliasDenominator_massZero_ne_zero_physical
      (d := 4) (M := L ^ (depth + 1)) (N' := 2 * (K * Q))
      (a := cmp99SourceFlowFlatFullComplexA a L depth) hA ell

/-- Source-flow physical endpoint: the literal stabilized Step-7b field is
the internally constructed Green applied to the literal coefficient-one
`Q'^*`. -/
theorem cmp99SourceSeparatedSourceFlowFlatPhysicalStabilizedFieldCLM_eq_green_comp
    (hL : 2 ≤ L) (depth : ℕ) {a : ℝ} (ha : 0 < a) :
    cmp99SourceFlatFullComplexPrecisionStabilizedQprimeStarFieldCLM
        (d := 4) (M := L ^ (depth + 1)) (N' := 2 * (K * Q))
        (Nc := Nc) 0 (cmp99SourceFlowFlatFullComplexA a L depth) =
      (cmp99SourceSeparatedSourceFlowFlatPhysicalStep7bGreenCLM
        (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth ha).comp
        (cmp99SourceFlatFullComplexWeightedAdjointCLM
          (d := 4) (M := L ^ (depth + 1)) (N' := 2 * (K * Q))
          (Nc := Nc)) := by
  apply cmp99SourceFlatFullComplexPrecisionStabilizedFieldCLM_eq_inverse_comp
    (d := 4) (M := L ^ (depth + 1)) (N' := 2 * (K * Q))
    (Nc := Nc)
  · exact
      cmp99SourceSeparatedSourceFlowFlatPhysicalStep7bGreenCLM_comp_precision
        (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth ha
  · intro ell k hk
    exact cmp99SourceFlatQprimePhysicalFineSymbol_massZero_ne_zero_noncentral
      ell k hk
  · exact
      cmp99SourceSeparatedSourceFlowFlatPhysicalStabilizedAliasDenominator_ne_zero
        L K Q depth ha

end

end YangMills.RG
