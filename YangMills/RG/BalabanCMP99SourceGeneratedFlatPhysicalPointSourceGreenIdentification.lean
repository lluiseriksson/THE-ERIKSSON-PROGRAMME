/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceGeneratedFlatPhysicalGreenIdentification
import YangMills.RG.BalabanCMP99SourceFlatFullComplexPrecisionPointSourceInverseUniqueness
import YangMills.RG.BalabanCMP99SourceFlatQprimePhysicalCentralAveragePairNonvanishing

/-!
# PRE-VALIDATION: generated flat physical Green on a literal point source

The full-periodic Eq. (2.46) point-source solution is identified with the
internally generated Step-7b Green. The inverse law, noncentral fine-symbol
family, stabilized denominator, and central averaging-pair nonvanishing are
all constructed in the proof.

Source is present, its `.olean` has not yet been materialized, and the result
has not yet been verified by the compiler.
-/

namespace YangMills.RG

open YangMills

noncomputable section

variable {M Q Nc : ℕ}
variable [NeZero M] [NeZero Q] [NeZero Nc]

/-- Generated physical endpoint for the literal full-box point source. -/
theorem cmp99SourceGeneratedFlatPhysicalPointSourceSolution_eq_green_apply
    (hM : 2 ≤ M) (depth : ℕ)
    (y : FinBox 4 (M ^ (depth + 1) * (2 * (M * Q))))
    (v : SUNLieComplexCoord Nc) :
    cmp99SourceFlatFullComplexPrecisionPointSourceSolution
        (d := 4) (M := M ^ (depth + 1)) (N' := 2 * (M * Q))
        (Nc := Nc) 0
        (cmp99SourceGeneratedFullComplexA 4 M (depth + 1)
          (cmp99SourceGeneratedFullComplexSpacing M (depth + 1)) 0)
        y v =
      cmp99SourceGeneratedFlatPhysicalStep7bGreenCLM
        (M := M) (Q := Q) (Nc := Nc) hM depth
        (cmp99FlatComplexFibrePointSource y v) := by
  apply
    cmp99SourceFlatFullComplexPrecisionPointSourceSolution_eq_inverse_apply
      (d := 4) (M := M ^ (depth + 1)) (N' := 2 * (M * Q))
      (Nc := Nc)
  · exact cmp99SourceGeneratedFlatPhysicalStep7bGreenCLM_comp_precision
      (M := M) (Q := Q) (Nc := Nc) hM depth
  · intro ell k hk
    exact cmp99SourceFlatQprimePhysicalFineSymbol_massZero_ne_zero_noncentral
      ell k hk
  · exact cmp99SourceGeneratedFlatPhysicalStabilizedAliasDenominator_ne_zero
      M Q depth
  · intro ell
    exact cmp89Eq249CentralEntireAveragePair_physicalCoarse_ne_zero ell

end

end YangMills.RG
