/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceFlatFullComplexPrecisionInverseUniqueness
import YangMills.RG.BalabanCMP99SourceFlatFullComplexPrecisionPointSourceSolution

/-!
# PRE-VALIDATION: point-source solution identified by inverse uniqueness

The internally constructed Eq. (2.46) point-source field is identified with
the action of any left inverse of the same literal full-box precision. The
inverse law is the only Green input; the desired point-source equality is
derived from the already proved precision equation.

Source is present, its `.olean` has not yet been materialized, and the result
has not yet been verified by the compiler.
-/

namespace YangMills.RG

open YangMills Matrix

noncomputable section

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

/-- Inverse uniqueness for the full-periodic physical point source. -/
theorem cmp99SourceFlatFullComplexPrecisionPointSourceSolution_eq_inverse_apply
    (mass a : ℝ)
    (G : (FinBox d (M * N') → SUNLieComplexCoord Nc) →L[ℂ]
      (FinBox d (M * N') → SUNLieComplexCoord Nc))
    (hGK : G.comp
        (cmp99SourceFlatFullComplexPrecisionCLM
          (d := d) (M := M) (N' := N') (Nc := Nc) mass a) =
      ContinuousLinearMap.id ℂ _)
    (y : FinBox d (M * N')) (v : SUNLieComplexCoord Nc)
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
    cmp99SourceFlatFullComplexPrecisionPointSourceSolution mass a y v =
      G (cmp99FlatComplexFibrePointSource y v) := by
  calc
    cmp99SourceFlatFullComplexPrecisionPointSourceSolution mass a y v =
        (ContinuousLinearMap.id ℂ _)
          (cmp99SourceFlatFullComplexPrecisionPointSourceSolution mass a y v) := by
            simp
    _ = (G.comp
          (cmp99SourceFlatFullComplexPrecisionCLM
            (d := d) (M := M) (N' := N') (Nc := Nc) mass a))
          (cmp99SourceFlatFullComplexPrecisionPointSourceSolution mass a y v) := by
            rw [hGK]
    _ = G (cmp99SourceFlatFullComplexPrecisionAction mass a
          (cmp99SourceFlatFullComplexPrecisionPointSourceSolution mass a y v)) := rfl
    _ = G (cmp99FlatComplexFibrePointSource y v) := by
      rw [cmp99SourceFlatFullComplexPrecisionAction_pointSourceSolution
        mass a y v hfine hstabilized hpair]

end

end YangMills.RG
