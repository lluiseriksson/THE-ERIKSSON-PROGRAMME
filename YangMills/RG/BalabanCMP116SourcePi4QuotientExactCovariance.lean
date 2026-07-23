/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourcePi4CorePartition
import YangMills.RG.BalabanCMP99PatchedParametrixNeumann
import YangMills.RG.BalabanCMP116PhysicalEndomorphismMatrix

/-!
# Exact covariance on the quotient-safe source `Pi^4` charts

The complex weakening series uses distinct `Pi^4` collars rather than literal
cell centres.  This file constructs the exact corrected covariance on that
same chart type.  Coincident collars are merged, their owner cores are
unioned, and the unique `Unit` label ensures that the quotient cores form the
exact partition proved upstream.
-/

namespace YangMills.RG

noncomputable section

private abbrev PhysicalEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc →L[ℝ]
    PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

/-- Complete corrected covariance on the quotient-safe source collars. -/
noncomputable def cmp116SourcePi4QuotientExactPatchedCovariance
    {M Q Nc : ℕ} [NeZero M] [NeZero Q]
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c) :
    PhysicalEndomorphism M Q Nc :=
  cmp99CorrectedPatchedPhysicalCovariance
    (cmp99SourcePi4Charts :
      Finset (CMP99SourcePi4Chart Unit Q))
    K
    cmp99SourcePi4ChartEnlarged
    (cmp99SourcePi4ChartCore (M := M))
    hc hmass hK

/-- Defect contraction makes the quotient-safe covariance an exact right
inverse.  The quotient core partition is generated internally. -/
theorem comp_cmp116SourcePi4QuotientExactPatchedCovariance_eq_id
    {M Q Nc : ℕ} [NeZero M] [NeZero Q]
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (hD :
      ‖cmp99PatchedPhysicalParametrixDefect
          (cmp99SourcePi4Charts :
            Finset (CMP99SourcePi4Chart Unit Q))
          K
          cmp99SourcePi4ChartEnlarged
          (cmp99SourcePi4ChartCore (M := M))
          hc hmass hK‖ < 1) :
    K.comp
        (cmp116SourcePi4QuotientExactPatchedCovariance
          K hc hmass hK) =
      ContinuousLinearMap.id ℝ
        (PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc) := by
  exact comp_cmp99CorrectedPatchedPhysicalCovariance_eq_id
    (cmp99SourcePi4Charts :
      Finset (CMP99SourcePi4Chart Unit Q))
    K
    cmp99SourcePi4ChartEnlarged
    (cmp99SourcePi4ChartCore (M := M))
    hc hmass hK
    cmp99SourcePi4UnitChartCore_corePartition
    hD

/-- Matrix form of the quotient-safe exact inverse.  This is the base identity
needed by the full all-head complex weakening matrix. -/
theorem cmp116SourcePi4Quotient_precision_mul_exactCovarianceMatrix_eq_one
    {M Q Nc : ℕ} [NeZero M] [NeZero Q]
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (hD :
      ‖cmp99PatchedPhysicalParametrixDefect
          (cmp99SourcePi4Charts :
            Finset (CMP99SourcePi4Chart Unit Q))
          K
          cmp99SourcePi4ChartEnlarged
          (cmp99SourcePi4ChartCore (M := M))
          hc hmass hK‖ < 1) :
    cmp116PhysicalEndomorphismComplexMatrix K *
        cmp116PhysicalEndomorphismComplexMatrix
          (cmp116SourcePi4QuotientExactPatchedCovariance
            K hc hmass hK) =
      1 := by
  rw [← cmp116PhysicalEndomorphismComplexMatrix_comp,
    comp_cmp116SourcePi4QuotientExactPatchedCovariance_eq_id
      K hc hmass hK hD]
  exact cmp116PhysicalEndomorphismComplexMatrix_id

end

end YangMills.RG
