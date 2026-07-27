/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80PhysicalH
import YangMills.RG.BalabanCMP99SourcePi4WeakenedCoarseMiddle

/-!
# The rectangular source-Pi4 weakening of CMP102 equation (80)

The source random-walk construction first produces a weakened fine Green
operator `G(s) : E → E`.  CMP102 equation (80), however, consumes the
rectangular background minimizer

`H(s) = G(s) Q* (Q G(s) Q*)⁻¹ : F → E`.

This module inserts that literal rectangular operator into equation (80).
The only additional analytic input away from full coupling is coercivity of
the source coarse middle `Q G(s) Q*`.  At full coupling the potential is
proved equal to the physical CMP102 potential, rather than to a second fine
covariance.
-/

namespace YangMills.RG

open scoped RealInnerProductSpace

noncomputable section

private abbrev FineField (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))] :=
  FinePhysicalOneCochain 4 M (2 * Q) Nc

private abbrev CoarseField (Q Nc : ℕ) [NeZero (2 * Q)] :=
  CoarsePhysicalOneCochain 4 (2 * Q) Nc

/-- CMP102 equation (80) with the literal source-faithful rectangular
weakened background minimizer. -/
noncomputable def cmp102Eq80SourcePi4RectangularWeakenedPotential
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero Nc]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (U : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc)
    {a CP ε mass : ℝ} (ha : 0 < a)
    (hP : FlatGaugeHodgePoincare 4 M (2 * Q) Nc
      (matrixSUNAdjointModel Nc) CP)
    (hε : 0 ≤ ε) (hsmall : PhysicalWilsonSmallBackground U ε)
    (hbudget : cmp116ConcreteInteractingWilsonGaugeDefectBudget 4 Nc ε <
      min 1 a / CP)
    (anchor : FinBox 4 Q)
    (hmass : 0 < mass)
    (s : FinBox 4 (2 * Q) → ℝ)
    {coarseRate : ℝ} (hcoarseRate : 0 < coarseRate)
    (hcoarse : IsCoerciveCLM
      (cmp99SourcePi4WeakenedCoarseMiddle
        (R := R) anchor (interactingPhysicalBasePrecisionCLM U a)
        (sub_pos.mpr hbudget) hmass
        (isCoerciveCLM_interactingPhysicalBasePrecision
          U ha hP hε hsmall) s) coarseRate)
    (D D₃ : FineField M Q Nc → CoarseField Q Nc)
    (V₀ : FineField M Q Nc → ℝ)
    (Δπ : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    (J A : FineField M Q Nc) : ℝ :=
  cmp102Eq80GlobalPotential D D₃ V₀
    (cmp99SourcePi4WeakenedPhysicalH
      (R := R) anchor (interactingPhysicalBasePrecisionCLM U a)
      (sub_pos.mpr hbudget) hmass
      (isCoerciveCLM_interactingPhysicalBasePrecision
        U ha hP hε hsmall) s hcoarseRate hcoarse)
    Δπ J A

/-- Full coupling recovers the physical rectangular equation-(80) potential
exactly. -/
theorem cmp102Eq80SourcePi4RectangularWeakenedPotential_one_eq_physical
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero Nc]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (U : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc)
    {a CP ε mass : ℝ} (ha : 0 < a)
    (hP : FlatGaugeHodgePoincare 4 M (2 * Q) Nc
      (matrixSUNAdjointModel Nc) CP)
    (hε : 0 ≤ ε) (hsmall : PhysicalWilsonSmallBackground U ε)
    (hbudget : cmp116ConcreteInteractingWilsonGaugeDefectBudget 4 Nc ε <
      min 1 a / CP)
    (anchor : FinBox 4 Q)
    (hsourceRange : R + 1 ≤ 4 * M)
    (hrange : PhysicalCovarianceFiniteRange
      (interactingPhysicalBasePrecisionCLM U a) physicalBondDist R)
    (hmass : 0 < mass)
    (hD :
      ‖cmp99PatchedPhysicalParametrixDefect
          (cmp99SourcePi4Charts :
            Finset (CMP99SourcePi4Chart Unit Q))
          (interactingPhysicalBasePrecisionCLM U a)
          cmp99SourcePi4ChartEnlarged
          (cmp99SourcePi4ChartCore (M := M))
          (sub_pos.mpr hbudget) hmass
          (isCoerciveCLM_interactingPhysicalBasePrecision
            U ha hP hε hsmall)‖ < 1)
    {coarseRate : ℝ} (hcoarseRate : 0 < coarseRate)
    (hcoarse : IsCoerciveCLM
      (cmp99SourcePi4WeakenedCoarseMiddle
        (R := R) anchor (interactingPhysicalBasePrecisionCLM U a)
        (sub_pos.mpr hbudget) hmass
        (isCoerciveCLM_interactingPhysicalBasePrecision
          U ha hP hε hsmall) (fun _ => 1)) coarseRate)
    (D D₃ : FineField M Q Nc → CoarseField Q Nc)
    (V₀ : FineField M Q Nc → ℝ)
    (Δπ : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    (J A : FineField M Q Nc) :
    cmp102Eq80SourcePi4RectangularWeakenedPotential
        (R := R) U ha hP hε hsmall hbudget anchor hmass
        (fun _ => 1) hcoarseRate hcoarse D D₃ V₀ Δπ J A =
      cmp102Eq80PhysicalGlobalPotential
        U ha hP hε hsmall hbudget D D₃ V₀ Δπ J A := by
  unfold cmp102Eq80SourcePi4RectangularWeakenedPotential
  unfold cmp102Eq80PhysicalGlobalPotential
  rw [cmp99SourcePi4WeakenedPhysicalH_one_eq_physicalH
    U ha hP hε hsmall hbudget anchor hsourceRange hrange hmass hD
      hcoarseRate hcoarse]

/-- Component normalizations make every rectangular weakened potential
vanish at the origin. -/
theorem cmp102Eq80SourcePi4RectangularWeakenedPotential_zero
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero Nc]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (U : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc)
    {a CP ε mass : ℝ} (ha : 0 < a)
    (hP : FlatGaugeHodgePoincare 4 M (2 * Q) Nc
      (matrixSUNAdjointModel Nc) CP)
    (hε : 0 ≤ ε) (hsmall : PhysicalWilsonSmallBackground U ε)
    (hbudget : cmp116ConcreteInteractingWilsonGaugeDefectBudget 4 Nc ε <
      min 1 a / CP)
    (anchor : FinBox 4 Q) (hmass : 0 < mass)
    (s : FinBox 4 (2 * Q) → ℝ)
    {coarseRate : ℝ} (hcoarseRate : 0 < coarseRate)
    (hcoarse : IsCoerciveCLM
      (cmp99SourcePi4WeakenedCoarseMiddle
        (R := R) anchor (interactingPhysicalBasePrecisionCLM U a)
        (sub_pos.mpr hbudget) hmass
        (isCoerciveCLM_interactingPhysicalBasePrecision
          U ha hP hε hsmall) s) coarseRate)
    (D D₃ : FineField M Q Nc → CoarseField Q Nc)
    (V₀ : FineField M Q Nc → ℝ)
    (Δπ : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    (J : FineField M Q Nc)
    (hD0 : D 0 = 0) (hD₃0 : D₃ 0 = 0) (hV₀0 : V₀ 0 = 0) :
    cmp102Eq80SourcePi4RectangularWeakenedPotential
      (R := R) U ha hP hε hsmall hbudget anchor hmass s
        hcoarseRate hcoarse D D₃ V₀ Δπ J 0 = 0 := by
  exact cmp102Eq80GlobalPotential_zero D D₃ V₀
    (cmp99SourcePi4WeakenedPhysicalH
      (R := R) anchor (interactingPhysicalBasePrecisionCLM U a)
      (sub_pos.mpr hbudget) hmass
      (isCoerciveCLM_interactingPhysicalBasePrecision
        U ha hP hε hsmall) s hcoarseRate hcoarse)
    Δπ J hD0 hD₃0 hV₀0

/-- `C²` field regularity propagates through the rectangular weakened
background minimizer. -/
theorem contDiff_two_cmp102Eq80SourcePi4RectangularWeakenedPotential
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero Nc]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (U : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc)
    {a CP ε mass : ℝ} (ha : 0 < a)
    (hP : FlatGaugeHodgePoincare 4 M (2 * Q) Nc
      (matrixSUNAdjointModel Nc) CP)
    (hε : 0 ≤ ε) (hsmall : PhysicalWilsonSmallBackground U ε)
    (hbudget : cmp116ConcreteInteractingWilsonGaugeDefectBudget 4 Nc ε <
      min 1 a / CP)
    (anchor : FinBox 4 Q) (hmass : 0 < mass)
    (s : FinBox 4 (2 * Q) → ℝ)
    {coarseRate : ℝ} (hcoarseRate : 0 < coarseRate)
    (hcoarse : IsCoerciveCLM
      (cmp99SourcePi4WeakenedCoarseMiddle
        (R := R) anchor (interactingPhysicalBasePrecisionCLM U a)
        (sub_pos.mpr hbudget) hmass
        (isCoerciveCLM_interactingPhysicalBasePrecision
          U ha hP hε hsmall) s) coarseRate)
    (D D₃ : FineField M Q Nc → CoarseField Q Nc)
    (V₀ : FineField M Q Nc → ℝ)
    (Δπ : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    (J : FineField M Q Nc)
    (hD : ContDiff ℝ 2 D) (hD₃ : ContDiff ℝ 2 D₃)
    (hV₀ : ContDiff ℝ 2 V₀) :
    ContDiff ℝ 2
      (cmp102Eq80SourcePi4RectangularWeakenedPotential
        (R := R) U ha hP hε hsmall hbudget anchor hmass s
          hcoarseRate hcoarse D D₃ V₀ Δπ J) := by
  exact contDiff_two_cmp102Eq80GlobalPotential D D₃ V₀
    (cmp99SourcePi4WeakenedPhysicalH
      (R := R) anchor (interactingPhysicalBasePrecisionCLM U a)
      (sub_pos.mpr hbudget) hmass
      (isCoerciveCLM_interactingPhysicalBasePrecision
        U ha hP hε hsmall) s hcoarseRate hcoarse)
    Δπ J hD hD₃ hV₀

end

end YangMills.RG
