/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceEq3126PhysicalH
import YangMills.RG.BalabanCMP116SourcePi4FullWeakenedCovariance

/-!
# The weakened coarse middle in the CMP99 background minimizer

The source `Pi^4` random-walk series constructs the weakened fine covariance
`G(s) : E → E`.  It must not be inserted directly into the rectangular
propagator slot `H : F → E` of CMP102 equation (80).  The source-faithful
first step is instead the coarse middle

`Q G(s) Q* : F → F`,

which is the operator inverted in CMP99 equation (3.126).  This module fixes
that distinction in the types and proves that full coupling recovers the
coarse middle built from the exact patched covariance.

No invertibility of the weakened middle away from full coupling is asserted.
-/

namespace YangMills.RG

noncomputable section

private abbrev FineField (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] [NeZero (2 * Q)] [NeZero (M * (2 * Q))] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

private abbrev CoarseField (Q Nc : ℕ) [NeZero (2 * Q)] :=
  PhysicalGaugeOneCochain 4 (2 * Q) Nc

private abbrev FineEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] [NeZero (2 * Q)] [NeZero (M * (2 * Q))] :=
  FineField M Q Nc →L[ℝ] FineField M Q Nc

/-- The literal weakened version of the middle `Q G Q*` in CMP99
equation (3.126). -/
noncomputable def cmp99SourcePi4WeakenedCoarseMiddle
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (anchor : FinBox 4 Q)
    (K : FineEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (s : FinBox 4 (2 * Q) → ℝ) :
    CoarseField Q Nc →L[ℝ] CoarseField Q Nc :=
  let Qblock :=
    flatBlockConstraintQCLM (d := 4) (Nc := Nc) M (2 * Q)
  let Gs :=
    cmp116SourcePi4FullWeakenedCovariance
      (R := R) anchor K hc hmass hK s
  Qblock.comp (Gs.comp Qblock.adjoint)

/-- At full coupling, the weakened coarse middle is exactly `Q G Q*`
formed with the quotient-safe exact patched covariance. -/
theorem cmp99SourcePi4WeakenedCoarseMiddle_one_eq_exact
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (anchor : FinBox 4 Q)
    (K : FineEndomorphism M Q Nc)
    (hsourceRange : R + 1 ≤ 4 * M)
    (hrange : PhysicalCovarianceFiniteRange K physicalBondDist R)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (hD :
      ‖cmp99PatchedPhysicalParametrixDefect
          (cmp99SourcePi4Charts :
            Finset (CMP99SourcePi4Chart Unit Q))
          K cmp99SourcePi4ChartEnlarged
          (cmp99SourcePi4ChartCore (M := M))
          hc hmass hK‖ < 1) :
    cmp99SourcePi4WeakenedCoarseMiddle
        (R := R) anchor K hc hmass hK (fun _ => 1) =
      let Qblock :=
        flatBlockConstraintQCLM (d := 4) (Nc := Nc) M (2 * Q)
      Qblock.comp
        ((cmp116SourcePi4QuotientExactPatchedCovariance
          K hc hmass hK).comp Qblock.adjoint) := by
  unfold cmp99SourcePi4WeakenedCoarseMiddle
  rw [cmp116SourcePi4FullWeakenedCovariance_one_eq_exact
    anchor K hsourceRange hrange hc hmass hK hD]

/-- Rectangular weakened background minimizer assembled according to CMP99
equation (3.126).  The caller supplies the coarse inverse of `Q G(s) Q*`;
away from full coupling its existence is a separate analytic question. -/
noncomputable def cmp99SourcePi4WeakenedBackgroundMinimizer
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (anchor : FinBox 4 Q)
    (K : FineEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (s : FinBox 4 (2 * Q) → ℝ)
    (coarseCovariance : CoarseField Q Nc →L[ℝ] CoarseField Q Nc) :
    CoarseField Q Nc →L[ℝ] FineField M Q Nc :=
  let Qblock :=
    flatBlockConstraintQCLM (d := 4) (Nc := Nc) M (2 * Q)
  let Gs :=
    cmp116SourcePi4FullWeakenedCovariance
      (R := R) anchor K hc hmass hK s
  Gs.comp (Qblock.adjoint.comp coarseCovariance)

/-- A right inverse for the weakened coarse middle gives the exact block
response `Q H(s) = 1`. -/
theorem
    flatBlockConstraint_comp_cmp99SourcePi4WeakenedBackgroundMinimizer_eq_id
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (anchor : FinBox 4 Q)
    (K : FineEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (s : FinBox 4 (2 * Q) → ℝ)
    (coarseCovariance : CoarseField Q Nc →L[ℝ] CoarseField Q Nc)
    (hinverse :
      (cmp99SourcePi4WeakenedCoarseMiddle
        (R := R) anchor K hc hmass hK s).comp coarseCovariance =
          ContinuousLinearMap.id ℝ (CoarseField Q Nc)) :
    (flatBlockConstraintQCLM (d := 4) (Nc := Nc) M (2 * Q)).comp
        (cmp99SourcePi4WeakenedBackgroundMinimizer
          (R := R) anchor K hc hmass hK s coarseCovariance) =
      ContinuousLinearMap.id ℝ (CoarseField Q Nc) := by
  simpa [cmp99SourcePi4WeakenedCoarseMiddle,
    cmp99SourcePi4WeakenedBackgroundMinimizer,
    ContinuousLinearMap.comp_assoc] using hinverse

/-- At full coupling, the rectangular minimizer uses the exact patched fine
covariance and the supplied coarse covariance, with no extra fine propagator
factor. -/
theorem cmp99SourcePi4WeakenedBackgroundMinimizer_one_eq_exact
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (anchor : FinBox 4 Q)
    (K : FineEndomorphism M Q Nc)
    (hsourceRange : R + 1 ≤ 4 * M)
    (hrange : PhysicalCovarianceFiniteRange K physicalBondDist R)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (hD :
      ‖cmp99PatchedPhysicalParametrixDefect
          (cmp99SourcePi4Charts :
            Finset (CMP99SourcePi4Chart Unit Q))
          K cmp99SourcePi4ChartEnlarged
          (cmp99SourcePi4ChartCore (M := M))
          hc hmass hK‖ < 1)
    (coarseCovariance : CoarseField Q Nc →L[ℝ] CoarseField Q Nc) :
    cmp99SourcePi4WeakenedBackgroundMinimizer
        (R := R) anchor K hc hmass hK (fun _ => 1) coarseCovariance =
      let Qblock :=
        flatBlockConstraintQCLM (d := 4) (Nc := Nc) M (2 * Q)
      (cmp116SourcePi4QuotientExactPatchedCovariance
          K hc hmass hK).comp (Qblock.adjoint.comp coarseCovariance) := by
  unfold cmp99SourcePi4WeakenedBackgroundMinimizer
  rw [cmp116SourcePi4FullWeakenedCovariance_one_eq_exact
    anchor K hsourceRange hrange hc hmass hK hD]

end

end YangMills.RG
