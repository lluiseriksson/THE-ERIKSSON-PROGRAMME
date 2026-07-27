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

/-- Strict coercivity makes a continuous-linear right inverse unique. -/
theorem rightInverse_unique_of_isCoerciveCLM
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (A B₁ B₂ : E →L[ℝ] E) {c : ℝ} (hc : 0 < c)
    (hA : IsCoerciveCLM A c)
    (h₁ : A.comp B₁ = ContinuousLinearMap.id ℝ E)
    (h₂ : A.comp B₂ = ContinuousLinearMap.id ℝ E) :
    B₁ = B₂ := by
  ext x
  apply isCoerciveCLM_injective A hc hA
  have h₁x := congrArg (fun T : E →L[ℝ] E => T x) h₁
  have h₂x := congrArg (fun T : E →L[ℝ] E => T x) h₂
  simpa using h₁x.trans h₂x.symm

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

/-- For the interacting Wilson precision, the quotient-safe patched
covariance is the same exact inverse as the coercivity-generated physical
covariance. -/
theorem
    cmp116SourcePi4QuotientExactPatchedCovariance_eq_interactingPhysicalCovariance
    {M Q Nc : ℕ}
    [NeZero M] [NeZero Q] [NeZero Nc]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (U : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc)
    {a CP ε mass : ℝ} (ha : 0 < a)
    (hP : FlatGaugeHodgePoincare 4 M (2 * Q) Nc
      (matrixSUNAdjointModel Nc) CP)
    (hε : 0 ≤ ε) (hsmall : PhysicalWilsonSmallBackground U ε)
    (hbudget : cmp116ConcreteInteractingWilsonGaugeDefectBudget 4 Nc ε <
      min 1 a / CP)
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
            U ha hP hε hsmall)‖ < 1) :
    cmp116SourcePi4QuotientExactPatchedCovariance
        (interactingPhysicalBasePrecisionCLM U a)
        (sub_pos.mpr hbudget) hmass
        (isCoerciveCLM_interactingPhysicalBasePrecision
          U ha hP hε hsmall) =
      interactingPhysicalCovarianceCLM
        U ha hP hε hsmall hbudget := by
  apply rightInverse_unique_of_isCoerciveCLM
    (interactingPhysicalBasePrecisionCLM U a)
    _ _
    (sub_pos.mpr hbudget)
    (isCoerciveCLM_interactingPhysicalBasePrecision U ha hP hε hsmall)
  · exact
      comp_cmp116SourcePi4QuotientExactPatchedCovariance_eq_id
        (interactingPhysicalBasePrecisionCLM U a)
        (sub_pos.mpr hbudget) hmass
        (isCoerciveCLM_interactingPhysicalBasePrecision
          U ha hP hε hsmall) hD
  · exact interactingPhysicalBasePrecision_comp_covariance
      U ha hP hε hsmall hbudget

/-- Consequently, the fully coupled weakened coarse middle is literally the
physical CMP99 middle `Q G Q*` for the interacting Wilson covariance. -/
theorem
    cmp99SourcePi4WeakenedCoarseMiddle_one_eq_physicalCoarseMiddle
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
            U ha hP hε hsmall)‖ < 1) :
    cmp99SourcePi4WeakenedCoarseMiddle
        (R := R) anchor (interactingPhysicalBasePrecisionCLM U a)
        (sub_pos.mpr hbudget) hmass
        (isCoerciveCLM_interactingPhysicalBasePrecision
          U ha hP hε hsmall) (fun _ => 1) =
      cmp99SourceEq3126PhysicalCoarseMiddle
        U ha hP hε hsmall hbudget := by
  rw [cmp99SourcePi4WeakenedCoarseMiddle_one_eq_exact
    anchor (interactingPhysicalBasePrecisionCLM U a)
    hsourceRange hrange (sub_pos.mpr hbudget) hmass
    (isCoerciveCLM_interactingPhysicalBasePrecision
      U ha hP hε hsmall) hD]
  rw [
    cmp116SourcePi4QuotientExactPatchedCovariance_eq_interactingPhysicalCovariance
      U ha hP hε hsmall hbudget hmass hD]
  rfl

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

/-- With the interacting precision and its physical coarse covariance, the
fully coupled rectangular weakened minimizer recovers the auxiliary physical
CMP99 background minimizer exactly. -/
theorem
    cmp99SourcePi4WeakenedBackgroundMinimizer_one_eq_physicalH
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
            U ha hP hε hsmall)‖ < 1) :
    cmp99SourcePi4WeakenedBackgroundMinimizer
        (R := R) anchor (interactingPhysicalBasePrecisionCLM U a)
        (sub_pos.mpr hbudget) hmass
        (isCoerciveCLM_interactingPhysicalBasePrecision
          U ha hP hε hsmall) (fun _ => 1)
        (cmp99SourceEq3126PhysicalCoarseCovariance
          U ha hP hε hsmall hbudget) =
      cmp99SourceEq3126PhysicalH U ha hP hε hsmall hbudget := by
  rw [cmp99SourcePi4WeakenedBackgroundMinimizer_one_eq_exact
    anchor (interactingPhysicalBasePrecisionCLM U a)
    hsourceRange hrange (sub_pos.mpr hbudget) hmass
    (isCoerciveCLM_interactingPhysicalBasePrecision
      U ha hP hε hsmall) hD]
  rw [
    cmp116SourcePi4QuotientExactPatchedCovariance_eq_interactingPhysicalCovariance
      U ha hP hε hsmall hbudget hmass hD]
  rfl

end

end YangMills.RG
