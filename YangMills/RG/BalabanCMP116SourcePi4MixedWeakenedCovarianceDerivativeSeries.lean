/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import Mathlib.Analysis.Calculus.SmoothSeries
import YangMills.RG.BalabanCMP116MatrixTraceLinftyOpNorm
import YangMills.RG.BalabanCMP116SourcePi4FullComplexContourDefect
import YangMills.RG.BalabanCMP116SourcePi4MixedWeakenedCovarianceDerivative

/-!
# Summable mixed physical weakening derivatives

Every finite walk layer is multiaffine in the weakening coordinates.  The
exact unit finite-difference identity therefore propagates absolute
summability from the physical covariance layers to every finite mixed
derivative.  No new term bound, ambient chart count, or volume-dependent
constant is assumed.

The final theorem differentiates the length-ordered mixed series in a fresh
coordinate.  `hasDerivAt_tsum` is invoked only after the derivative series
has been proved absolutely summable.
-/

namespace YangMills.RG

noncomputable section

open scoped Matrix.Norms.Operator

private abbrev PhysicalEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc →L[ℝ]
    PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

private theorem update_zero_unitShifted_mixed
    {D : Type*} [DecidableEq D]
    (sigma : D → ℂ) (d : D)
    (hsigma : ∀ x, ‖sigma x - 1‖ ≤ (1 : ℝ)) :
    ∀ x, ‖Function.update sigma d 0 x - 1‖ ≤ (1 : ℝ) := by
  intro x
  by_cases hx : x = d
  · subst x
    simp
  · rw [Function.update_of_ne hx]
    exact hsigma x

private theorem update_one_unitShifted_mixed
    {D : Type*} [DecidableEq D]
    (sigma : D → ℂ) (d : D)
    (hsigma : ∀ x, ‖sigma x - 1‖ ≤ (1 : ℝ)) :
    ∀ x, ‖Function.update sigma d 1 x - 1‖ ≤ (1 : ℝ) := by
  intro x
  by_cases hx : x = d
  · subst x
    simp
  · rw [Function.update_of_ne hx]
    exact hsigma x

private theorem update_zero_cap_mixed
    {D : Type*} [DecidableEq D]
    (sigma : D → ℂ) (d : D) (Rweak : ℝ)
    (hcap : ∀ x, ‖sigma x‖ ≤ Rweak) :
    ∀ x, ‖Function.update sigma d 0 x‖ ≤ Rweak := by
  intro x
  by_cases hx : x = d
  · subst x
    simpa using (norm_nonneg (sigma d)).trans (hcap d)
  · rw [Function.update_of_ne hx]
    exact hcap x

private theorem update_one_cap_mixed
    {D : Type*} [DecidableEq D]
    (sigma : D → ℂ) (d : D) (Rweak : ℝ)
    (hRweak : 1 ≤ Rweak) (hcap : ∀ x, ‖sigma x‖ ≤ Rweak) :
    ∀ x, ‖Function.update sigma d 1 x‖ ≤ Rweak := by
  intro x
  by_cases hx : x = d
  · subst x
    simpa using hRweak
  · rw [Function.update_of_ne hx]
    exact hcap x

/-- The physical contour estimates imply absolute summability, in matrix
norm, of the un-differentiated weakened covariance layers. -/
theorem
    summable_norm_cmp116SourcePi4FullComplexWeakenedCovarianceLayer
    {M Q Nc R Δ : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    {Ahead rho rate Rweak : ℝ}
    (hAhead : 0 ≤ Ahead) (hrho : 0 ≤ rho) (hrate : 0 < rate)
    (hgeom : ((2 ^ 4 : ℕ) : ℝ) * Real.exp (-rate) < 1)
    (Cert : CMP99PhysicalPatchWeightedCertificate
      (cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q))
      K cmp99SourcePi4ChartEnlarged
      (cmp99SourcePi4ChartCore (M := M))
      hc hmass hK physicalBondDist Ahead rho rate)
    (htri : ∀ target source middle :
      PhysicalBond 4 (M * (2 * Q)),
      physicalBondDist target source ≤
        physicalBondDist target middle + physicalBondDist middle source)
    (hrange : R + 1 ≤ 4 * M)
    (hΔ : ∀ x, (cmp116CoarseFaceAdj 4 Q).degree x ≤ Δ)
    (hΔ1 : 1 ≤ Δ)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (hRweak : 1 ≤ Rweak)
    (hsigma : ∀ x, ‖sigma x - 1‖ ≤ (1 : ℝ))
    (hcap : ∀ x, ‖sigma x‖ ≤ Rweak)
    (hsmall :
      ‖cmp116SourcePi4ComplexContourRatio Δ rho Rweak‖ < 1) :
    Summable fun n : ℕ =>
      ‖cmp116SourcePi4FullComplexWeakenedCovarianceLayer
        (R := R) anchor K hc hmass hK sigma n‖ := by
  let oneLayer := fun n : ℕ =>
    cmp116SourcePi4FullComplexWeakenedCovarianceLayer
      (R := R) anchor K hc hmass hK (fun _ => 1) n
  let diffLayer := fun n : ℕ =>
    cmp116SourcePi4FullComplexWeakenedCovarianceLayer
        (R := R) anchor K hc hmass hK sigma n - oneLayer n
  let rowMass : ℝ :=
    ((Nc ^ 2 - 1 : ℕ) : ℝ) *
      cmp99PhysicalBondGeometricRowSum 4 rate
  have hdiffMajor :
      Summable fun n : ℕ =>
        cmp116SourcePi4ComplexDefectLayerAmplitude
          Δ Ahead rho 1 Rweak n * rowMass :=
    (hasSum_cmp116SourcePi4ComplexDefectLayerAmplitude
      Δ Ahead rho 1 Rweak hsmall).summable.mul_right rowMass
  have hdiffNorm : Summable fun n : ℕ => ‖diffLayer n‖ := by
    apply Summable.of_nonneg_of_le (fun n => norm_nonneg (diffLayer n))
      (fun n =>
        linfty_opNorm_cmp116SourcePi4FullComplexWeakenedCovarianceLayer_sub_one_le
          anchor K hc hmass hK hAhead hrho hrate hgeom Cert htri hrange
          hΔ hΔ1 sigma (by positivity) hRweak hsigma hcap n)
    exact hdiffMajor
  let branch : ℝ := cmp116SourcePi4TerminalBranching Δ
  let qbase : ℝ := branch * rho
  have hbranch : 0 ≤ branch := by
    dsimp [branch]
    positivity
  have hqbase0 : 0 ≤ qbase := mul_nonneg hbranch hrho
  have hcontour0 :
      0 ≤ cmp116SourcePi4ComplexContourRatio Δ rho Rweak := by
    unfold cmp116SourcePi4ComplexContourRatio
    positivity
  have hcontourLt :
      cmp116SourcePi4ComplexContourRatio Δ rho Rweak < 1 := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg hcontour0] using hsmall
  have hpow : 1 ≤ Rweak ^ 10000 := one_le_pow₀ hRweak
  have hqbaseLe :
      qbase ≤ cmp116SourcePi4ComplexContourRatio Δ rho Rweak := by
    unfold cmp116SourcePi4ComplexContourRatio
    dsimp [qbase, branch]
    nlinarith
  have hqbaseNorm : ‖qbase‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hqbase0]
    exact lt_of_le_of_lt hqbaseLe hcontourLt
  have honeMajor :
      Summable fun n : ℕ => (Ahead * qbase ^ n) * rowMass :=
    ((summable_geometric_of_norm_lt_one hqbaseNorm).mul_left Ahead).mul_right
      rowMass
  have honeNorm : Summable fun n : ℕ => ‖oneLayer n‖ := by
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg (oneLayer n))
      (fun n => ?_) honeMajor
    · show ‖oneLayer n‖ ≤ (Ahead * qbase ^ n) * rowMass
      dsimp [oneLayer]
      rw [cmp116SourcePi4FullComplexWeakenedCovarianceLayer_one
        (R := R) anchor K hc hmass hK n]
      have hrow :=
        cmp116SourcePi4QuotientGeneratedWalkLayer_weightedRow_physical
          K hc hmass hK physicalBondDist hAhead hrho hrate.le Cert htri
          hrange hΔ hΔ1 n
      have hmatrix :=
        linfty_opNorm_cmp116PhysicalEndomorphismComplexMatrix_le_of_weightedRow
          (cmp116SourcePi4QuotientGeneratedWalkLayer
            (R := R) K hc hmass hK n)
          hrate hgeom hrow
      convert hmatrix using 1
      dsimp [qbase, branch, rowMass]
      rw [Nat.cast_pow, mul_pow]
      ring
  have hsum := hdiffNorm.add honeNorm
  apply Summable.of_nonneg_of_le
    (fun n => norm_nonneg
      (cmp116SourcePi4FullComplexWeakenedCovarianceLayer
        (R := R) anchor K hc hmass hK sigma n))
    (fun n => by
      calc
        ‖cmp116SourcePi4FullComplexWeakenedCovarianceLayer
            (R := R) anchor K hc hmass hK sigma n‖ =
            ‖diffLayer n + oneLayer n‖ := by
          congr 1
          dsimp [diffLayer]
          exact (sub_add_cancel _ _).symm
        _ ≤ ‖diffLayer n‖ + ‖oneLayer n‖ := norm_add_le _ _)
  exact hsum

/-- Every finite mixed weakening derivative is absolutely summable in
walk length.  The proof is induction on the erased carrier using the exact
unit finite difference, so the conclusion remains source-specific. -/
theorem
    summable_norm_cmp116SourcePi4FullComplexWeakenedCovarianceLayerMixedDerivative
    {M Q Nc R Δ : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    {Ahead rho rate Rweak : ℝ}
    (hAhead : 0 ≤ Ahead) (hrho : 0 ≤ rho) (hrate : 0 < rate)
    (hgeom : ((2 ^ 4 : ℕ) : ℝ) * Real.exp (-rate) < 1)
    (Cert : CMP99PhysicalPatchWeightedCertificate
      (cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q))
      K cmp99SourcePi4ChartEnlarged
      (cmp99SourcePi4ChartCore (M := M))
      hc hmass hK physicalBondDist Ahead rho rate)
    (htri : ∀ target source middle :
      PhysicalBond 4 (M * (2 * Q)),
      physicalBondDist target source ≤
        physicalBondDist target middle + physicalBondDist middle source)
    (hrange : R + 1 ≤ 4 * M)
    (hΔ : ∀ x, (cmp116CoarseFaceAdj 4 Q).degree x ≤ Δ)
    (hΔ1 : 1 ≤ Δ)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (S : Finset (FinBox 4 (2 * Q)))
    (hRweak : 1 ≤ Rweak)
    (hsigma : ∀ x, ‖sigma x - 1‖ ≤ (1 : ℝ))
    (hcap : ∀ x, ‖sigma x‖ ≤ Rweak)
    (hsmall :
      ‖cmp116SourcePi4ComplexContourRatio Δ rho Rweak‖ < 1) :
    Summable fun n : ℕ =>
      ‖cmp116SourcePi4FullComplexWeakenedCovarianceLayerMixedDerivative
        (R := R) anchor K hc hmass hK sigma S n‖ := by
  classical
  induction S using Finset.induction_on generalizing sigma with
  | empty =>
      simpa only [
        cmp116SourcePi4FullComplexWeakenedCovarianceLayerMixedDerivative_empty]
        using
          summable_norm_cmp116SourcePi4FullComplexWeakenedCovarianceLayer
            anchor K hc hmass hK hAhead hrho hrate hgeom Cert htri hrange
            hΔ hΔ1 sigma hRweak hsigma hcap hsmall
  | @insert d S hdS ih =>
      have hOne := ih (Function.update sigma d 1)
        (update_one_unitShifted_mixed sigma d hsigma)
        (update_one_cap_mixed sigma d Rweak hRweak hcap)
      have hZero := ih (Function.update sigma d 0)
        (update_zero_unitShifted_mixed sigma d hsigma)
        (update_zero_cap_mixed sigma d Rweak hcap)
      refine Summable.of_nonneg_of_le
        (fun n => norm_nonneg
          (cmp116SourcePi4FullComplexWeakenedCovarianceLayerMixedDerivative
            (R := R) anchor K hc hmass hK sigma (insert d S) n))
        (fun n => ?_) (hOne.add hZero)
      · show
          ‖cmp116SourcePi4FullComplexWeakenedCovarianceLayerMixedDerivative
              (R := R) anchor K hc hmass hK sigma (insert d S) n‖ ≤
            ‖cmp116SourcePi4FullComplexWeakenedCovarianceLayerMixedDerivative
              (R := R) anchor K hc hmass hK
              (Function.update sigma d 1) S n‖ +
            ‖cmp116SourcePi4FullComplexWeakenedCovarianceLayerMixedDerivative
              (R := R) anchor K hc hmass hK
              (Function.update sigma d 0) S n‖
        rw [
          cmp116SourcePi4FullComplexWeakenedCovarianceLayerMixedDerivative_insert_eq_sub
            anchor K hc hmass hK sigma S d hdS n]
        exact norm_sub_le _ _

/-- Length-ordered complete mixed derivative of the physical weakened
covariance. -/
noncomputable def
    cmp116SourcePi4FullComplexWeakenedCovarianceMatrixMixedDerivative
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (S : Finset (FinBox 4 (2 * Q))) :
    Matrix
      (CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc)
      (CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc) ℂ :=
  fun row col =>
    ∑' n : ℕ,
      cmp116SourcePi4FullComplexWeakenedCovarianceLayerMixedDerivative
        (R := R) anchor K hc hmass hK sigma S n row col

/-- The complete mixed series is independent of a coordinate already present
in its derivative carrier. -/
theorem
    cmp116SourcePi4FullComplexWeakenedCovarianceMatrixMixedDerivative_update_of_mem
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (S : Finset (FinBox 4 (2 * Q)))
    (d : FinBox 4 (2 * Q)) (hdS : d ∈ S) (z : ℂ) :
    cmp116SourcePi4FullComplexWeakenedCovarianceMatrixMixedDerivative
        (R := R) anchor K hc hmass hK
        (Function.update sigma d z) S =
      cmp116SourcePi4FullComplexWeakenedCovarianceMatrixMixedDerivative
        (R := R) anchor K hc hmass hK sigma S := by
  funext row col
  apply tsum_congr
  intro n
  exact congrFun (congrFun
    (cmp116SourcePi4FullComplexWeakenedCovarianceLayerMixedDerivative_update_of_mem
      anchor K hc hmass hK sigma S d hdS z n) row) col

/-- A fresh weakening derivative passes through the complete length-ordered
mixed series.  Absolute summability of both the base and derivative series
is generated internally from the physical contour estimates. -/
theorem
    hasDerivAt_cmp116SourcePi4FullComplexWeakenedCovarianceMatrixMixedDerivative_update
    {M Q Nc R Δ : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    {Ahead rho rate Rweak : ℝ}
    (hAhead : 0 ≤ Ahead) (hrho : 0 ≤ rho) (hrate : 0 < rate)
    (hgeom : ((2 ^ 4 : ℕ) : ℝ) * Real.exp (-rate) < 1)
    (Cert : CMP99PhysicalPatchWeightedCertificate
      (cmp99SourcePi4Charts :
        Finset (CMP99SourcePi4Chart Unit Q))
      K cmp99SourcePi4ChartEnlarged
      (cmp99SourcePi4ChartCore (M := M))
      hc hmass hK physicalBondDist Ahead rho rate)
    (htri : ∀ target source middle :
      PhysicalBond 4 (M * (2 * Q)),
      physicalBondDist target source ≤
        physicalBondDist target middle + physicalBondDist middle source)
    (hrange : R + 1 ≤ 4 * M)
    (hΔ : ∀ x, (cmp116CoarseFaceAdj 4 Q).degree x ≤ Δ)
    (hΔ1 : 1 ≤ Δ)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (S : Finset (FinBox 4 (2 * Q)))
    (d : FinBox 4 (2 * Q)) (hdS : d ∉ S)
    (hRweak : 1 ≤ Rweak)
    (hsigma : ∀ x, ‖sigma x - 1‖ ≤ (1 : ℝ))
    (hcap : ∀ x, ‖sigma x‖ ≤ Rweak)
    (hsmall :
      ‖cmp116SourcePi4ComplexContourRatio Δ rho Rweak‖ < 1)
    (row col : CMP116PhysicalWalkCoordinate
      4 (M * (2 * Q)) Nc)
    (t : ℂ) :
    HasDerivAt
      (fun z =>
        cmp116SourcePi4FullComplexWeakenedCovarianceMatrixMixedDerivative
          (R := R) anchor K hc hmass hK
          (Function.update sigma d z) S row col)
      (cmp116SourcePi4FullComplexWeakenedCovarianceMatrixMixedDerivative
        (R := R) anchor K hc hmass hK sigma (insert d S) row col)
      t := by
  let derivativeTerm : ℕ → ℂ := fun n =>
    cmp116SourcePi4FullComplexWeakenedCovarianceLayerMixedDerivative
      (R := R) anchor K hc hmass hK sigma (insert d S) n row col
  have hderivativeMatrix :=
    summable_norm_cmp116SourcePi4FullComplexWeakenedCovarianceLayerMixedDerivative
      anchor K hc hmass hK hAhead hrho hrate hgeom Cert htri hrange hΔ hΔ1
      sigma (insert d S) hRweak hsigma hcap hsmall
  have hderivative :
      Summable fun n : ℕ => ‖derivativeTerm n‖ := by
    apply Summable.of_nonneg_of_le
      (fun n => norm_nonneg (derivativeTerm n))
      (fun n => by
        dsimp [derivativeTerm]
        exact norm_matrix_entry_le_linfty_opNorm _ row col)
    exact hderivativeMatrix
  have hbaseMatrix :=
    summable_norm_cmp116SourcePi4FullComplexWeakenedCovarianceLayerMixedDerivative
      anchor K hc hmass hK hAhead hrho hrate hgeom Cert htri hrange hΔ hΔ1
      (Function.update sigma d 1) S hRweak
      (update_one_unitShifted_mixed sigma d hsigma)
      (update_one_cap_mixed sigma d Rweak hRweak hcap) hsmall
  have hbase : Summable fun n : ℕ =>
      cmp116SourcePi4FullComplexWeakenedCovarianceLayerMixedDerivative
        (R := R) anchor K hc hmass hK
        (Function.update sigma d 1) S n row col := by
    apply Summable.of_norm
    apply Summable.of_nonneg_of_le
      (fun n => norm_nonneg
        (cmp116SourcePi4FullComplexWeakenedCovarianceLayerMixedDerivative
          (R := R) anchor K hc hmass hK
          (Function.update sigma d 1) S n row col))
      (fun n =>
        norm_matrix_entry_le_linfty_opNorm
          (cmp116SourcePi4FullComplexWeakenedCovarianceLayerMixedDerivative
            (R := R) anchor K hc hmass hK
            (Function.update sigma d 1) S n) row col)
    exact hbaseMatrix
  have hseries := hasDerivAt_tsum
    (g := fun n z =>
      cmp116SourcePi4FullComplexWeakenedCovarianceLayerMixedDerivative
        (R := R) anchor K hc hmass hK
        (Function.update sigma d z) S n row col)
    (g' := fun n _ => derivativeTerm n)
    (u := fun n => ‖derivativeTerm n‖) (y₀ := (1 : ℂ))
    hderivative
    (fun n z =>
      hasDerivAt_cmp116SourcePi4FullComplexWeakenedCovarianceLayerMixedDerivative_update
        anchor K hc hmass hK sigma S d hdS n row col z)
    (fun n _ => le_rfl)
    hbase t
  simpa [cmp116SourcePi4FullComplexWeakenedCovarianceMatrixMixedDerivative,
    derivativeTerm] using hseries

end

end YangMills.RG
