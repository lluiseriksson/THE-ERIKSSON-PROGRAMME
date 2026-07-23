/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116SourcePi4TerminalComplexDefectBound

/-!
# Summed source complex contour defect

The length-layer estimate is summed with the exact differentiated geometric
series.  The contour radius survives linearly, and the only ratio is the
literal local branching factor times the physical continuation rate and the
source weakening budget.
-/

namespace YangMills.RG

noncomputable section

open scoped Matrix.Norms.Operator

private abbrev PhysicalEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc →L[ℝ]
    PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

/-- Scalar ratio of the source contour-defect series. -/
noncomputable def cmp116SourcePi4ComplexContourRatio
    (Δ : ℕ) (rho Rweak : ℝ) : ℝ :=
  (cmp116SourcePi4TerminalBranching Δ : ℝ) * rho * Rweak ^ 10000

/-- Length-zero prefactor of the source contour-defect series. -/
noncomputable def cmp116SourcePi4ComplexContourPrefactor
    (Ahead radius Rweak : ℝ) : ℝ :=
  (10000 : ℝ) * radius * Rweak ^ 10000 * Ahead

/-- The raw layer amplitude is exactly a differentiated geometric term. -/
theorem cmp116SourcePi4ComplexDefectLayerAmplitude_eq_contourPrefactor_mul
    (Δ : ℕ) (Ahead rho radius Rweak : ℝ) (n : ℕ) :
    cmp116SourcePi4ComplexDefectLayerAmplitude
        Δ Ahead rho radius Rweak n =
      cmp116SourcePi4ComplexContourPrefactor Ahead radius Rweak *
        ((n + 1 : ℕ) : ℝ) *
        cmp116SourcePi4ComplexContourRatio Δ rho Rweak ^ n := by
  unfold cmp116SourcePi4ComplexDefectLayerAmplitude
    cmp116SourcePi4ComplexContourPrefactor
    cmp116SourcePi4ComplexContourRatio
  rw [Nat.cast_pow]
  push_cast
  rw [show 10000 * (n + 1) = 10000 + 10000 * n by omega]
  rw [pow_add, pow_mul, mul_pow, mul_pow]
  ring

/-- Exact scalar sum of the source contour-defect amplitudes. -/
theorem hasSum_cmp116SourcePi4ComplexDefectLayerAmplitude
    (Δ : ℕ) (Ahead rho radius Rweak : ℝ)
    (hsmall : ‖cmp116SourcePi4ComplexContourRatio Δ rho Rweak‖ < 1) :
    HasSum
      (cmp116SourcePi4ComplexDefectLayerAmplitude
        Δ Ahead rho radius Rweak)
      (cmp116SourcePi4ComplexContourPrefactor Ahead radius Rweak *
        (1 - cmp116SourcePi4ComplexContourRatio Δ rho Rweak)⁻¹ ^ 2) := by
  have hgeom :
      HasSum
        (fun n : ℕ =>
          ((n + 1 : ℕ) : ℝ) *
            cmp116SourcePi4ComplexContourRatio Δ rho Rweak ^ n)
        ((1 - cmp116SourcePi4ComplexContourRatio Δ rho Rweak)⁻¹ ^ 2) := by
    simpa using
      (hasSum_choose_mul_geometric_of_norm_lt_one'
        (R := ℝ) 1 hsmall)
  convert hgeom.mul_left
    (cmp116SourcePi4ComplexContourPrefactor Ahead radius Rweak) using 1
  ext n
  simpa only [mul_assoc] using
    (cmp116SourcePi4ComplexDefectLayerAmplitude_eq_contourPrefactor_mul
      Δ Ahead rho radius Rweak n)

/-- The complete matrix-valued contour-defect layers are summable in the
volume-uniform `L∞` operator norm. -/
theorem summable_cmp116SourcePi4FullComplexWeakenedCovarianceLayer_sub_one
    {M Q Nc R Δ : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    {Ahead rho rate radius Rweak : ℝ}
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
    (hradius : 0 ≤ radius) (hRweak : 1 ≤ Rweak)
    (hdiff : ∀ d, ‖sigma d - 1‖ ≤ radius)
    (hcap : ∀ d, ‖sigma d‖ ≤ Rweak)
    (hsmall :
      ‖cmp116SourcePi4ComplexContourRatio Δ rho Rweak‖ < 1) :
    Summable fun n : ℕ =>
      cmp116SourcePi4FullComplexWeakenedCovarianceLayer
          (R := R) anchor K hc hmass hK sigma n -
        cmp116SourcePi4FullComplexWeakenedCovarianceLayer
          (R := R) anchor K hc hmass hK (fun _ => 1) n := by
  let rowMass : ℝ :=
    ((Nc ^ 2 - 1 : ℕ) : ℝ) *
      cmp99PhysicalBondGeometricRowSum 4 rate
  have hmajor :
      Summable fun n : ℕ =>
        cmp116SourcePi4ComplexDefectLayerAmplitude
          Δ Ahead rho radius Rweak n * rowMass :=
    (hasSum_cmp116SourcePi4ComplexDefectLayerAmplitude
      Δ Ahead rho radius Rweak hsmall).summable.mul_right rowMass
  apply Summable.of_norm_bounded hmajor
  intro n
  exact
    linfty_opNorm_cmp116SourcePi4FullComplexWeakenedCovarianceLayer_sub_one_le
      anchor K hc hmass hK hAhead hrho hrate hgeom Cert htri hrange
      hΔ hΔ1 sigma hradius hRweak hdiff hcap n

/-- Under the contour ratio condition the fully coupled matrix layers are
also summable in matrix norm.  This is the base half needed to identify the
literal pointwise complex series with a matrix `tsum`. -/
theorem summable_cmp116SourcePi4FullComplexWeakenedCovarianceLayer_one
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
    (hRweak : 1 ≤ Rweak)
    (hsmall :
      ‖cmp116SourcePi4ComplexContourRatio Δ rho Rweak‖ < 1) :
    Summable fun n : ℕ =>
      cmp116SourcePi4FullComplexWeakenedCovarianceLayer
        (R := R) anchor K hc hmass hK (fun _ => 1) n := by
  let branch : ℝ := cmp116SourcePi4TerminalBranching Δ
  let qbase : ℝ := branch * rho
  let rowMass : ℝ :=
    ((Nc ^ 2 - 1 : ℕ) : ℝ) *
      cmp99PhysicalBondGeometricRowSum 4 rate
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
  have hmajor :
      Summable fun n : ℕ => (Ahead * qbase ^ n) * rowMass :=
    ((summable_geometric_of_norm_lt_one hqbaseNorm).mul_left Ahead).mul_right
      rowMass
  apply Summable.of_norm_bounded hmajor
  intro n
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
  dsimp [qbase, branch]
  rw [Nat.cast_pow, mul_pow]
  ring

/-- Complete volume-uniform contour estimate for the literal complex
weakened covariance matrix.  The defect is linear in the contour radius and
has the exact differentiated-geometric denominator. -/
theorem linfty_opNorm_cmp116SourcePi4FullComplexWeakenedCovarianceMatrix_sub_one_le
    {M Q Nc R Δ : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    {Ahead rho rate radius Rweak : ℝ}
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
    (hradius : 0 ≤ radius) (hRweak : 1 ≤ Rweak)
    (hdiff : ∀ d, ‖sigma d - 1‖ ≤ radius)
    (hcap : ∀ d, ‖sigma d‖ ≤ Rweak)
    (hsmall :
      ‖cmp116SourcePi4ComplexContourRatio Δ rho Rweak‖ < 1) :
    ‖cmp116SourcePi4FullComplexWeakenedCovarianceMatrix
          (R := R) anchor K hc hmass hK sigma -
        cmp116SourcePi4FullComplexWeakenedCovarianceMatrix
          (R := R) anchor K hc hmass hK (fun _ => 1)‖ ≤
      (cmp116SourcePi4ComplexContourPrefactor Ahead radius Rweak *
        (1 - cmp116SourcePi4ComplexContourRatio Δ rho Rweak)⁻¹ ^ 2) *
        (((Nc ^ 2 - 1 : ℕ) : ℝ) *
          cmp99PhysicalBondGeometricRowSum 4 rate) := by
  let sigmaLayer := fun n : ℕ =>
    cmp116SourcePi4FullComplexWeakenedCovarianceLayer
      (R := R) anchor K hc hmass hK sigma n
  let oneLayer := fun n : ℕ =>
    cmp116SourcePi4FullComplexWeakenedCovarianceLayer
      (R := R) anchor K hc hmass hK (fun _ => 1) n
  let diffLayer := fun n : ℕ => sigmaLayer n - oneLayer n
  let rowMass : ℝ :=
    ((Nc ^ 2 - 1 : ℕ) : ℝ) *
      cmp99PhysicalBondGeometricRowSum 4 rate
  have hdiffSum : Summable diffLayer := by
    exact
      summable_cmp116SourcePi4FullComplexWeakenedCovarianceLayer_sub_one
        anchor K hc hmass hK hAhead hrho hrate hgeom Cert htri hrange
        hΔ hΔ1 sigma hradius hRweak hdiff hcap hsmall
  have honeSum : Summable oneLayer := by
    exact
      summable_cmp116SourcePi4FullComplexWeakenedCovarianceLayer_one
        anchor K hc hmass hK hAhead hrho hrate hgeom Cert htri hrange
        hΔ hΔ1 hRweak hsmall
  have hsigmaSum : Summable sigmaLayer := by
    have hadd := hdiffSum.add honeSum
    exact hadd.congr fun n => by
      dsimp [diffLayer]
      exact sub_add_cancel (sigmaLayer n) (oneLayer n)
  have hsigmaMatrix :
      cmp116SourcePi4FullComplexWeakenedCovarianceMatrix
          (R := R) anchor K hc hmass hK sigma =
        ∑' n : ℕ, sigmaLayer n := by
    funext row col
    rw [cmp116SourcePi4FullComplexWeakenedCovarianceMatrix]
    symm
    calc
      (∑' n : ℕ, sigmaLayer n) row col =
          (∑' n : ℕ, sigmaLayer n row) col := by
        exact congrFun (tsum_apply (x := row) hsigmaSum) col
      _ = ∑' n : ℕ, sigmaLayer n row col :=
        tsum_apply ((Pi.summable.mp hsigmaSum) row)
  have honeMatrix :
      cmp116SourcePi4FullComplexWeakenedCovarianceMatrix
          (R := R) anchor K hc hmass hK (fun _ => 1) =
        ∑' n : ℕ, oneLayer n := by
    funext row col
    rw [cmp116SourcePi4FullComplexWeakenedCovarianceMatrix]
    symm
    calc
      (∑' n : ℕ, oneLayer n) row col =
          (∑' n : ℕ, oneLayer n row) col := by
        exact congrFun (tsum_apply (x := row) honeSum) col
      _ = ∑' n : ℕ, oneLayer n row col :=
        tsum_apply ((Pi.summable.mp honeSum) row)
  rw [hsigmaMatrix, honeMatrix]
  apply physicalWalkMatrix_linfty_opNorm_le_of_fixedRate
  · unfold cmp116SourcePi4ComplexContourPrefactor
    positivity
  · exact hgeom
  · intro row col
    let sigmaEntry := fun n : ℕ => sigmaLayer n row col
    let oneEntry := fun n : ℕ => oneLayer n row col
    let diffEntry := fun n : ℕ => sigmaEntry n - oneEntry n
    have hsigmaEntry : Summable sigmaEntry := by
      exact
        (Pi.summable.mp
          (Pi.summable.mp hsigmaSum row) col)
    have honeEntry : Summable oneEntry := by
      exact
        (Pi.summable.mp
          (Pi.summable.mp honeSum row) col)
    have hdiffEntry : Summable diffEntry := by
      exact hsigmaEntry.sub honeEntry
    have hsigmaApply :
        (∑' n : ℕ, sigmaLayer n) row col =
          ∑' n : ℕ, sigmaEntry n := by
      calc
        (∑' n : ℕ, sigmaLayer n) row col =
            (∑' n : ℕ, sigmaLayer n row) col := by
          exact congrFun (tsum_apply (x := row) hsigmaSum) col
        _ = ∑' n : ℕ, sigmaLayer n row col :=
          tsum_apply ((Pi.summable.mp hsigmaSum) row)
        _ = ∑' n : ℕ, sigmaEntry n := rfl
    have honeApply :
        (∑' n : ℕ, oneLayer n) row col =
          ∑' n : ℕ, oneEntry n := by
      calc
        (∑' n : ℕ, oneLayer n) row col =
            (∑' n : ℕ, oneLayer n row) col := by
          exact congrFun (tsum_apply (x := row) honeSum) col
        _ = ∑' n : ℕ, oneLayer n row col :=
          tsum_apply ((Pi.summable.mp honeSum) row)
        _ = ∑' n : ℕ, oneEntry n := rfl
    have htsumSub :
        (∑' n : ℕ, diffEntry n) =
          (∑' n : ℕ, sigmaEntry n) - ∑' n : ℕ, oneEntry n :=
      hsigmaEntry.tsum_sub honeEntry
    have hmajorHasSum :
        HasSum
          (fun n : ℕ =>
            cmp116SourcePi4ComplexDefectLayerAmplitude
              Δ Ahead rho radius Rweak n *
              Real.exp (-(rate *
                (physicalBondDist row.1 col.1 : ℝ))))
          ((cmp116SourcePi4ComplexContourPrefactor Ahead radius Rweak *
            (1 - cmp116SourcePi4ComplexContourRatio Δ rho Rweak)⁻¹ ^ 2) *
            Real.exp (-(rate *
              (physicalBondDist row.1 col.1 : ℝ)))) :=
      (hasSum_cmp116SourcePi4ComplexDefectLayerAmplitude
        Δ Ahead rho radius Rweak hsmall).mul_right
          (Real.exp (-(rate *
            (physicalBondDist row.1 col.1 : ℝ))))
    rw [Matrix.sub_apply, hsigmaApply, honeApply, ← htsumSub]
    calc
      ‖∑' n : ℕ, diffEntry n‖ ≤ ∑' n : ℕ, ‖diffEntry n‖ :=
        norm_tsum_le_tsum_norm hdiffEntry.norm
      _ ≤ ∑' n : ℕ,
          cmp116SourcePi4ComplexDefectLayerAmplitude
            Δ Ahead rho radius Rweak n *
            Real.exp (-(rate *
              (physicalBondDist row.1 col.1 : ℝ))) := by
        exact Summable.tsum_le_tsum
          (fun n =>
            norm_cmp116SourcePi4FullComplexWeakenedCovarianceLayer_sub_one_apply_le'
              anchor K hc hmass hK hAhead hrho hrate Cert htri hrange
              hΔ hΔ1 sigma hradius hRweak hdiff hcap n row col)
          hdiffEntry.norm hmajorHasSum.summable
      _ = (cmp116SourcePi4ComplexContourPrefactor Ahead radius Rweak *
            (1 - cmp116SourcePi4ComplexContourRatio Δ rho Rweak)⁻¹ ^ 2) *
            Real.exp (-(rate *
              (physicalBondDist row.1 col.1 : ℝ))) :=
        hmajorHasSum.tsum_eq

end

end YangMills.RG
