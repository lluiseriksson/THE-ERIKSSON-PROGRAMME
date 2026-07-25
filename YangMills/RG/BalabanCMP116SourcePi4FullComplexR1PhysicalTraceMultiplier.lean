/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116SourcePi4FullComplexR1PhysicalDefectBudget
import YangMills.RG.BalabanCMP116SourceRestrictedUniformR1TraceBound

/-!
# Physical uniform multiplier for the source `R1` trace telescope

The coordinate-pivot trace theorem previously received a bound for the
complete `R1` telescope multiplier.  Here that bound is generated from the
literal base matrices and the physical `R2`, `R3`, and covariance-defect
budgets.  Thus the source-facing trace estimate no longer needs an abstract
`hmultiplier`.
-/

namespace YangMills.RG

noncomputable section

open scoped Matrix.Norms.Operator

private abbrev PhysicalEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc →L[ℝ]
    PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

private theorem r1TraceMultiplierBudget_le_of_bounds
    {ι : Type*} [Fintype ι]
    (G0 G1 C0 C1 U V : Matrix ι ι ℂ)
    {g1Row g1Column c1Column uBound : ℝ}
    (hG1row : ‖G1‖ ≤ g1Row)
    (hG1column : ‖G1.transpose‖ ≤ g1Column)
    (hC1column : ‖C1.transpose‖ ≤ c1Column)
    (hU : ‖U‖ ≤ uBound) :
    Matrix.r1TraceMultiplierBudget G0 G1 C0 C1 U V ≤
      ‖V‖ * g1Column * c1Column * uBound +
        g1Row * ‖G0.transpose‖ +
        ‖V‖ * ‖G0.transpose‖ * ‖C0‖ * uBound := by
  have hg1Column0 : 0 ≤ g1Column :=
    (norm_nonneg G1.transpose).trans hG1column
  have hc1Column0 : 0 ≤ c1Column :=
    (norm_nonneg C1.transpose).trans hC1column
  unfold Matrix.r1TraceMultiplierBudget
  gcongr

/-- Explicit uniform bound for the exact source `R1` trace multiplier. -/
noncomputable def cmp116SourcePi4PhysicalComplexR1TraceMultiplierBound
    {M Q Nc : ℕ}
    [NeZero M] [NeZero Q] [NeZero Nc] [NeZero (Nc ^ 2 - 1)]
    (K root : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (Z0 : Finset (FinBox 4 (2 * Q)))
    (Delta : ℕ) (Ahead rho rate radius Rweak : ℝ) : ℝ :=
  let G0 := cmp116SourcePi4PhysicalBaseGammaMatrix K root Z0
  let C0 := cmp116SourcePi4PhysicalBaseCovarianceMatrix K hc hmass hK
  let P0 := cmp116PhysicalEndomorphismComplexMatrix K
  let constraint := cmp116SourcePi4ConstraintMatrix M Q Nc
  let complement :=
    cmp116SourcePi4ComplementProjectionMatrix (M := M) (Nc := Nc) Z0
  let rootMatrix := cmp116SourcePi4ReferenceRootMatrix root
  let V := P0 * (constraint * complement) * rootMatrix
  let R2row :=
    cmp116SourcePi4PhysicalComplexR2RowBound
      K Delta Ahead rho rate radius Rweak
  let R3row :=
    cmp116SourcePi4PhysicalComplexR3RowBound
      K root Z0 Delta Ahead rho rate radius Rweak
  let R3column :=
    cmp116SourcePi4PhysicalComplexR3ColumnBound
      K root Z0 Delta Ahead rho rate radius Rweak
  let covarianceDefect :=
    cmp116SourcePi4PhysicalComplexContourDefectBound
      Nc Delta Ahead rho rate radius Rweak
  let Ubound := ‖constraint.transpose‖ * (‖P0‖ + R2row)
  ‖V‖ * (‖G0.transpose‖ + R3column) *
      (‖C0.transpose‖ + covarianceDefect) * Ubound +
    (‖G0‖ + R3row) * ‖G0.transpose‖ +
    ‖V‖ * ‖G0.transpose‖ * ‖C0‖ * Ubound

/-- The exact source trace multiplier is bounded by the explicit physical
budget above.  The caller supplies only the physical contour certificate and
the two scalar Neumann conditions. -/
theorem cmp116SourcePi4FullComplexR1TraceMultiplierBudget_le_physical
    {M Q Nc R Delta : ℕ}
    [NeZero M] [NeZero Q] [NeZero Nc] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K root : PhysicalEndomorphism M Q Nc)
    (hsourceRange : R + 1 ≤ 4 * M)
    (hfiniteRange : PhysicalCovarianceFiniteRange K physicalBondDist R)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (hD :
      ‖cmp99PatchedPhysicalParametrixDefect
          (cmp99SourcePi4Charts :
            Finset (CMP99SourcePi4Chart Unit Q))
          K cmp99SourcePi4ChartEnlarged
          (cmp99SourcePi4ChartCore (M := M))
          hc hmass hK‖ < 1)
    (Z0 : Finset (FinBox 4 (2 * Q)))
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
    (hDelta : ∀ x, (cmp116CoarseFaceAdj 4 Q).degree x ≤ Delta)
    (hDelta1 : 1 ≤ Delta)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (hradius : 0 ≤ radius) (hRweak : 1 ≤ Rweak)
    (hdiff : ∀ d, ‖sigma d - 1‖ ≤ radius)
    (hcap : ∀ d, ‖sigma d‖ ≤ Rweak)
    (hseries :
      ‖cmp116SourcePi4ComplexContourRatio Delta rho Rweak‖ < 1)
    (hneumann :
      ‖cmp116PhysicalEndomorphismComplexMatrix K‖ *
        cmp116SourcePi4PhysicalComplexContourDefectBound
          Nc Delta Ahead rho rate radius Rweak < 1)
    (hneumannTranspose :
      cmp116SourcePi4PhysicalComplexTransposeRelativeDefectBound
        K Delta Ahead rho rate radius Rweak < 1) :
    let C0 := cmp116SourcePi4PhysicalBaseCovarianceMatrix K hc hmass hK
    let C1 := cmp116SourcePi4FullComplexWeakenedCovarianceMatrix
      (R := R) anchor K hc hmass hK sigma
    let P0 := cmp116PhysicalEndomorphismComplexMatrix K
    let P1 := cmp116SourcePi4FullComplexWeakenedPrecisionMatrix
      (R := R) anchor K hc hmass hK sigma
    let G0 := cmp116SourcePi4PhysicalBaseGammaMatrix K root Z0
    let G1 := cmp116SourcePi4FullComplexGammaMatrix
      (R := R) anchor K root hc hmass hK Z0 sigma
    let constraint := cmp116SourcePi4ConstraintMatrix M Q Nc
    let complement :=
      cmp116SourcePi4ComplementProjectionMatrix (M := M) (Nc := Nc) Z0
    let rootMatrix := cmp116SourcePi4ReferenceRootMatrix root
    let U := -(constraint.transpose * P1)
    let V := P0 * (constraint * complement) * rootMatrix
    Matrix.r1TraceMultiplierBudget G0 G1 C0 C1 U V ≤
      cmp116SourcePi4PhysicalComplexR1TraceMultiplierBound
        K root hc hmass hK Z0 Delta Ahead rho rate radius Rweak := by
  dsimp only
  let C0 := cmp116SourcePi4PhysicalBaseCovarianceMatrix K hc hmass hK
  let C1 := cmp116SourcePi4FullComplexWeakenedCovarianceMatrix
    (R := R) anchor K hc hmass hK sigma
  let P0 := cmp116PhysicalEndomorphismComplexMatrix K
  let P1 := cmp116SourcePi4FullComplexWeakenedPrecisionMatrix
    (R := R) anchor K hc hmass hK sigma
  let G0 := cmp116SourcePi4PhysicalBaseGammaMatrix K root Z0
  let G1 := cmp116SourcePi4FullComplexGammaMatrix
    (R := R) anchor K root hc hmass hK Z0 sigma
  let constraint := cmp116SourcePi4ConstraintMatrix M Q Nc
  let complement :=
    cmp116SourcePi4ComplementProjectionMatrix (M := M) (Nc := Nc) Z0
  let rootMatrix := cmp116SourcePi4ReferenceRootMatrix root
  let R2row :=
    cmp116SourcePi4PhysicalComplexR2RowBound
      K Delta Ahead rho rate radius Rweak
  let R3row :=
    cmp116SourcePi4PhysicalComplexR3RowBound
      K root Z0 Delta Ahead rho rate radius Rweak
  let R3column :=
    cmp116SourcePi4PhysicalComplexR3ColumnBound
      K root Z0 Delta Ahead rho rate radius Rweak
  let covarianceDefect :=
    cmp116SourcePi4PhysicalComplexContourDefectBound
      Nc Delta Ahead rho rate radius Rweak
  let U := -(constraint.transpose * P1)
  let V := P0 * (constraint * complement) * rootMatrix
  let Ubound := ‖constraint.transpose‖ * (‖P0‖ + R2row)
  have hR2row :
      ‖cmp116SourcePi4FullComplexR2Matrix
          (R := R) anchor K hc hmass hK sigma‖ ≤ R2row := by
    simpa [R2row] using
      (linfty_opNorm_cmp116SourcePi4FullComplexR2Matrix_le_physical
        anchor K hsourceRange hfiniteRange hc hmass hK hD
        hAhead hrho hrate hgeom Cert htri hDelta hDelta1 sigma
        hradius hRweak hdiff hcap hseries hneumann)
  have hP1 : ‖P1‖ ≤ ‖P0‖ + R2row := by
    calc
      ‖P1‖ =
          ‖P0 - cmp116SourcePi4FullComplexR2Matrix
            (R := R) anchor K hc hmass hK sigma‖ := by
        congr 1
        dsimp [P1, P0]
        unfold cmp116SourcePi4FullComplexR2Matrix
        abel
      _ ≤ ‖P0‖ +
          ‖cmp116SourcePi4FullComplexR2Matrix
            (R := R) anchor K hc hmass hK sigma‖ := norm_sub_le _ _
      _ ≤ ‖P0‖ + R2row := add_le_add (le_refl _) hR2row
  have hU : ‖U‖ ≤ Ubound := by
    dsimp [U, Ubound]
    rw [norm_neg]
    exact (Matrix.linfty_opNorm_mul _ _).trans
      (mul_le_mul_of_nonneg_left hP1 (norm_nonneg _))
  have hR3row : ‖G1 - G0‖ ≤ R3row := by
    simpa [G1, G0, R3row, cmp116SourcePi4FullComplexR3Matrix] using
      (linfty_opNorm_cmp116SourcePi4FullComplexR3Matrix_le_physical
        (R := R) anchor K root hsourceRange hfiniteRange hc hmass hK hD Z0
        hAhead hrho hrate hgeom Cert htri hDelta hDelta1 sigma
        hradius hRweak hdiff hcap hseries hneumann)
  have hR3column : ‖(G1 - G0).transpose‖ ≤ R3column := by
    simpa [G1, G0, R3column, cmp116SourcePi4FullComplexR3Matrix] using
      (linfty_opNorm_transpose_cmp116SourcePi4FullComplexR3Matrix_le_physical
        (R := R) anchor K root hsourceRange hfiniteRange hc hmass hK hD Z0
        hAhead hrho hrate hgeom Cert htri hDelta hDelta1 sigma
        hradius hRweak hdiff hcap hseries hneumannTranspose)
  have hG1row : ‖G1‖ ≤ ‖G0‖ + R3row := by
    calc
      ‖G1‖ = ‖G0 + (G1 - G0)‖ := by
        congr 1
        abel
      _ ≤ ‖G0‖ + ‖G1 - G0‖ := norm_add_le _ _
      _ ≤ ‖G0‖ + R3row := add_le_add (le_refl _) hR3row
  have hG1column : ‖G1.transpose‖ ≤ ‖G0.transpose‖ + R3column := by
    calc
      ‖G1.transpose‖ = ‖G0.transpose + (G1 - G0).transpose‖ := by
        congr 1
        ext i j
        simp
      _ ≤ ‖G0.transpose‖ + ‖(G1 - G0).transpose‖ := norm_add_le _ _
      _ ≤ ‖G0.transpose‖ + R3column :=
        add_le_add (le_refl _) hR3column
  have hC0 :
      cmp116SourcePi4FullComplexWeakenedCovarianceMatrix
          (R := R) anchor K hc hmass hK (fun _ => 1) = C0 := by
    simpa [C0, cmp116SourcePi4PhysicalBaseCovarianceMatrix] using
      (cmp116SourcePi4FullComplexWeakenedCovarianceMatrix_one_eq_exact
        anchor K hsourceRange hfiniteRange hc hmass hK hD)
  have hCovarianceColumn :
      ‖(C1 - C0).transpose‖ ≤ covarianceDefect := by
    change ‖(cmp116SourcePi4FullComplexWeakenedCovarianceMatrix
        (R := R) anchor K hc hmass hK sigma - C0).transpose‖ ≤
      covarianceDefect
    rw [← hC0]
    simpa [covarianceDefect,
      cmp116SourcePi4PhysicalComplexContourDefectBound] using
      (linfty_opNorm_transpose_cmp116SourcePi4FullComplexWeakenedCovarianceMatrix_sub_one_le
        anchor K hc hmass hK hAhead hrho hrate hgeom Cert htri
        hsourceRange hDelta hDelta1 sigma hradius hRweak hdiff hcap hseries)
  have hC1column :
      ‖C1.transpose‖ ≤ ‖C0.transpose‖ + covarianceDefect := by
    calc
      ‖C1.transpose‖ = ‖C0.transpose + (C1 - C0).transpose‖ := by
        congr 1
        ext i j
        simp
      _ ≤ ‖C0.transpose‖ + ‖(C1 - C0).transpose‖ := norm_add_le _ _
      _ ≤ ‖C0.transpose‖ + covarianceDefect :=
        add_le_add (le_refl _) hCovarianceColumn
  change Matrix.r1TraceMultiplierBudget G0 G1 C0 C1 U V ≤ _
  change Matrix.r1TraceMultiplierBudget G0 G1 C0 C1 U V ≤
    ‖V‖ * (‖G0.transpose‖ + R3column) *
        (‖C0.transpose‖ + covarianceDefect) * Ubound +
      (‖G0‖ + R3row) * ‖G0.transpose‖ +
      ‖V‖ * ‖G0.transpose‖ * ‖C0‖ * Ubound
  exact r1TraceMultiplierBudget_le_of_bounds
    G0 G1 C0 C1 U V hG1row hG1column hC1column hU

end

end YangMills.RG
