/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116ComplexR1DefectBudget
import YangMills.RG.BalabanCMP116SourcePi4FullComplexR3BilateralNorm

/-!
# Physical bilateral defect budget for the source-complex `R1`

The exact `R1` telescope is bounded here using the literal fully coupled
Gamma/covariance, the physical `R3` bounds, and the source contour covariance
defect.  The base norms remain the norms of their literal source matrices;
no caller-supplied `R1`, `R2`, `R3`, Gamma, or covariance estimate occurs.
-/

namespace YangMills.RG

noncomputable section

open scoped Matrix.Norms.Operator

private abbrev PhysicalEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc →L[ℝ]
    PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

/-- Explicit source-specific `R1` defect budget.  The base factors are literal
physical matrices and both contour defects use the volume-uniform source
budgets proved upstream. -/
noncomputable def cmp116SourcePi4PhysicalComplexR1DefectBilateralBudget
    {M Q Nc : ℕ}
    [NeZero M] [NeZero Q] [NeZero Nc] [NeZero (Nc ^ 2 - 1)]
    (K root : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (Z0 : Finset (FinBox 4 (2 * Q)))
    (Delta : ℕ) (Ahead rho rate radius Rweak : ℝ) : ℝ :=
  let G0 := cmp116SourcePi4PhysicalBaseGammaMatrix K root Z0
  let C0 := cmp116SourcePi4PhysicalBaseCovarianceMatrix K hc hmass hK
  let R3row :=
    cmp116SourcePi4PhysicalComplexR3RowBound
      K root Z0 Delta Ahead rho rate radius Rweak
  let R3column :=
    cmp116SourcePi4PhysicalComplexR3ColumnBound
      K root Z0 Delta Ahead rho rate radius Rweak
  let covarianceDefect :=
    cmp116SourcePi4PhysicalComplexContourDefectBound
      Nc Delta Ahead rho rate radius Rweak
  cmp116R1TelescopeDefectBilateralBudget
    ‖G0‖ ‖G0.transpose‖ ‖C0‖ ‖C0.transpose‖
    R3row R3column covarianceDefect covarianceDefect

/-- The exact source `R1` telescope is controlled by a fully physical
bilateral defect budget.  In particular, no `hr1`, `hR2`, `hR3`, or abstract
covariance-defect norm is exposed. -/
theorem cmp116SourcePi4FullComplexR1TelescopeSchurBudget_le_physicalDefect
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
    cmp116SourcePi4FullComplexR1TelescopeSchurBudget
        (R := R) anchor K root hc hmass hK Z0 sigma ≤
      cmp116SourcePi4PhysicalComplexR1DefectBilateralBudget
        K root hc hmass hK Z0 Delta Ahead rho rate radius Rweak := by
  let G0 := cmp116SourcePi4PhysicalBaseGammaMatrix K root Z0
  let G1 := cmp116SourcePi4FullComplexGammaMatrix
    (R := R) anchor K root hc hmass hK Z0 sigma
  let C0 := cmp116SourcePi4PhysicalBaseCovarianceMatrix K hc hmass hK
  let C1 := cmp116SourcePi4FullComplexWeakenedCovarianceMatrix
    (R := R) anchor K hc hmass hK sigma
  let R3row :=
    cmp116SourcePi4PhysicalComplexR3RowBound
      K root Z0 Delta Ahead rho rate radius Rweak
  let R3column :=
    cmp116SourcePi4PhysicalComplexR3ColumnBound
      K root Z0 Delta Ahead rho rate radius Rweak
  let covarianceDefect :=
    cmp116SourcePi4PhysicalComplexContourDefectBound
      Nc Delta Ahead rho rate radius Rweak
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
  have hC0 :
      cmp116SourcePi4FullComplexWeakenedCovarianceMatrix
          (R := R) anchor K hc hmass hK (fun _ => 1) = C0 := by
    simpa [C0, cmp116SourcePi4PhysicalBaseCovarianceMatrix] using
      (cmp116SourcePi4FullComplexWeakenedCovarianceMatrix_one_eq_exact
        anchor K hsourceRange hfiniteRange hc hmass hK hD)
  have hCovarianceRow : ‖C1 - C0‖ ≤ covarianceDefect := by
    change ‖cmp116SourcePi4FullComplexWeakenedCovarianceMatrix
        (R := R) anchor K hc hmass hK sigma - C0‖ ≤ covarianceDefect
    rw [← hC0]
    simpa [covarianceDefect,
      cmp116SourcePi4PhysicalComplexContourDefectBound] using
      (linfty_opNorm_cmp116SourcePi4FullComplexWeakenedCovarianceMatrix_sub_one_le
        anchor K hc hmass hK hAhead hrho hrate hgeom Cert htri
        hsourceRange hDelta hDelta1 sigma hradius hRweak hdiff hcap hseries)
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
  change cmp116R1TelescopeBilateralSchurBudget G0 G1 C0 C1 ≤ _
  change cmp116R1TelescopeBilateralSchurBudget G0 G1 C0 C1 ≤
    cmp116R1TelescopeDefectBilateralBudget
      ‖G0‖ ‖G0.transpose‖ ‖C0‖ ‖C0.transpose‖
      R3row R3column covarianceDefect covarianceDefect
  exact cmp116R1TelescopeBilateralSchurBudget_le_defectBudget
    G0 G1 C0 C1 (le_refl _) (le_refl _) (le_refl _) (le_refl _)
    hR3row hR3column hCovarianceRow hCovarianceColumn

end

end YangMills.RG
