/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116SourcePi4FullComplexR2PhysicalBound
import YangMills.RG.BalabanCMP116SourcePi4FullComplexR2TransposePhysicalBound

/-!
# Bilateral physical bound for the source-complex `R2`

The real quadratic estimate uses the average of the row norm of `R2` and
the row norm of its transpose.  This module combines the two independently
constructed physical Neumann bounds.  No matrix-valued `R2` estimate remains
as an input.
-/

namespace YangMills.RG

noncomputable section

open scoped Matrix.Norms.Operator

private abbrev PhysicalEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc →L[ℝ]
    PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

/-- The explicit bilateral source-complex `R2` budget. -/
noncomputable def cmp116SourcePi4PhysicalComplexR2BilateralBound
    {M Q Nc : ℕ} [NeZero M] [NeZero Q]
    (K : PhysicalEndomorphism M Q Nc)
    (Delta : ℕ) (Ahead rho rate radius Rweak : ℝ) : ℝ :=
  (cmp116SourcePi4PhysicalComplexR2RowBound
      K Delta Ahead rho rate radius Rweak +
    cmp116SourcePi4PhysicalComplexR2ColumnBound
      K Delta Ahead rho rate radius Rweak) / 2

set_option maxHeartbeats 12000000 in
/-- The literal source-complex `R2` and its transpose satisfy the explicit
bilateral physical budget. -/
theorem
    bilateral_cmp116SourcePi4FullComplexR2Matrix_le_physical
    {M Q Nc R Delta : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
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
    (‖cmp116SourcePi4FullComplexR2Matrix
          (R := R) anchor K hc hmass hK sigma‖ +
        ‖(cmp116SourcePi4FullComplexR2Matrix
          (R := R) anchor K hc hmass hK sigma).transpose‖) / 2 ≤
      cmp116SourcePi4PhysicalComplexR2BilateralBound
        K Delta Ahead rho rate radius Rweak := by
  apply div_le_div_of_nonneg_right _ (by norm_num : (0 : ℝ) ≤ 2)
  exact add_le_add
    (linfty_opNorm_cmp116SourcePi4FullComplexR2Matrix_le_physical
      anchor K hsourceRange hfiniteRange hc hmass hK hD
      hAhead hrho hrate hgeom Cert htri hDelta hDelta1 sigma
      hradius hRweak hdiff hcap hseries hneumann)
    (linfty_opNorm_transpose_cmp116SourcePi4FullComplexR2Matrix_le_physical
      anchor K hsourceRange hfiniteRange hc hmass hK hD
      hAhead hrho hrate hgeom Cert htri hDelta hDelta1 sigma
      hradius hRweak hdiff hcap hseries hneumannTranspose)

end

end YangMills.RG
