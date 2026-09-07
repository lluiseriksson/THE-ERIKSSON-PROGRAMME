/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80SourcePi4CarrierAnchoredPotentialDerivative
import YangMills.RG.BalabanCMP116PhysicalEndomorphismSchurNorm

/-!
# Operator norm of one carrier-anchored equation-(80) domain coefficient

The completed carrier-anchored coefficient already has an entrywise
exponential kernel bound uniform in the ambient volume.  This file sums that
kernel in both matrix directions and applies the exact physical coordinate
isometry plus the bilateral Schur estimate.  The result controls the genuine
physical `L²` operator reconstructed from one source domain.
-/

namespace YangMills.RG

open scoped Matrix.Norms.Operator

noncomputable section

private abbrev PhysicalEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc →L[ℝ]
    PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

/-- The literal completed domain operator is bounded uniformly in the
ambient volume by its summed physical exponential kernel.  The displayed
ratio retains the actual branching and continuation parameters. -/
theorem norm_cmp102Eq80SourcePi4CarrierAnchoredDomainOperator_le
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
    (s : FinBox 4 (2 * Q) → ℝ)
    (hRweak : 1 ≤ Rweak)
    (hcap : ∀ d, ‖(s d : ℂ)‖ ≤ Rweak)
    (S : Finset (FinBox 4 (2 * Q)))
    (Y : Finset (FinBox 4 (2 * Q)))
    (hsmall :
      ‖cmp116SourcePi4ComplexContourRatio Δ rho Rweak‖ < 1) :
    ‖cmp102Eq80SourcePi4CarrierAnchoredDomainOperator
        (R := R) anchor K hc hmass hK s S Y‖ ≤
      (cmp116SourcePi4MixedDerivativeDomainPrefactor Ahead Rweak *
        (1 - cmp116SourcePi4ComplexContourRatio Δ rho Rweak)⁻¹) *
        (((Nc ^ 2 - 1 : ℕ) : ℝ) *
          cmp99PhysicalBondGeometricRowSum 4 rate) := by
  let amplitude :=
    cmp116SourcePi4MixedDerivativeDomainPrefactor Ahead Rweak *
      (1 - cmp116SourcePi4ComplexContourRatio Δ rho Rweak)⁻¹
  let matrix :=
    cmp102Eq80SourcePi4CarrierAnchoredDomainMatrix
      (R := R) anchor K hc hmass hK s S Y
  have hRweak0 : 0 ≤ Rweak := le_trans (by norm_num) hRweak
  have hprefactor :
      0 ≤ cmp116SourcePi4MixedDerivativeDomainPrefactor Ahead Rweak := by
    unfold cmp116SourcePi4MixedDerivativeDomainPrefactor
    positivity
  have hratio0 :
      0 ≤ cmp116SourcePi4ComplexContourRatio Δ rho Rweak := by
    unfold cmp116SourcePi4ComplexContourRatio
    positivity
  have hratio_lt :
      cmp116SourcePi4ComplexContourRatio Δ rho Rweak < 1 := by
    exact lt_of_le_of_lt
      (le_trans (le_abs_self _)
        (by simp [Real.norm_eq_abs]))
      hsmall
  have hamplitude : 0 ≤ amplitude := by
    exact mul_nonneg hprefactor
      (inv_nonneg.mpr (sub_nonneg.mpr hratio_lt.le))
  have hrow :
      ‖matrix‖ ≤
        amplitude *
          (((Nc ^ 2 - 1 : ℕ) : ℝ) *
            cmp99PhysicalBondGeometricRowSum 4 rate) := by
    apply physicalWalkMatrix_linfty_opNorm_le_of_fixedRate
      matrix amplitude rate hamplitude hgeom
    intro row col
    exact
      norm_cmp102Eq80SourcePi4CarrierAnchoredDomainCoefficient_le
        anchor K hc hmass hK hAhead hrho hrate Cert htri hrange hΔ hΔ1
        (fun x => (s x : ℂ)) hRweak hcap S Y row col hsmall
  have hcol :
      ‖matrix.transpose‖ ≤
        amplitude *
          (((Nc ^ 2 - 1 : ℕ) : ℝ) *
            cmp99PhysicalBondGeometricRowSum 4 rate) := by
    apply physicalWalkMatrix_linfty_opNorm_le_of_fixedRate
      matrix.transpose amplitude rate hamplitude hgeom
    intro row col
    simpa [matrix, Matrix.transpose_apply, physicalBondDist_comm] using
      (norm_cmp102Eq80SourcePi4CarrierAnchoredDomainCoefficient_le
        anchor K hc hmass hK hAhead hrho hrate Cert htri hrange hΔ hΔ1
        (fun x => (s x : ℂ)) hRweak hcap S Y col row hsmall)
  change
    ‖cmp116PhysicalEndomorphismOfComplexMatrixCLM matrix‖ ≤ _
  exact
    norm_cmp116PhysicalEndomorphismOfComplexMatrixCLM_le_of_bilateral
      matrix
      (amplitude *
        (((Nc ^ 2 - 1 : ℕ) : ℝ) *
          cmp99PhysicalBondGeometricRowSum 4 rate))
      (mul_nonneg hamplitude
        (mul_nonneg (Nat.cast_nonneg _)
          (cmp99PhysicalBondGeometricRowSum_nonneg hgeom)))
      hrow hcol

end

end YangMills.RG
