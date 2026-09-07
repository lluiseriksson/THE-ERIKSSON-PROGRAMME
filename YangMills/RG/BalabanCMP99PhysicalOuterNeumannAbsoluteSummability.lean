/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99PhysicalFineHeadTailAbsoluteSummability

/-!
# Absolute summability of the outer physical Neumann layers

The fixed-length word expansion is already absolutely summable.  This
module closes the remaining outer length sum directly from the literal
coarse relative defect.  The argument keeps its geometric ratio visible
and then transports the bound through the two-sided matrix map and the
real-linear physical reconstruction.
-/

namespace YangMills.RG

noncomputable section

open scoped Matrix.Norms.Operator

private abbrev FineField (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))] :=
  FinePhysicalOneCochain 4 M (2 * Q) Nc

set_option maxHeartbeats 2000000 in
/-- Physical outer Neumann layers are absolutely summable after
rectangular reconstruction.  No unconditional-to-absolute summability
conversion is used: the proof is the source relative-defect geometric
majorant. -/
theorem
    summable_norm_cmp99SourcePi4PhysicalBackgroundMinimizerNeumannLayers_of_source
    {M Q Nc R Δ : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (anchor : FinBox 4 Q)
    (K : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    (hsourceRange : R + 1 ≤ 4 * M)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    {coarseRate : ℝ} (hcoarseRate : 0 < coarseRate)
    (hcoarse : IsCoerciveCLM
      (cmp99SourcePi4WeakenedCoarseMiddle
        (R := R) anchor K hc hmass hK (fun _ => 1)) coarseRate)
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
    (hΔ : ∀ x, (cmp116CoarseFaceAdj 4 Q).degree x ≤ Δ)
    (hΔ1 : 1 ≤ Δ)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (hradius : 0 ≤ radius) (hRweak : 1 ≤ Rweak)
    (hdiff : ∀ d, ‖sigma d - 1‖ ≤ radius)
    (hcap : ∀ d, ‖sigma d‖ ≤ Rweak)
    (hcontourSmall :
      ‖cmp116SourcePi4ComplexContourRatio Δ rho Rweak‖ < 1)
    (hcoarseSmall :
      cmp99SourcePi4ComplexCoarseRelativeDefectBound
        (M := M) (Q := Q) (Nc := Nc)
        (cmp99SourcePi4WeakenedCoarseCovariance
          (R := R) anchor K hc hmass hK (fun _ => 1)
          hcoarseRate hcoarse)
        Δ Ahead rho rate radius Rweak < 1) :
    Summable fun neumannLength : ℕ =>
      ‖cmp99SourcePi4PhysicalBackgroundMinimizerNeumannLayer
        (R := R) anchor K hc hmass hK
        (cmp99SourcePi4WeakenedCoarseCovariance
          (R := R) anchor K hc hmass hK (fun _ => 1)
          hcoarseRate hcoarse)
        sigma neumannLength‖ := by
  let baseCoarseCovariance :=
    cmp99SourcePi4WeakenedCoarseCovariance
      (R := R) anchor K hc hmass hK (fun _ => 1)
      hcoarseRate hcoarse
  let baseInv :=
    cmp116PhysicalEndomorphismComplexMatrix baseCoarseCovariance
  let D :=
    cmp99SourcePi4FullComplexCoarseMiddleRelativeDefect
      (R := R) anchor K hc hmass hK baseCoarseCovariance sigma
  let left :=
    cmp116SourcePi4FullComplexWeakenedCovarianceMatrix
        (R := R) anchor K hc hmass hK sigma *
      cmp99SourcePi4ComplexBlockAdjointMatrix
        (M := M) (Q := Q) (Nc := Nc)
  let L := complexMatrixTwoSidedCLM left baseInv
  have hDsmall : ‖D‖ < 1 := by
    exact lt_of_le_of_lt
      (norm_cmp99SourcePi4FullComplexCoarseMiddleRelativeDefect_le_source
        anchor K hc hmass hK baseCoarseCovariance
        hAhead hrho hrate hgeom Cert htri hsourceRange hΔ hΔ1 sigma
        hradius hRweak hdiff hcap hcontourSmall)
      hcoarseSmall
  have hgeo : Summable fun n : ℕ => ‖D‖ ^ n :=
    summable_geometric_of_lt_one (norm_nonneg D) hDsmall
  have hpowNorm (n : ℕ) : ‖(-D) ^ n‖ ≤ ‖D‖ ^ n := by
    induction n with
    | zero => simp
    | succ n ih =>
        have hmul :
            ‖(-D) ^ n * (-D)‖ ≤ ‖D‖ ^ n * ‖D‖ := by
          calc
            ‖(-D) ^ n * (-D)‖ ≤ ‖(-D) ^ n‖ * ‖-D‖ :=
              Matrix.linfty_opNorm_mul _ _
            _ ≤ ‖D‖ ^ n * ‖-D‖ :=
              mul_le_mul_of_nonneg_right ih (norm_nonneg _)
            _ = ‖D‖ ^ n * ‖D‖ := by rw [norm_neg]
        simpa only [pow_succ] using hmul
  have hmappedNorm : Summable fun n : ℕ => ‖L ((-D) ^ n)‖ := by
    apply
      (hgeo.mul_left (ContinuousLinearMap.opNorm L)).of_nonneg_of_le
        (fun _ => norm_nonneg _)
    intro n
    calc
      ‖L ((-D) ^ n)‖ ≤
          ContinuousLinearMap.opNorm L * ‖(-D) ^ n‖ :=
        L.le_opNorm ((-D) ^ n)
      _ ≤ ContinuousLinearMap.opNorm L * ‖D‖ ^ n :=
        mul_le_mul_of_nonneg_left (hpowNorm n) L.opNorm_nonneg
  have hlayer (n : ℕ) :
      cmp99SourcePi4ComplexBackgroundMinimizerNeumannLayer
          (R := R) anchor K hc hmass hK
          baseCoarseCovariance sigma n =
        L ((-D) ^ n) := by
    simp [cmp99SourcePi4ComplexBackgroundMinimizerNeumannLayer,
      baseCoarseCovariance, baseInv, D, left, L,
      complexMatrixTwoSidedCLM_apply, Matrix.mul_assoc]
  have hcomplex :
      Summable fun n : ℕ =>
        ‖cmp99SourcePi4ComplexBackgroundMinimizerNeumannLayer
          (R := R) anchor K hc hmass hK
          baseCoarseCovariance sigma n‖ :=
    hmappedNorm.congr fun n => by rw [hlayer n]
  apply summable_norm_cmp99PhysicalRectangularOfComplexMatrix
  simpa [baseCoarseCovariance] using hcomplex

end

end YangMills.RG
