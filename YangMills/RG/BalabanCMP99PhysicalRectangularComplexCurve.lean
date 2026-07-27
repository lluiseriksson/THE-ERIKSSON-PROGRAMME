/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99ComplexRectangularMinimizerDerivative
import YangMills.RG.BalabanCMP99PhysicalRectangularMatrixReconstruction

/-!
# Real physical curves reconstructed from rectangular complex matrices

The contour construction is holomorphic entrywise, while CMP102 equation
(80) consumes a real continuous linear map.  This module restricts a
rectangular complex matrix curve to the real axis, takes entrywise real
parts, and reconstructs its exact physical derivative.
-/

namespace YangMills.RG

noncomputable section

/-- Entrywise complex derivatives reconstruct after restriction to the real
axis to the derivative of the real physical rectangular map. -/
theorem
    hasDerivAt_cmp99PhysicalRectangularOfComplexMatrix_compOfReal
    {d N₁ N₂ Nc : ℕ}
    [NeZero d] [NeZero N₁] [NeZero N₂] [NeZero (Nc ^ 2 - 1)]
    (A : ℂ → Matrix (CMP116PhysicalWalkCoordinate d N₂ Nc)
      (CMP116PhysicalWalkCoordinate d N₁ Nc) ℂ)
    (A' : Matrix (CMP116PhysicalWalkCoordinate d N₂ Nc)
      (CMP116PhysicalWalkCoordinate d N₁ Nc) ℂ)
    (t : ℝ)
    (hentry : ∀ i j,
      HasDerivAt (fun z => A z i j) (A' i j) (t : ℂ)) :
    HasDerivAt
      (fun u : ℝ =>
        cmp99PhysicalRectangularOfComplexMatrix (A (u : ℂ)))
      (cmp99PhysicalRectangularOfComplexMatrix A') t := by
  apply hasDerivAt_cmp99PhysicalRectangularOfComplexMatrix_of_entrywise
  intro i j
  have hcomplex := (hentry i j).comp_ofReal
  simpa [Function.comp_def, Complex.reCLM_apply] using
    ((Complex.reCLM : ℂ →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt
      t hcomplex)

private abbrev FineField (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))] :=
  FinePhysicalOneCochain 4 M (2 * Q) Nc

private abbrev CoarseField (Q Nc : ℕ) [NeZero (2 * Q)] :=
  CoarsePhysicalOneCochain 4 (2 * Q) Nc

/-- Real physical rectangular minimizer curve obtained from the complete
complex source contour. -/
noncomputable def cmp99SourcePi4RealBackgroundMinimizerOperatorCurve
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (anchor : FinBox 4 Q)
    (K : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (d : FinBox 4 (2 * Q))
    (u : ℝ) : CoarseField Q Nc →L[ℝ] FineField M Q Nc :=
  cmp99PhysicalRectangularOfComplexMatrix
    (cmp99SourcePi4FullComplexBackgroundMinimizerMatrix
      (R := R) anchor K hc hmass hK
      (Function.update sigma d (u : ℂ)))

/-- Reconstructed physical derivative of the source minimizer curve. -/
noncomputable def
    cmp99SourcePi4RealBackgroundMinimizerOperatorDerivative
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (anchor : FinBox 4 Q)
    (K : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (d : FinBox 4 (2 * Q))
    (t : ℝ) : CoarseField Q Nc →L[ℝ] FineField M Q Nc :=
  cmp99PhysicalRectangularOfComplexMatrix
    (cmp99SourcePi4FullComplexBackgroundMinimizerMatrixDerivative
      (R := R) anchor K hc hmass hK sigma d (t : ℂ))

set_option maxHeartbeats 4000000 in
/-- The full source contour estimates generate the derivative of the real
physical rectangular minimizer. -/
theorem
    hasDerivAt_cmp99SourcePi4RealBackgroundMinimizerOperatorCurve_of_source
    {M Q Nc R Δ : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (anchor : FinBox 4 Q)
    (K : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    (hsourceRange : R + 1 ≤ 4 * M)
    (hfiniteRange : PhysicalCovarianceFiniteRange
      K physicalBondDist R)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (hD :
      ‖cmp99PatchedPhysicalParametrixDefect
          (cmp99SourcePi4Charts :
            Finset (CMP99SourcePi4Chart Unit Q))
          K cmp99SourcePi4ChartEnlarged
          (cmp99SourcePi4ChartCore (M := M))
          hc hmass hK‖ < 1)
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
    (d : FinBox 4 (2 * Q))
    (hradius : 0 ≤ radius) (hRweak : 1 ≤ Rweak)
    (hsigma : ∀ x, ‖sigma x - 1‖ ≤ (1 : ℝ))
    (hcap : ∀ x, ‖sigma x‖ ≤ Rweak)
    (t : ℝ)
    (hdiffUpdate :
      ∀ x, ‖Function.update sigma d (t : ℂ) x - 1‖ ≤ radius)
    (hcapUpdate :
      ∀ x, ‖Function.update sigma d (t : ℂ) x‖ ≤ Rweak)
    (hcontourSmall :
      ‖cmp116SourcePi4ComplexContourRatio Δ rho Rweak‖ < 1)
    (hcoarseSmall :
      cmp99SourcePi4ComplexCoarseRelativeDefectBound
        (M := M) (Q := Q) (Nc := Nc)
        (cmp99SourcePi4WeakenedCoarseCovariance
          (R := R) anchor K hc hmass hK (fun _ => 1)
          hcoarseRate hcoarse)
        Δ Ahead rho rate radius Rweak < 1) :
    HasDerivAt
      (cmp99SourcePi4RealBackgroundMinimizerOperatorCurve
        (R := R) anchor K hc hmass hK sigma d)
      (cmp99SourcePi4RealBackgroundMinimizerOperatorDerivative
        (R := R) anchor K hc hmass hK sigma d t) t := by
  apply
    hasDerivAt_cmp99PhysicalRectangularOfComplexMatrix_compOfReal
      (d := 4) (N₁ := 2 * Q) (N₂ := M * (2 * Q)) (Nc := Nc)
      (A := fun z =>
        cmp99SourcePi4FullComplexBackgroundMinimizerMatrix
          (R := R) anchor K hc hmass hK
          (Function.update sigma d z))
      (A' :=
        cmp99SourcePi4FullComplexBackgroundMinimizerMatrixDerivative
          (R := R) anchor K hc hmass hK sigma d (t : ℂ))
      (t := t)
  intro row col
  exact
    hasDerivAt_cmp99SourcePi4FullComplexBackgroundMinimizerMatrix_update_of_source
      anchor K hsourceRange hfiniteRange hc hmass hK hD
      hcoarseRate hcoarse hAhead hrho hrate hgeom Cert htri hΔ hΔ1
      sigma d hradius hRweak hsigma hcap (t : ℂ)
      hdiffUpdate hcapUpdate hcontourSmall hcoarseSmall row col

end

end YangMills.RG
