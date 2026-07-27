/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import Mathlib.Analysis.Complex.CauchyIntegral
import YangMills.RG.BalabanCMP99PhysicalRectangularComplexCurve

/-!
# Analytic FTC for the rectangular CMP99 minimizer

The weakened background minimizer is the rational matrix curve

`H(u) = C(u) Q* (Q C(u) Q*)⁻¹`.

This module isolates its genuine analytic domain: the open set on which the
literal coarse middle is nonsingular.  On that set every entry of `H` is
holomorphic and its canonical derivative is continuous.  This is the
regularity input needed for a source-faithful one-coordinate FTC; no
integrability premise for an opaque derivative is introduced.
-/

namespace YangMills.RG

noncomputable section

/-- The open nonsingular locus of the coarse middle of a rectangular
minimizer curve. -/
def cmp99ComplexBackgroundMinimizerNonsingularSet
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (C : ℂ → Matrix ι ι ℂ)
    (Q : Matrix κ ι ℂ) (Qstar : Matrix ι κ ℂ) : Set ℂ :=
  {u |
    (cmp99ComplexCoarseMiddleCurve C Q Qstar u).det ≠ 0}

/-- Entrywise entire covariance data make the nonsingular locus of the
literal coarse middle open. -/
theorem isOpen_cmp99ComplexBackgroundMinimizerNonsingularSet
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (C : ℂ → Matrix ι ι ℂ)
    (Q : Matrix κ ι ℂ) (Qstar : Matrix ι κ ℂ)
    (hC : ∀ t i j, DifferentiableAt ℂ (fun u => C u i j) t) :
    IsOpen (cmp99ComplexBackgroundMinimizerNonsingularSet C Q Qstar) := by
  let M := cmp99ComplexCoarseMiddleCurve C Q Qstar
  have hM : ∀ t i j, DifferentiableAt ℂ (fun u => M u i j) t := by
    intro t i j
    simp only [M, cmp99ComplexCoarseMiddleCurve, Matrix.mul_apply]
    apply DifferentiableAt.fun_sum
    intro k _hk
    apply DifferentiableAt.mul_const
    apply DifferentiableAt.fun_sum
    intro l _hl
    exact (hC t l k).const_mul (Q i l)
  have hdet : Continuous fun u => (M u).det := by
    rw [continuous_iff_continuousAt]
    intro t
    exact
      (differentiableAt_complexMatrixDet_of_entrywise
        M t (hM t)).continuousAt
  rw [show
    cmp99ComplexBackgroundMinimizerNonsingularSet C Q Qstar =
      (fun u => (M u).det) ⁻¹' ({0}ᶜ : Set ℂ) by
        ext u
        simp [cmp99ComplexBackgroundMinimizerNonsingularSet, M]]
  exact isOpen_compl_singleton.preimage hdet

/-- Every entry of the rectangular minimizer is holomorphic on the
nonsingular locus. -/
theorem differentiableOn_cmp99ComplexBackgroundMinimizerCurveEntry
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (C : ℂ → Matrix ι ι ℂ)
    (Q : Matrix κ ι ℂ) (Qstar : Matrix ι κ ℂ)
    (hC : ∀ t i j, DifferentiableAt ℂ (fun u => C u i j) t)
    (row : ι) (col : κ) :
    DifferentiableOn ℂ
      (fun u =>
        cmp99ComplexBackgroundMinimizerCurve
          C Q Qstar u row col)
      (cmp99ComplexBackgroundMinimizerNonsingularSet C Q Qstar) := by
  intro t ht
  exact
    (differentiableAt_cmp99ComplexBackgroundMinimizerCurveEntry
      C Q Qstar t (hC t)
      (by
        simpa [cmp99ComplexBackgroundMinimizerNonsingularSet] using ht)
      row col).differentiableWithinAt

/-- The canonical entry derivative of the rectangular minimizer is
continuous throughout its nonsingular locus. -/
theorem continuousOn_cmp99ComplexBackgroundMinimizerCurveDerivativeEntry
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (C : ℂ → Matrix ι ι ℂ)
    (Q : Matrix κ ι ℂ) (Qstar : Matrix ι κ ℂ)
    (hC : ∀ t i j, DifferentiableAt ℂ (fun u => C u i j) t)
    (row : ι) (col : κ) :
    ContinuousOn
      (fun u =>
        cmp99ComplexBackgroundMinimizerCurveDerivative
          C Q Qstar u row col)
      (cmp99ComplexBackgroundMinimizerNonsingularSet C Q Qstar) := by
  let U := cmp99ComplexBackgroundMinimizerNonsingularSet C Q Qstar
  let f := fun u =>
    cmp99ComplexBackgroundMinimizerCurve C Q Qstar u row col
  have hU : IsOpen U :=
    isOpen_cmp99ComplexBackgroundMinimizerNonsingularSet C Q Qstar hC
  have hf : DifferentiableOn ℂ f U := by
    simpa [f, U] using
      differentiableOn_cmp99ComplexBackgroundMinimizerCurveEntry
        C Q Qstar hC row col
  have hana : AnalyticOnNhd ℂ f U := hf.analyticOnNhd hU
  simpa [cmp99ComplexBackgroundMinimizerCurveDerivative, f, U] using
    hana.deriv.continuousOn

/-- Entrywise continuity of a rectangular complex matrix curve reconstructs
to continuity of its real physical rectangular map. -/
theorem
    continuousOn_cmp99PhysicalRectangularOfComplexMatrix_of_entrywise
    {d N₁ N₂ Nc : ℕ}
    [NeZero d] [NeZero N₁] [NeZero N₂] [NeZero (Nc ^ 2 - 1)]
    {X : Type*} [TopologicalSpace X]
    (A : X → Matrix (CMP116PhysicalWalkCoordinate d N₂ Nc)
      (CMP116PhysicalWalkCoordinate d N₁ Nc) ℂ)
    (s : Set X)
    (hentry : ∀ i j, ContinuousOn (fun x => A x i j) s) :
    ContinuousOn
      (fun x => cmp99PhysicalRectangularOfComplexMatrix (A x)) s := by
  rw [show
    (fun x => cmp99PhysicalRectangularOfComplexMatrix (A x)) =
      fun x => ∑ i, ∑ j, (A x i j).re •
        cmp99PhysicalRectangularOfComplexMatrix
          (cmp99ComplexRectangularMatrixUnit i j) by
    funext x
    exact cmp99PhysicalRectangularOfComplexMatrix_eq_sum_units (A x)]
  apply continuousOn_finset_sum Finset.univ
  intro i _hi
  apply continuousOn_finset_sum Finset.univ
  intro j _hj
  exact
    (Complex.continuous_re.comp_continuousOn (hentry i j)).smul
      continuousOn_const

private abbrev FineField (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))] :=
  FinePhysicalOneCochain 4 M (2 * Q) Nc

private abbrev FineCoord (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))] :=
  CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc

private abbrev CoarseCoord (Q Nc : ℕ)
    [NeZero Q] [NeZero (2 * Q)] :=
  CMP116PhysicalWalkCoordinate 4 (2 * Q) Nc

theorem sourceUpdate_unitShifted
    {D : Type*} [DecidableEq D]
    (sigma : D → ℂ) (d : D)
    {radius t : ℝ}
    (hsigma : ∀ x, ‖sigma x - 1‖ ≤ (1 : ℝ))
    (hradius : 1 ≤ radius)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ∀ x, ‖Function.update sigma d (t : ℂ) x - 1‖ ≤ radius := by
  intro x
  by_cases hxd : x = d
  · subst x
    rw [Function.update_self]
    norm_cast
    rw [Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr ht.2)]
    exact (show -(t - 1) ≤ 1 by linarith [ht.1]).trans hradius
  · rw [Function.update_of_ne hxd]
    exact (hsigma x).trans hradius

theorem sourceUpdate_cap
    {D : Type*} [DecidableEq D]
    (sigma : D → ℂ) (d : D)
    {Rweak t : ℝ}
    (hRweak : 1 ≤ Rweak)
    (hcap : ∀ x, ‖sigma x‖ ≤ Rweak)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ∀ x, ‖Function.update sigma d (t : ℂ) x‖ ≤ Rweak := by
  intro x
  by_cases hxd : x = d
  · subst x
    rw [Function.update_self]
    norm_cast
    rw [Real.norm_eq_abs, abs_of_nonneg ht.1]
    exact ht.2.trans hRweak
  · rw [Function.update_of_ne hxd]
    exact hcap x

set_option maxHeartbeats 7000000 in
/-- Source contour bounds make the canonical derivative of every complex
rectangular-minimizer entry continuous on the complete real FTC segment.
The caller supplies neither a coarse determinant nor integrability. -/
theorem
    continuousOn_cmp99SourcePi4BackgroundMinimizerDerivative_compOfReal_of_source
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
    (hradius : 1 ≤ radius) (hRweak : 1 ≤ Rweak)
    (hsigma : ∀ x, ‖sigma x - 1‖ ≤ (1 : ℝ))
    (hcap : ∀ x, ‖sigma x‖ ≤ Rweak)
    (hcontourSmall :
      ‖cmp116SourcePi4ComplexContourRatio Δ rho Rweak‖ < 1)
    (hcoarseSmall :
      cmp99SourcePi4ComplexCoarseRelativeDefectBound
        (M := M) (Q := Q) (Nc := Nc)
        (cmp99SourcePi4WeakenedCoarseCovariance
          (R := R) anchor K hc hmass hK (fun _ => 1)
          hcoarseRate hcoarse)
        Δ Ahead rho rate radius Rweak < 1)
    (row : FineCoord M Q Nc) (col : CoarseCoord Q Nc) :
    ContinuousOn
      (fun t : ℝ =>
        cmp99SourcePi4FullComplexBackgroundMinimizerMatrixDerivative
          (R := R) anchor K hc hmass hK sigma d (t : ℂ) row col)
      (Set.Icc (0 : ℝ) 1) := by
  let Ccurve := fun u =>
    cmp116SourcePi4FullComplexWeakenedCovarianceMatrix
      (R := R) anchor K hc hmass hK
      (Function.update sigma d u)
  let Qmat :=
    cmp99SourcePi4ComplexBlockMatrix
      (M := M) (Q := Q) (Nc := Nc)
  let Qstar :=
    cmp99SourcePi4ComplexBlockAdjointMatrix
      (M := M) (Q := Q) (Nc := Nc)
  let U :=
    cmp99ComplexBackgroundMinimizerNonsingularSet Ccurve Qmat Qstar
  have hC : ∀ t i j,
      DifferentiableAt ℂ (fun u => Ccurve u i j) t := by
    intro t i j
    exact
      (hasDerivAt_cmp116SourcePi4FullComplexWeakenedCovarianceMatrix_update
        anchor K hc hmass hK hAhead hrho hrate hgeom Cert htri
        hsourceRange hΔ hΔ1 sigma d hRweak hsigma hcap
        hcontourSmall i j t).differentiableAt
  have hcontinuous :
      ContinuousOn
        (fun u =>
          cmp99ComplexBackgroundMinimizerCurveDerivative
            Ccurve Qmat Qstar u row col) U := by
    simpa [U] using
      continuousOn_cmp99ComplexBackgroundMinimizerCurveDerivativeEntry
        Ccurve Qmat Qstar hC row col
  have hmaps : Set.MapsTo (fun t : ℝ => (t : ℂ))
      (Set.Icc (0 : ℝ) 1) U := by
    intro t ht
    have hdet :=
      cmp99SourcePi4FullComplexCoarseMiddleMatrix_det_ne_zero_of_source
        anchor K hsourceRange hfiniteRange hc hmass hK hD
        hcoarseRate hcoarse hAhead hrho hrate hgeom Cert htri hΔ hΔ1
        (Function.update sigma d (t : ℂ))
        (show 0 ≤ radius by linarith) hRweak
        (sourceUpdate_unitShifted sigma d hsigma hradius ht)
        (sourceUpdate_cap sigma d hRweak hcap ht)
        hcontourSmall hcoarseSmall
    simpa [U, Ccurve, Qmat, Qstar,
      cmp99ComplexBackgroundMinimizerNonsingularSet,
      cmp99ComplexCoarseMiddleCurve,
      cmp99SourcePi4FullComplexCoarseMiddleMatrix] using hdet
  have hcomp :=
    hcontinuous.comp Complex.continuous_ofReal.continuousOn hmaps
  simpa [Ccurve, Qmat, Qstar,
    cmp99SourcePi4FullComplexBackgroundMinimizerMatrixDerivative] using hcomp

set_option maxHeartbeats 9000000 in
/-- One-coordinate FTC for every entry of the source-faithful rectangular
minimizer.  Analyticity on the nonsingular locus produces interval
integrability internally. -/
theorem
    integral_cmp99SourcePi4BackgroundMinimizerDerivative_eq_sub_of_source
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
    (hradius : 1 ≤ radius) (hRweak : 1 ≤ Rweak)
    (hsigma : ∀ x, ‖sigma x - 1‖ ≤ (1 : ℝ))
    (hcap : ∀ x, ‖sigma x‖ ≤ Rweak)
    (hcontourSmall :
      ‖cmp116SourcePi4ComplexContourRatio Δ rho Rweak‖ < 1)
    (hcoarseSmall :
      cmp99SourcePi4ComplexCoarseRelativeDefectBound
        (M := M) (Q := Q) (Nc := Nc)
        (cmp99SourcePi4WeakenedCoarseCovariance
          (R := R) anchor K hc hmass hK (fun _ => 1)
          hcoarseRate hcoarse)
        Δ Ahead rho rate radius Rweak < 1)
    (row : FineCoord M Q Nc) (col : CoarseCoord Q Nc) :
    (∫ t : ℝ in (0 : ℝ)..1,
        cmp99SourcePi4FullComplexBackgroundMinimizerMatrixDerivative
          (R := R) anchor K hc hmass hK sigma d (t : ℂ) row col) =
      cmp99SourcePi4FullComplexBackgroundMinimizerMatrix
          (R := R) anchor K hc hmass hK
          (Function.update sigma d (1 : ℂ)) row col -
        cmp99SourcePi4FullComplexBackgroundMinimizerMatrix
          (R := R) anchor K hc hmass hK
          (Function.update sigma d (0 : ℂ)) row col := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun t : ℝ =>
      cmp99SourcePi4FullComplexBackgroundMinimizerMatrix
        (R := R) anchor K hc hmass hK
        (Function.update sigma d (t : ℂ)) row col)
    (f' := fun t : ℝ =>
      cmp99SourcePi4FullComplexBackgroundMinimizerMatrixDerivative
        (R := R) anchor K hc hmass hK sigma d (t : ℂ) row col)
  · intro t ht
    have htIcc : t ∈ Set.Icc (0 : ℝ) 1 := by
      simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht
    exact
      (hasDerivAt_cmp99SourcePi4FullComplexBackgroundMinimizerMatrix_update_of_source
        anchor K hsourceRange hfiniteRange hc hmass hK hD
        hcoarseRate hcoarse hAhead hrho hrate hgeom Cert htri hΔ hΔ1
        sigma d (show 0 ≤ radius by linarith) hRweak hsigma hcap
        (t : ℂ)
        (sourceUpdate_unitShifted sigma d hsigma hradius htIcc)
        (sourceUpdate_cap sigma d hRweak hcap htIcc)
        hcontourSmall hcoarseSmall row col).comp_ofReal
  · have hcontinuous :=
      continuousOn_cmp99SourcePi4BackgroundMinimizerDerivative_compOfReal_of_source
        anchor K hsourceRange hfiniteRange hc hmass hK hD
        hcoarseRate hcoarse hAhead hrho hrate hgeom Cert htri hΔ hΔ1
        sigma d hradius hRweak hsigma hcap hcontourSmall hcoarseSmall
        row col
    have hcontinuous' : ContinuousOn
        (fun t : ℝ =>
          cmp99SourcePi4FullComplexBackgroundMinimizerMatrixDerivative
            (R := R) anchor K hc hmass hK sigma d (t : ℂ) row col)
        (Set.uIcc (0 : ℝ) 1) := by
      simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hcontinuous
    exact hcontinuous'.intervalIntegrable

set_option maxHeartbeats 10000000 in
/-- Physical one-coordinate FTC for the source-faithful rectangular
minimizer.  Both the derivative and its interval integrability are generated
from the literal contour estimates. -/
theorem
    integral_cmp99SourcePi4RealBackgroundMinimizerOperatorDerivative_eq_sub_of_source
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
    (hradius : 1 ≤ radius) (hRweak : 1 ≤ Rweak)
    (hsigma : ∀ x, ‖sigma x - 1‖ ≤ (1 : ℝ))
    (hcap : ∀ x, ‖sigma x‖ ≤ Rweak)
    (hcontourSmall :
      ‖cmp116SourcePi4ComplexContourRatio Δ rho Rweak‖ < 1)
    (hcoarseSmall :
      cmp99SourcePi4ComplexCoarseRelativeDefectBound
        (M := M) (Q := Q) (Nc := Nc)
        (cmp99SourcePi4WeakenedCoarseCovariance
          (R := R) anchor K hc hmass hK (fun _ => 1)
          hcoarseRate hcoarse)
        Δ Ahead rho rate radius Rweak < 1) :
    (∫ t : ℝ in (0 : ℝ)..1,
        cmp99SourcePi4RealBackgroundMinimizerOperatorDerivative
          (R := R) anchor K hc hmass hK sigma d t) =
      cmp99SourcePi4RealBackgroundMinimizerOperatorCurve
          (R := R) anchor K hc hmass hK sigma d 1 -
        cmp99SourcePi4RealBackgroundMinimizerOperatorCurve
          (R := R) anchor K hc hmass hK sigma d 0 := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := cmp99SourcePi4RealBackgroundMinimizerOperatorCurve
      (R := R) anchor K hc hmass hK sigma d)
    (f' := cmp99SourcePi4RealBackgroundMinimizerOperatorDerivative
      (R := R) anchor K hc hmass hK sigma d)
  · intro t ht
    have htIcc : t ∈ Set.Icc (0 : ℝ) 1 := by
      simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht
    exact
      hasDerivAt_cmp99SourcePi4RealBackgroundMinimizerOperatorCurve_of_source
        anchor K hsourceRange hfiniteRange hc hmass hK hD
        hcoarseRate hcoarse hAhead hrho hrate hgeom Cert htri hΔ hΔ1
        sigma d (show 0 ≤ radius by linarith) hRweak hsigma hcap t
        (sourceUpdate_unitShifted sigma d hsigma hradius htIcc)
        (sourceUpdate_cap sigma d hRweak hcap htIcc)
        hcontourSmall hcoarseSmall
  · have hcontinuous : ContinuousOn
        (cmp99SourcePi4RealBackgroundMinimizerOperatorDerivative
          (R := R) anchor K hc hmass hK sigma d)
        (Set.Icc (0 : ℝ) 1) := by
      apply
        continuousOn_cmp99PhysicalRectangularOfComplexMatrix_of_entrywise
      intro row col
      exact
        continuousOn_cmp99SourcePi4BackgroundMinimizerDerivative_compOfReal_of_source
          anchor K hsourceRange hfiniteRange hc hmass hK hD
          hcoarseRate hcoarse hAhead hrho hrate hgeom Cert htri hΔ hΔ1
          sigma d hradius hRweak hsigma hcap hcontourSmall hcoarseSmall
          row col
    have hcontinuous' : ContinuousOn
        (cmp99SourcePi4RealBackgroundMinimizerOperatorDerivative
          (R := R) anchor K hc hmass hK sigma d)
        (Set.uIcc (0 : ℝ) 1) := by
      simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hcontinuous
    exact hcontinuous'.intervalIntegrable

end

end YangMills.RG
