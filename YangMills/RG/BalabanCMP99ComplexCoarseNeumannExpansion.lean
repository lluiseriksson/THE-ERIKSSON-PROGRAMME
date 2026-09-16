/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourcePi4ComplexCoarseDefectBound

/-!
# Neumann expansion of the complex CMP99 coarse inverse

The determinant argument proves that the rectangular minimizer exists, but
does not retain localization.  This module rewrites the same literal coarse
inverse as the convergent Neumann series of the physical relative defect

`D(σ) = M(1)⁻¹ (M(σ) - M(1))`.

This is the algebraic bridge needed to combine the fine source random walks
with coarse-middle corrections without replacing the rectangular minimizer
by a square covariance.
-/

namespace YangMills.RG

noncomputable section

open scoped Matrix.Norms.Operator

/-- Neumann candidate for the inverse of `target`, expressed relative to a
chosen right inverse of `base`. -/
noncomputable def complexMatrixRelativeNeumannInverse
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (baseInv base target : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  (∑' n : ℕ, (-(baseInv * (target - base))) ^ n) * baseInv

/-- The relative Neumann candidate is an exact right inverse. -/
theorem mul_complexMatrixRelativeNeumannInverse_eq_one
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (baseInv base target : Matrix ι ι ℂ)
    (hbase : base * baseInv = 1)
    (hsmall : ‖baseInv * (target - base)‖ < 1) :
    target *
        complexMatrixRelativeNeumannInverse baseInv base target =
      1 := by
  let D := baseInv * (target - base)
  let N := ∑' n : ℕ, (-D) ^ n
  have hbaseLeft : baseInv * base = 1 := mul_eq_one_comm.mpr hbase
  have hgeom : (1 + D) * N = 1 := by
    simpa [sub_neg_eq_add, N] using
      (mul_neg_geom_series (-D) (by simpa [D] using hsmall))
  have htarget : target = base * (1 + D) := by
    calc
      target = base + (target - base) := by abel
      _ = base + (base * baseInv) * (target - base) := by rw [hbase, one_mul]
      _ = base + base * (baseInv * (target - base)) := by
        rw [Matrix.mul_assoc]
      _ = base * (1 + D) := by
        simp [D, Matrix.mul_add]
  rw [complexMatrixRelativeNeumannInverse, htarget]
  have hDtarget :
      baseInv * (base * (1 + D) - base) = D := by
    rw [Matrix.mul_sub,
      ← Matrix.mul_assoc baseInv base (1 + D),
      hbaseLeft, Matrix.one_mul]
    abel
  rw [hDtarget]
  change (base * (1 + D)) * (N * baseInv) = 1
  rw [Matrix.mul_assoc base (1 + D) (N * baseInv),
    ← Matrix.mul_assoc (1 + D) N baseInv, hgeom,
    Matrix.one_mul, hbase]

/-- Hence the literal nonsingular inverse equals its convergent relative
Neumann series. -/
theorem complexMatrixNonsingInv_eq_relativeNeumannInverse
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (baseInv base target : Matrix ι ι ℂ)
    (hbase : base * baseInv = 1)
    (hsmall : ‖baseInv * (target - base)‖ < 1) :
    target⁻¹ =
      complexMatrixRelativeNeumannInverse baseInv base target :=
  Matrix.inv_eq_right_inv
    (mul_complexMatrixRelativeNeumannInverse_eq_one
      baseInv base target hbase hsmall)

private abbrev FineField (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))] :=
  FinePhysicalOneCochain 4 M (2 * Q) Nc

private abbrev CoarseField (Q Nc : ℕ) [NeZero (2 * Q)] :=
  CoarsePhysicalOneCochain 4 (2 * Q) Nc

/-- The literal CMP99 complex coarse inverse is exactly the Neumann series
of its physical relative defect. -/
theorem cmp99SourcePi4FullComplexCoarseMiddleMatrix_inv_eq_neumann
    {M Q Nc R : ℕ}
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
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (hsmall :
      ‖cmp99SourcePi4FullComplexCoarseMiddleRelativeDefect
        (R := R) anchor K hc hmass hK
        (cmp99SourcePi4WeakenedCoarseCovariance
          (R := R) anchor K hc hmass hK (fun _ => 1)
          hcoarseRate hcoarse)
        sigma‖ < 1) :
    (cmp99SourcePi4FullComplexCoarseMiddleMatrix
        (R := R) anchor K hc hmass hK sigma)⁻¹ =
      complexMatrixRelativeNeumannInverse
        (cmp116PhysicalEndomorphismComplexMatrix
          (cmp99SourcePi4WeakenedCoarseCovariance
            (R := R) anchor K hc hmass hK (fun _ => 1)
            hcoarseRate hcoarse))
        (cmp99SourcePi4FullComplexCoarseMiddleMatrix
          (R := R) anchor K hc hmass hK (fun _ => 1))
        (cmp99SourcePi4FullComplexCoarseMiddleMatrix
          (R := R) anchor K hc hmass hK sigma) := by
  apply complexMatrixNonsingInv_eq_relativeNeumannInverse
  · exact
      cmp99SourcePi4FullComplexCoarseMiddleMatrix_one_mul_coarseCovariance_eq_one
        anchor K hsourceRange hfiniteRange hc hmass hK hD
        hcoarseRate hcoarse
  · simpa [cmp99SourcePi4FullComplexCoarseMiddleRelativeDefect] using hsmall

private abbrev FineCoord (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))] :=
  CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc

private abbrev CoarseCoord (Q Nc : ℕ)
    [NeZero Q] [NeZero (2 * Q)] :=
  CMP116PhysicalWalkCoordinate 4 (2 * Q) Nc

/-- One coarse-Neumann layer of the literal rectangular minimizer. -/
noncomputable def cmp99SourcePi4ComplexBackgroundMinimizerNeumannLayer
    {M Q Nc R : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (anchor : FinBox 4 Q)
    (K : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (baseCoarseCovariance :
      CoarseField Q Nc →L[ℝ] CoarseField Q Nc)
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (n : ℕ) :
    Matrix (FineCoord M Q Nc) (CoarseCoord Q Nc) ℂ :=
  let Csigma :=
    cmp116SourcePi4FullComplexWeakenedCovarianceMatrix
      (R := R) anchor K hc hmass hK sigma
  let baseInv :=
    cmp116PhysicalEndomorphismComplexMatrix baseCoarseCovariance
  let D :=
    cmp99SourcePi4FullComplexCoarseMiddleRelativeDefect
      (R := R) anchor K hc hmass hK baseCoarseCovariance sigma
  (Csigma *
      cmp99SourcePi4ComplexBlockAdjointMatrix
        (M := M) (Q := Q) (Nc := Nc)) *
    ((-D) ^ n * baseInv)

/-- Under the literal relative-defect contraction, the complete complex
rectangular minimizer is the length-ordered sum of its coarse-Neumann
layers. -/
theorem
    cmp99SourcePi4FullComplexBackgroundMinimizerMatrix_eq_tsum_neumannLayers
    {M Q Nc R : ℕ}
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
    (sigma : FinBox 4 (2 * Q) → ℂ)
    (hsmall :
      ‖cmp99SourcePi4FullComplexCoarseMiddleRelativeDefect
        (R := R) anchor K hc hmass hK
        (cmp99SourcePi4WeakenedCoarseCovariance
          (R := R) anchor K hc hmass hK (fun _ => 1)
          hcoarseRate hcoarse)
        sigma‖ < 1) :
    cmp99SourcePi4FullComplexBackgroundMinimizerMatrix
        (R := R) anchor K hc hmass hK sigma =
      ∑' n : ℕ,
        cmp99SourcePi4ComplexBackgroundMinimizerNeumannLayer
          (R := R) anchor K hc hmass hK
          (cmp99SourcePi4WeakenedCoarseCovariance
            (R := R) anchor K hc hmass hK (fun _ => 1)
            hcoarseRate hcoarse)
          sigma n := by
  let baseInv :=
    cmp116PhysicalEndomorphismComplexMatrix
      (cmp99SourcePi4WeakenedCoarseCovariance
        (R := R) anchor K hc hmass hK (fun _ => 1)
        hcoarseRate hcoarse)
  let D :=
    cmp99SourcePi4FullComplexCoarseMiddleRelativeDefect
      (R := R) anchor K hc hmass hK
      (cmp99SourcePi4WeakenedCoarseCovariance
        (R := R) anchor K hc hmass hK (fun _ => 1)
        hcoarseRate hcoarse)
      sigma
  let left :=
    cmp116SourcePi4FullComplexWeakenedCovarianceMatrix
        (R := R) anchor K hc hmass hK sigma *
      cmp99SourcePi4ComplexBlockAdjointMatrix
        (M := M) (Q := Q) (Nc := Nc)
  have hpow : Summable fun n : ℕ => (-D) ^ n :=
    summable_geometric_of_norm_lt_one (by simpa [D] using hsmall)
  rw [cmp99SourcePi4FullComplexBackgroundMinimizerMatrix,
    cmp99SourcePi4FullComplexCoarseMiddleMatrix_inv_eq_neumann
      anchor K hsourceRange hfiniteRange hc hmass hK hD
      hcoarseRate hcoarse sigma hsmall]
  unfold complexMatrixRelativeNeumannInverse
  change left * ((∑' n : ℕ, (-D) ^ n) * baseInv) =
    ∑' n : ℕ, left * ((-D) ^ n * baseInv)
  rw [← hpow.tsum_mul_right baseInv]
  let L :
      Matrix (CoarseCoord Q Nc) (CoarseCoord Q Nc) ℂ →ₗ[ℂ]
        Matrix (FineCoord M Q Nc) (CoarseCoord Q Nc) ℂ := {
    toFun := fun X => left * X
    map_add' := fun X Y => by simp [Matrix.mul_add]
    map_smul' := fun r X => by
      ext i j
      simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul]
      simp only [RingHom.id_apply]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _hx
      ring
  }
  let Lc :
      Matrix (CoarseCoord Q Nc) (CoarseCoord Q Nc) ℂ →L[ℂ]
        Matrix (FineCoord M Q Nc) (CoarseCoord Q Nc) ℂ :=
    ⟨L, L.continuous_of_finiteDimensional⟩
  exact Lc.map_tsum (hpow.mul_right baseInv)

/-- The complete source contour budgets generate the coarse-Neumann
expansion of the rectangular minimizer; no contraction of a renamed matrix
is supplied by the caller. -/
theorem
    cmp99SourcePi4FullComplexBackgroundMinimizerMatrix_eq_tsum_neumannLayers_of_source
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
    cmp99SourcePi4FullComplexBackgroundMinimizerMatrix
        (R := R) anchor K hc hmass hK sigma =
      ∑' n : ℕ,
        cmp99SourcePi4ComplexBackgroundMinimizerNeumannLayer
          (R := R) anchor K hc hmass hK
          (cmp99SourcePi4WeakenedCoarseCovariance
            (R := R) anchor K hc hmass hK (fun _ => 1)
            hcoarseRate hcoarse)
          sigma n := by
  apply
    cmp99SourcePi4FullComplexBackgroundMinimizerMatrix_eq_tsum_neumannLayers
      anchor K hsourceRange hfiniteRange hc hmass hK hD
      hcoarseRate hcoarse sigma
  exact lt_of_le_of_lt
    (norm_cmp99SourcePi4FullComplexCoarseMiddleRelativeDefect_le_source
      anchor K hc hmass hK
      (cmp99SourcePi4WeakenedCoarseCovariance
        (R := R) anchor K hc hmass hK (fun _ => 1)
        hcoarseRate hcoarse)
      hAhead hrho hrate hgeom Cert htri hsourceRange hΔ hΔ1 sigma
      hradius hRweak hdiff hcap hcontourSmall)
    hcoarseSmall

end

end YangMills.RG
