/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99ComplexCoarseDefectWordExpansion

/-!
# Complete ordered-word expansion of the complex CMP99 minimizer

This module attaches the literal fine head `C(σ) Q*` and the full-coupling
coarse inverse to each ordered coarse-defect word.  It thereby rewrites the
rectangular minimizer itself as a length-ordered nested physical series.
The outer length order is retained, so no exchange of two infinite sums is
hidden.
-/

namespace YangMills.RG

noncomputable section

open scoped Matrix.Norms.Operator

/-- Continuous two-sided multiplication from a square middle matrix into a
possibly rectangular matrix space. -/
noncomputable def complexMatrixTwoSidedCLM
    {α β γ : Type*}
    [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    [Fintype γ] [DecidableEq γ]
    (left : Matrix α β ℂ) (right : Matrix β γ ℂ) :
    Matrix β β ℂ →L[ℂ] Matrix α γ ℂ := by
  let L : Matrix β β ℂ →ₗ[ℂ] Matrix α γ ℂ := {
    toFun := fun X => left * X * right
    map_add' := fun X Y => by
      simp [Matrix.mul_add, Matrix.add_mul]
    map_smul' := fun r X => by
      simp [Matrix.mul_smul, Matrix.smul_mul]
  }
  exact ⟨L, L.continuous_of_finiteDimensional⟩

theorem complexMatrixTwoSidedCLM_apply
    {α β γ : Type*}
    [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    [Fintype γ] [DecidableEq γ]
    (left : Matrix α β ℂ) (right : Matrix β γ ℂ)
    (X : Matrix β β ℂ) :
    complexMatrixTwoSidedCLM left right X =
      left * X * right := rfl

private abbrev FineField (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))] :=
  FinePhysicalOneCochain 4 M (2 * Q) Nc

private abbrev CoarseField (Q Nc : ℕ) [NeZero (2 * Q)] :=
  CoarsePhysicalOneCochain 4 (2 * Q) Nc

private abbrev FineCoord (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))] :=
  CMP116PhysicalWalkCoordinate 4 (M * (2 * Q)) Nc

private abbrev CoarseCoord (Q Nc : ℕ)
    [NeZero Q] [NeZero (2 * Q)] :=
  CMP116PhysicalWalkCoordinate 4 (2 * Q) Nc

/-- One complete minimizer term: the literal fine head, an ordered word of
negative coarse-defect layers, and the full-coupling coarse inverse. -/
noncomputable def cmp99SourcePi4ComplexBackgroundMinimizerWordTerm
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
    {n : ℕ} (word : Fin n → ℕ) :
    Matrix (FineCoord M Q Nc) (CoarseCoord Q Nc) ℂ :=
  (cmp116SourcePi4FullComplexWeakenedCovarianceMatrix
        (R := R) anchor K hc hmass hK sigma *
      cmp99SourcePi4ComplexBlockAdjointMatrix
        (M := M) (Q := Q) (Nc := Nc)) *
    cmp99OrderedTupleProduct
      (fun layer : ℕ =>
        -cmp99SourcePi4ComplexCoarseRelativeDefectLayer
          (R := R) anchor K hc hmass hK
          baseCoarseCovariance sigma layer)
      word *
    cmp116PhysicalEndomorphismComplexMatrix baseCoarseCovariance

/-- For a fixed Neumann length, the literal minimizer layer is exactly the
absolutely convergent sum of complete ordered physical word terms. -/
theorem
    cmp99SourcePi4ComplexBackgroundMinimizerNeumannLayer_eq_tsum_words_of_source
    {M Q Nc R Δ : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    [NeZero (2 * Q)] [NeZero (M * (2 * Q))]
    (anchor : FinBox 4 Q)
    (K : FineField M Q Nc →L[ℝ] FineField M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (baseCoarseCovariance :
      CoarseField Q Nc →L[ℝ] CoarseField Q Nc)
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
      ‖cmp116SourcePi4ComplexContourRatio Δ rho Rweak‖ < 1)
    (n : ℕ) :
    cmp99SourcePi4ComplexBackgroundMinimizerNeumannLayer
        (R := R) anchor K hc hmass hK
        baseCoarseCovariance sigma n =
      ∑' word : Fin n → ℕ,
        cmp99SourcePi4ComplexBackgroundMinimizerWordTerm
          (R := R) anchor K hc hmass hK
          baseCoarseCovariance sigma word := by
  let defectLayer := fun layer : ℕ =>
    cmp99SourcePi4ComplexCoarseRelativeDefectLayer
      (R := R) anchor K hc hmass hK
      baseCoarseCovariance sigma layer
  let left :=
    cmp116SourcePi4FullComplexWeakenedCovarianceMatrix
        (R := R) anchor K hc hmass hK sigma *
      cmp99SourcePi4ComplexBlockAdjointMatrix
        (M := M) (Q := Q) (Nc := Nc)
  let right :=
    cmp116PhysicalEndomorphismComplexMatrix baseCoarseCovariance
  have hnormLayers :
      Summable fun layer : ℕ => ‖defectLayer layer‖ :=
    summable_norm_cmp99SourcePi4ComplexCoarseRelativeDefectLayer_of_source
      anchor K hc hmass hK baseCoarseCovariance
      hAhead hrho hrate hgeom Cert htri hrange hΔ hΔ1 sigma
      hradius hRweak hdiff hcap hsmall
  have hnegNorm :
      Summable fun layer : ℕ => ‖-defectLayer layer‖ := by
    simpa only [norm_neg] using hnormLayers
  have hwordNorm :
      Summable fun word : Fin n → ℕ =>
        ‖cmp99OrderedTupleProduct
          (fun layer => -defectLayer layer) word‖ :=
    summable_norm_cmp99OrderedTupleProduct
      (fun layer => -defectLayer layer) hnegNorm n
  rw [cmp99SourcePi4ComplexBackgroundMinimizerNeumannLayer,
    neg_cmp99SourcePi4FullComplexCoarseMiddleRelativeDefect_pow_eq_tsum_words_of_source
      anchor K hc hmass hK baseCoarseCovariance
      hAhead hrho hrate hgeom Cert htri hrange hΔ hΔ1 sigma
      hradius hRweak hdiff hcap hsmall n]
  calc
    cmp116SourcePi4FullComplexWeakenedCovarianceMatrix
          (R := R) anchor K hc hmass hK sigma *
        cmp99SourcePi4ComplexBlockAdjointMatrix
          (M := M) (Q := Q) (Nc := Nc) *
        ((∑' word : Fin n → ℕ,
            cmp99OrderedTupleProduct
              (fun layer => -defectLayer layer) word) *
          cmp116PhysicalEndomorphismComplexMatrix
            baseCoarseCovariance) =
      left *
          (∑' word : Fin n → ℕ,
            cmp99OrderedTupleProduct
              (fun layer => -defectLayer layer) word) *
        right := by
          simp only [left, right, Matrix.mul_assoc]
    _ = complexMatrixTwoSidedCLM left right
          (∑' word : Fin n → ℕ,
            cmp99OrderedTupleProduct
              (fun layer => -defectLayer layer) word) := rfl
    _ = ∑' word : Fin n → ℕ,
          complexMatrixTwoSidedCLM left right
            (cmp99OrderedTupleProduct
              (fun layer => -defectLayer layer) word) :=
      (complexMatrixTwoSidedCLM left right).map_tsum hwordNorm.of_norm
    _ = ∑' word : Fin n → ℕ,
          cmp99SourcePi4ComplexBackgroundMinimizerWordTerm
            (R := R) anchor K hc hmass hK
            baseCoarseCovariance sigma word := by
      apply tsum_congr
      intro word
      rfl

/-- The literal complex rectangular minimizer is the length-ordered nested
sum of its complete physical coarse-defect words.  The outer length order
is exactly the one in the original covariance construction. -/
theorem
    cmp99SourcePi4FullComplexBackgroundMinimizerMatrix_eq_tsum_tsum_words_of_source
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
      ∑' n : ℕ, ∑' word : Fin n → ℕ,
        cmp99SourcePi4ComplexBackgroundMinimizerWordTerm
          (R := R) anchor K hc hmass hK
          (cmp99SourcePi4WeakenedCoarseCovariance
            (R := R) anchor K hc hmass hK (fun _ => 1)
            hcoarseRate hcoarse)
          sigma word := by
  rw [
    cmp99SourcePi4FullComplexBackgroundMinimizerMatrix_eq_tsum_neumannLayers_of_source
      anchor K hsourceRange hfiniteRange hc hmass hK hD
      hcoarseRate hcoarse hAhead hrho hrate hgeom Cert htri hΔ hΔ1
      sigma hradius hRweak hdiff hcap hcontourSmall hcoarseSmall]
  apply tsum_congr
  intro n
  exact
    cmp99SourcePi4ComplexBackgroundMinimizerNeumannLayer_eq_tsum_words_of_source
      anchor K hc hmass hK
      (cmp99SourcePi4WeakenedCoarseCovariance
        (R := R) anchor K hc hmass hK (fun _ => 1)
        hcoarseRate hcoarse)
      hAhead hrho hrate hgeom Cert htri hsourceRange hΔ hΔ1 sigma
      hradius hRweak hdiff hcap hcontourSmall n

end

end YangMills.RG
