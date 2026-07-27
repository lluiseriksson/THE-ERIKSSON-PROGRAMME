/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99ComplexCoarseDefectLayerExpansion

/-!
# Ordered-word expansion of powers of the CMP99 coarse defect

The coarse inverse contains powers of a noncommutative norm-convergent layer
sum.  This module expands each such power over finite ordered tuples of
physical fine-layer indices.  Absolute convergence justifies every Cauchy
product; no commutation or informal exchange of infinite sums is used.
-/

namespace YangMills.RG

noncomputable section

open scoped Matrix.Norms.Operator

/-- Absolute summability of all ordered words of a fixed length. -/
theorem summable_norm_cmp99OrderedTupleProduct
    {E : Type*} [NormedRing E] [CompleteSpace E]
    (a : ℕ → E) (hA : Summable fun n => ‖a n‖) :
    ∀ k : ℕ,
      Summable fun word : Fin k → ℕ =>
        ‖cmp99OrderedTupleProduct a word‖ := by
  intro k
  induction k with
  | zero =>
      exact Summable.of_finite
  | succ k ih =>
      have hprod :
          Summable fun pair : ℕ × (Fin k → ℕ) =>
            ‖a pair.1 * cmp99OrderedTupleProduct a pair.2‖ :=
        Summable.mul_norm hA ih
      have hpull :
          Summable
            ((fun word : Fin (k + 1) → ℕ =>
                ‖cmp99OrderedTupleProduct a word‖) ∘
              (Fin.consEquiv (fun _ : Fin (k + 1) => ℕ))) := by
        refine hprod.congr fun pair => ?_
        change
          ‖a pair.1 * cmp99OrderedTupleProduct a pair.2‖ =
            ‖cmp99OrderedTupleProduct a
              (Fin.cons pair.1 pair.2)‖
        rw [cmp99OrderedTupleProduct_cons]
      exact
        ((Fin.consEquiv
          (fun _ : Fin (k + 1) => ℕ)).summable_iff).mp hpull

/-- A power of an absolutely convergent noncommutative series is the sum
over ordered tuples of its terms. -/
theorem tsum_pow_eq_tsum_cmp99OrderedTupleProduct
    {E : Type*} [NormedRing E] [CompleteSpace E]
    (a : ℕ → E) (hA : Summable fun n => ‖a n‖) :
    ∀ k : ℕ,
      (∑' n : ℕ, a n) ^ k =
        ∑' word : Fin k → ℕ,
          cmp99OrderedTupleProduct a word := by
  intro k
  induction k with
  | zero =>
      rw [pow_zero]
      symm
      apply tsum_eq_single (fun i : Fin 0 => i.elim0)
      intro word hword
      exact absurd (Subsingleton.elim word _) hword
  | succ k ih =>
      have hwords :
          Summable fun word : Fin k → ℕ =>
            ‖cmp99OrderedTupleProduct a word‖ :=
        summable_norm_cmp99OrderedTupleProduct a hA k
      rw [pow_succ', ih,
        tsum_mul_tsum_of_summable_norm hA hwords]
      rw [← (Fin.consEquiv
        (fun _ : Fin (k + 1) => ℕ)).tsum_eq
          (fun word : Fin (k + 1) → ℕ =>
            cmp99OrderedTupleProduct a word)]
      apply tsum_congr
      intro pair
      change
        a pair.1 * cmp99OrderedTupleProduct a pair.2 =
          cmp99OrderedTupleProduct a (Fin.cons pair.1 pair.2)
      exact (cmp99OrderedTupleProduct_cons a pair.1 pair.2).symm

private abbrev FineField (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))] :=
  FinePhysicalOneCochain 4 M (2 * Q) Nc

private abbrev CoarseField (Q Nc : ℕ) [NeZero (2 * Q)] :=
  CoarsePhysicalOneCochain 4 (2 * Q) Nc

/-- Every Neumann power of the literal coarse relative defect is exactly a
sum over ordered words of transported physical fine layers. -/
theorem
    neg_cmp99SourcePi4FullComplexCoarseMiddleRelativeDefect_pow_eq_tsum_words
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
    (hdiff : Summable fun layer : ℕ =>
      cmp116SourcePi4FullComplexWeakenedCovarianceLayer
          (R := R) anchor K hc hmass hK sigma layer -
        cmp116SourcePi4FullComplexWeakenedCovarianceLayer
          (R := R) anchor K hc hmass hK (fun _ => 1) layer)
    (hone : Summable fun layer : ℕ =>
      cmp116SourcePi4FullComplexWeakenedCovarianceLayer
        (R := R) anchor K hc hmass hK (fun _ => 1) layer)
    (hlayerNorm : Summable fun layer : ℕ =>
      ‖cmp99SourcePi4ComplexCoarseRelativeDefectLayer
        (R := R) anchor K hc hmass hK
        baseCoarseCovariance sigma layer‖)
    (n : ℕ) :
    (-cmp99SourcePi4FullComplexCoarseMiddleRelativeDefect
        (R := R) anchor K hc hmass hK
        baseCoarseCovariance sigma) ^ n =
      ∑' word : Fin n → ℕ,
        cmp99OrderedTupleProduct
          (fun layer : ℕ =>
            -cmp99SourcePi4ComplexCoarseRelativeDefectLayer
              (R := R) anchor K hc hmass hK
              baseCoarseCovariance sigma layer)
          word := by
  let layer := fun i : ℕ =>
    cmp99SourcePi4ComplexCoarseRelativeDefectLayer
      (R := R) anchor K hc hmass hK
      baseCoarseCovariance sigma i
  have hnegNorm :
      Summable fun i : ℕ => ‖-layer i‖ := by
    simpa only [norm_neg] using hlayerNorm
  rw [
    cmp99SourcePi4FullComplexCoarseMiddleRelativeDefect_eq_tsum_layers
      anchor K hc hmass hK baseCoarseCovariance sigma hdiff hone]
  calc
    (-(∑' i : ℕ, layer i)) ^ n =
        (∑' i : ℕ, -layer i) ^ n := by
          exact congrArg (fun X => X ^ n)
            (tsum_neg (f := layer)).symm
    _ = ∑' word : Fin n → ℕ,
          cmp99OrderedTupleProduct (fun i => -layer i) word :=
      tsum_pow_eq_tsum_cmp99OrderedTupleProduct
        (fun i => -layer i) hnegNorm n

/-- Source contour data generate the complete ordered-word expansion of
every coarse Neumann power.  All Fubini inputs are discharged from the
physical layer estimates. -/
theorem
    neg_cmp99SourcePi4FullComplexCoarseMiddleRelativeDefect_pow_eq_tsum_words_of_source
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
    (-cmp99SourcePi4FullComplexCoarseMiddleRelativeDefect
        (R := R) anchor K hc hmass hK
        baseCoarseCovariance sigma) ^ n =
      ∑' word : Fin n → ℕ,
        cmp99OrderedTupleProduct
          (fun layer : ℕ =>
            -cmp99SourcePi4ComplexCoarseRelativeDefectLayer
              (R := R) anchor K hc hmass hK
              baseCoarseCovariance sigma layer)
          word := by
  have hdiffLayers :
      Summable fun layer : ℕ =>
        cmp116SourcePi4FullComplexWeakenedCovarianceLayer
            (R := R) anchor K hc hmass hK sigma layer -
          cmp116SourcePi4FullComplexWeakenedCovarianceLayer
            (R := R) anchor K hc hmass hK (fun _ => 1) layer :=
    summable_cmp116SourcePi4FullComplexWeakenedCovarianceLayer_sub_one
      anchor K hc hmass hK hAhead hrho hrate hgeom Cert htri hrange
      hΔ hΔ1 sigma hradius hRweak hdiff hcap hsmall
  have honeLayers :
      Summable fun layer : ℕ =>
        cmp116SourcePi4FullComplexWeakenedCovarianceLayer
          (R := R) anchor K hc hmass hK (fun _ => 1) layer :=
    summable_cmp116SourcePi4FullComplexWeakenedCovarianceLayer_one
      anchor K hc hmass hK hAhead hrho hrate hgeom Cert htri hrange
      hΔ hΔ1 hRweak hsmall
  have hnormLayers :
      Summable fun layer : ℕ =>
        ‖cmp99SourcePi4ComplexCoarseRelativeDefectLayer
          (R := R) anchor K hc hmass hK
          baseCoarseCovariance sigma layer‖ :=
    summable_norm_cmp99SourcePi4ComplexCoarseRelativeDefectLayer_of_source
      anchor K hc hmass hK baseCoarseCovariance
      hAhead hrho hrate hgeom Cert htri hrange hΔ hΔ1 sigma
      hradius hRweak hdiff hcap hsmall
  exact
    neg_cmp99SourcePi4FullComplexCoarseMiddleRelativeDefect_pow_eq_tsum_words
      anchor K hc hmass hK baseCoarseCovariance sigma
      hdiffLayers honeLayers hnormLayers n

end

end YangMills.RG
