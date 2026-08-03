/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99ComplexFineHeadTailMultiplicityExpansion

/-!
# Complete nested multiplicity expansion of the complex CMP99 minimizer

PRE-VALIDATION: source is present, its `.olean` has not yet been materialized,
and the result has not yet been verified by the Lean compiler.

The literal rectangular minimizer already has a source-ordered expansion

`Neumann length -> coarse word -> tail choice -> head length -> head walk`.

The preceding multiplicity module expands each final word into a finite sum
over omitted tail factors.  This file lifts that finite identity through the
complete nested series without interchanging any two infinite sums.  Every
matrix word remains in its original noncommutative order, while every repeated
weakening carrier is retained in the multiplicity-valued monomial.

This is the exact whole-series algebraic bridge for `H(s)`.  It does not yet
flatten the nested series into one walk type, prove the radial multiplicity
majorant needed for that flattening, or construct the distinct source object
`H0(s)`.
-/

open scoped BigOperators

namespace YangMills.RG

noncomputable section

private abbrev FineField (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))] :=
  FinePhysicalOneCochain 4 M (2 * Q) Nc

/-- End-to-end multiplicity expansion of the literal complex rectangular
minimizer.  The original nesting order is preserved verbatim; the only new
sum is the finite powerset expansion inside each literal head-tail word. -/
theorem
    cmp99SourcePi4FullComplexBackgroundMinimizerMatrix_eq_nestedMultiplicitySeries_of_source
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
      ∑' neumannLength : ℕ,
        ∑' layerWord : Fin neumannLength → ℕ,
          ∑ choice : CMP99SourcePi4CoarseFineWalkChoice
              M Q R layerWord,
            ∑' headLength : ℕ,
              ∑ head : CMP99SourcePi4FineWalkIndex M Q R headLength,
                ∑ omitted ∈
                    (Finset.univ : Finset (Fin neumannLength)).powerset,
                  ((-1 : ℂ) ^ omitted.card *
                    cmp116ComplexWeakeningMultiplicityMonomial
                      (cmp99SourcePi4ComplexFineHeadTailMultiplicity
                        anchor head choice
                          (Finset.univ \ omitted)) sigma) •
                    cmp99SourcePi4ComplexFineHeadTailWordBase
                      K hc hmass hK
                      (cmp99SourcePi4WeakenedCoarseCovariance
                        (R := R) anchor K hc hmass hK (fun _ => 1)
                        hcoarseRate hcoarse)
                      head choice := by
  rw [
    cmp99SourcePi4FullComplexBackgroundMinimizerMatrix_eq_literalFineWalkSeries_of_source
      anchor K hsourceRange hfiniteRange hc hmass hK hD
      hcoarseRate hcoarse hAhead hrho hrate hgeom Cert htri hΔ hΔ1
      sigma hradius hRweak hdiff hcap hcontourSmall hcoarseSmall]
  apply tsum_congr
  intro neumannLength
  apply tsum_congr
  intro layerWord
  apply Finset.sum_congr rfl
  intro choice _hchoice
  apply tsum_congr
  intro headLength
  apply Finset.sum_congr rfl
  intro head _hhead
  exact
    cmp99SourcePi4ComplexFineHeadTailWordTerm_eq_sum_multiplicity
      anchor K hc hmass hK
      (cmp99SourcePi4WeakenedCoarseCovariance
        (R := R) anchor K hc hmass hK (fun _ => 1)
        hcoarseRate hcoarse)
      sigma head layerWord choice

end

end YangMills.RG
