/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80SourcePi4PhysicalSecondMixedLocalization
import YangMills.RG.BalabanCMP102Eq80SourcePi4VertexPolynomialFTC

/-!
# Arbitrary-depth Faà di Bruno formula for the physical equation-(80) potential

The finite vertex interpolation writes the literal physical potential as a
composition

`sigma ↦ V80 (H_interp sigma)`.

Mathlib's `OrderedFinpartition` implementation of the Faà di Bruno formula
therefore gives the exact derivative at every depth.  Each ordered partition
block is evaluated by one derivative of the interpolated propagator, and the
outer multilinear map is the corresponding derivative of the literal
four-term equation-(80) functional.

This replaces a hand-written depth-by-depth chain rule.  It is an equality of
actual iterated Fréchet derivatives, not a formal majorant.  Source-domain
localization of each inner propagator derivative is the next layer.
-/

namespace YangMills.RG

noncomputable section

private abbrev PhysicalField (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalGaugeOneCochain 4 (M * (2 * Q)) Nc

private abbrev PhysicalEndomorphism (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] :=
  PhysicalField M Q Nc →L[ℝ] PhysicalField M Q Nc

private abbrev WeakeningField (Q : ℕ) :=
  FinBox 4 (2 * Q) → ℝ

/-- The literal equation-(80) functional viewed as a function of its
propagator. -/
noncomputable def cmp102Eq80PotentialAsFunctionOfPropagator
    {M Q Nc : ℕ} [NeZero M] [NeZero Q]
    (D D₃ : PhysicalField M Q Nc → PhysicalField M Q Nc)
    (V₀ : PhysicalField M Q Nc → ℝ)
    (Δπ : PhysicalEndomorphism M Q Nc)
    (J A : PhysicalField M Q Nc)
    (H : PhysicalEndomorphism M Q Nc) : ℝ :=
  cmp102Eq80GlobalPotential D D₃ V₀ H Δπ J A

/-- The outer equation-(80) functional has the regularity of `V₀`. -/
theorem contDiff_cmp102Eq80PotentialAsFunctionOfPropagator
    {M Q Nc : ℕ} [NeZero M] [NeZero Q]
    (n : WithTop ℕ∞)
    (D D₃ : PhysicalField M Q Nc → PhysicalField M Q Nc)
    (V₀ : PhysicalField M Q Nc → ℝ)
    (Δπ : PhysicalEndomorphism M Q Nc)
    (J A : PhysicalField M Q Nc)
    (hV₀ : ContDiff ℝ n V₀) :
    ContDiff ℝ n
      (cmp102Eq80PotentialAsFunctionOfPropagator
        D D₃ V₀ Δπ J A) := by
  unfold cmp102Eq80PotentialAsFunctionOfPropagator
  exact
    contDiff_cmp102Eq80GlobalPotential_propagatorFamily
      D D₃ V₀
      (fun H : PhysicalEndomorphism M Q Nc => H)
      Δπ J A contDiff_id hV₀

/-- Exact arbitrary-depth Faà di Bruno identity for the physical
vertex-polynomial equation-(80) potential. -/
theorem iteratedFDeriv_cmp102Eq80SourcePi4RealPotentialVertexPolynomial
    {M Q Nc R n : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (D D₃ : PhysicalField M Q Nc → PhysicalField M Q Nc)
    (V₀ : PhysicalField M Q Nc → ℝ)
    (Δπ : PhysicalEndomorphism M Q Nc)
    (J : PhysicalField M Q Nc)
    (base : WeakeningField Q)
    (coordinates : List (FinBox 4 (2 * Q)))
    (sigma : WeakeningField Q)
    (A : PhysicalField M Q Nc)
    (hV₀ : ContDiff ℝ n V₀) :
    iteratedFDeriv ℝ n
        (fun tau =>
          cmp102Eq80SourcePi4RealPotentialVertexPolynomial
            (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J
            base coordinates tau A)
        sigma =
      (ftaylorSeries ℝ
          (cmp102Eq80PotentialAsFunctionOfPropagator
            D D₃ V₀ Δπ J A)
          (cmp116FiniteMultiaffineInterpolation
            (fun u =>
              cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative
                (R := R) anchor K hc hmass hK u ∅)
            base coordinates sigma)).taylorComp
        (ftaylorSeries ℝ
          (cmp116FiniteMultiaffineInterpolation
            (fun u =>
              cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative
                (R := R) anchor K hc hmass hK u ∅)
            base coordinates)
          sigma) n := by
  have houter :
      ContDiff ℝ n
        (cmp102Eq80PotentialAsFunctionOfPropagator
          D D₃ V₀ Δπ J A) :=
    contDiff_cmp102Eq80PotentialAsFunctionOfPropagator
      n D D₃ V₀ Δπ J A hV₀
  have hinner :
      ContDiff ℝ n
        (cmp116FiniteMultiaffineInterpolation
          (fun u =>
            cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative
              (R := R) anchor K hc hmass hK u ∅)
          base coordinates) :=
    contDiff_cmp116FiniteMultiaffineInterpolation
      n _ base coordinates
  have hcomp :=
    iteratedFDeriv_comp houter.contDiffAt hinner.contDiffAt
      (x := sigma) (i := n)
      (show (n : WithTop ℕ∞) ≤ (n : WithTop ℕ∞) from le_rfl)
  simpa [cmp102Eq80SourcePi4RealPotentialVertexPolynomial,
    cmp102Eq80PotentialAsFunctionOfPropagator,
    Function.comp_def] using hcomp

/-- Applied form of the arbitrary-depth formula: the derivative is the
finite sum over Mathlib's ordered partitions, with one inner propagator
derivative for every block. -/
theorem
    iteratedFDeriv_cmp102Eq80SourcePi4RealPotentialVertexPolynomial_apply_eq_sum_orderedFinpartition
    {M Q Nc R n : ℕ}
    [NeZero M] [NeZero Q] [NeZero (Nc ^ 2 - 1)]
    (anchor : FinBox 4 Q)
    (K : PhysicalEndomorphism M Q Nc)
    {c mass : ℝ} (hc : 0 < c) (hmass : 0 < mass)
    (hK : IsCoerciveCLM K c)
    (D D₃ : PhysicalField M Q Nc → PhysicalField M Q Nc)
    (V₀ : PhysicalField M Q Nc → ℝ)
    (Δπ : PhysicalEndomorphism M Q Nc)
    (J : PhysicalField M Q Nc)
    (base : WeakeningField Q)
    (coordinates : List (FinBox 4 (2 * Q)))
    (sigma : WeakeningField Q)
    (A : PhysicalField M Q Nc)
    (directions : Fin n → WeakeningField Q)
    (hV₀ : ContDiff ℝ n V₀) :
    iteratedFDeriv ℝ n
        (fun tau =>
          cmp102Eq80SourcePi4RealPotentialVertexPolynomial
            (R := R) anchor K hc hmass hK D D₃ V₀ Δπ J
            base coordinates tau A)
        sigma directions =
      ∑ partition : OrderedFinpartition n,
        ftaylorSeries ℝ
            (cmp102Eq80PotentialAsFunctionOfPropagator
              D D₃ V₀ Δπ J A)
            (cmp116FiniteMultiaffineInterpolation
              (fun u =>
                cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative
                  (R := R) anchor K hc hmass hK u ∅)
              base coordinates sigma)
            partition.length
          (partition.applyOrderedFinpartition
            (fun block =>
              ftaylorSeries ℝ
                (cmp116FiniteMultiaffineInterpolation
                  (fun u =>
                    cmp116SourcePi4FullRealWeakenedCovarianceMixedDerivative
                      (R := R) anchor K hc hmass hK u ∅)
                  base coordinates)
                sigma (partition.partSize block))
            directions) := by
  rw [
    iteratedFDeriv_cmp102Eq80SourcePi4RealPotentialVertexPolynomial
      anchor K hc hmass hK D D₃ V₀ Δπ J
      base coordinates sigma A hV₀]
  simp [FormalMultilinearSeries.taylorComp,
    FormalMultilinearSeries.compAlongOrderedFinpartition_apply]

end

end YangMills.RG
