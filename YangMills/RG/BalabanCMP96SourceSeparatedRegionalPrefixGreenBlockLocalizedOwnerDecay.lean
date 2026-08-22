/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP96SourceSeparatedRegionalPrefixRescaledOwnerDecay

/-!
# PRE-VALIDATION: physical P8 Green block-localized owner decay

This source is present, its `.olean` has not yet been materialized, and its
result has not yet been verified by the Lean compiler.

The sealed rescaled-owner theorem accepts a chosen source site representing
the requested owner.  The source-facing CMP99 (3.42) predicate quantifies
over every owner, including owners whose active fibre is empty.  This module
closes that interface gap: in an empty fibre the support condition forces the
input field to be zero; otherwise the representing site is constructed
internally.

The result remains per-depth.  It does not assert a uniform physical `B0` or
`delta0` and does not instantiate the complete CMP99 (3.42) certificate.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

variable {L K Q Nc : ℕ}
variable [NeZero L] [NeZero K] [NeZero Q] [NeZero Nc]

/-- The physical P8 Green satisfies the source-facing block-localized bound
for every source owner at one fixed depth.  Empty owner fibres contribute
only the zero input. -/
theorem cmp96SourceSeparatedRegionalPrefixGreen_blockLocalizedSupBound
    (P : CMP95SourceSmoothPartitionProfile)
    (hL : 2 ≤ L) (depth : ℕ) {spacing epsilon a decay : ℝ}
    (hspacing : 0 < spacing) (ha : 0 < a) (hdecay : 0 < decay)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 L Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize L (2 * (K * Q)) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 L (depth + 1)
      spacing epsilon < 1)
    (cell : FinBox 4 Q)
    (root : ActiveGaugeRegion.Site
      (cmp96SourceSeparatedRegionalCell P L K Q depth cell)) :
    letI : Nonempty (ActiveGaugeRegion.Site
      (cmp96SourceSeparatedRegionalCell P L K Q depth cell)) := ⟨root⟩
    let ell := L ^ (depth + 1)
    let A := cmp89SourceSeparatedPrefixPrecisionUpperBound
        (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth
        spacing epsilon a background budget fineSmall *
      Real.exp (decay * (ell : ℕ))
    let c := cmp89SourceSeparatedPrefixCoercivity
      (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth
      spacing epsilon a background budget fineSmall
    let rate := finitePiLpExponentialInverseDecayRate A decay
      (cmp99OmegaSiteExpSumBound (decay / 4)) c
    let ownerRate := (ell : ℝ) * rate
    let ownerAmplitude := (2 / c) *
      Real.exp (3 * rate * ((ell - 1 : ℕ) : ℝ))
    FinitePiLpTypedBlockLocalizedSupBound
      (cmp96SourceSeparatedRegionalPrefixGreen
        (L := L) (K := K) (Q := Q) (Nc := Nc)
        P hL depth hspacing ha background budget fineSmall hsmall cell)
      (cmp99Eq342SourceLocalizedActiveOwner L K Q depth)
      (cmp99Eq342SourceLocalizedActiveOwner L K Q depth)
      finBoxDist (ownerAmplitude * (ell : ℝ) ^ 2) ownerRate := by
  dsimp only
  let Omega := cmp96SourceSeparatedRegionalCell P L K Q depth cell
  let ell := L ^ (depth + 1)
  let Cregional := cmp96SourceSeparatedRegionalPrefixGreen
    P hL depth hspacing ha background budget fineSmall hsmall cell
  let A := cmp89SourceSeparatedPrefixPrecisionUpperBound hL depth
      spacing epsilon a background budget fineSmall *
    Real.exp (decay * (ell : ℕ))
  let c := cmp89SourceSeparatedPrefixCoercivity hL depth
    spacing epsilon a background budget fineSmall
  let rate := finitePiLpExponentialInverseDecayRate A decay
    (cmp99OmegaSiteExpSumBound (decay / 4)) c
  let ownerRate := (ell : ℝ) * rate
  let ownerAmplitude := (2 / c) *
    Real.exp (3 * rate * ((ell - 1 : ℕ) : ℝ))
  letI : Nonempty (ActiveGaugeRegion.Site Omega) := ⟨root⟩
  have hc : 0 < c := by
    exact cmp89SourceSeparatedPrefixCoercivity_pos hL depth hspacing ha
      background budget fineSmall hsmall
  have hA : 0 ≤ A := by
    exact mul_nonneg
      (cmp89SourceSeparatedPrefixPrecisionUpperBound_pos hL depth
        hspacing background budget fineSmall).le
      (Real.exp_pos _).le
  have hrow : 0 ≤ cmp99OmegaSiteExpSumBound (decay / 4) := by
    unfold cmp99OmegaSiteExpSumBound
    exact tsum_nonneg fun _ =>
      mul_nonneg (Nat.cast_nonneg _) (Real.exp_pos _).le
  have hrate : 0 < rate := by
    exact finitePiLpExponentialInverseDecayRate_pos hA hdecay hrow hc
  have hell : 0 < (ell : ℝ) := by
    exact_mod_cast pow_pos (NeZero.pos L) (depth + 1)
  have hownerAmplitude : 0 ≤ ownerAmplitude := by
    exact mul_nonneg (div_nonneg (by positivity) hc.le) (Real.exp_pos _).le
  refine ⟨mul_nonneg hownerAmplitude (sq_nonneg _), mul_pos hell hrate, ?_⟩
  intro owner f hf target
  by_cases howner : ∃ source : ActiveGaugeRegion.Site Omega,
      cmp99Eq342SourceLocalizedActiveOwner L K Q depth source = owner
  · rcases howner with ⟨source, hsource⟩
    have hbase :=
      norm_cmp96SourceSeparatedRegionalPrefixGreen_apply_le_rescaledOwnerScale
        P hL depth hspacing ha hdecay background budget fineSmall hsmall
        cell owner source hsource f hf target
    simpa [Cregional, ell, A, c, rate, ownerRate, ownerAmplitude,
      finBoxDist_comm] using hbase
  · have hfzero : f = 0 := by
      apply PiLp.ext
      intro source
      apply hf source
      intro hsource
      exact howner ⟨source, hsource⟩
    subst f
    have hzero :
        Cregional (0 : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc))
          target = 0 := by
      simp only [map_zero, PiLp.zero_apply]
    rw [hzero, norm_zero]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg hownerAmplitude (sq_nonneg _))
        (Real.exp_pos _).le)
      (finitePiLpSupNorm_nonneg 0)

end

end YangMills.RG
