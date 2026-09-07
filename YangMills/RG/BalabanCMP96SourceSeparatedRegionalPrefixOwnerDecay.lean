/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP96SourceSeparatedRegionalPrefixOwnerInputAction
import YangMills.RG.BalabanCMP99SourceLocalizationOwnerForwardDistanceBridge

/-!
# Physical P8 Green decay between localization owners

This module transports the sealed fine-site decay of the physical P8 Green
action to the literal CMP99 localization-owner distance.  The forward metric
comparison is constructed internally; no free owner metric or decay bound is
accepted, and the source-scale factor from the preceding brick is unchanged.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

variable {L K Q Nc : ℕ}
variable [NeZero L] [NeZero K] [NeZero Q] [NeZero Nc]

/-- The physical P8 Green acting on one source-owner input decays at the same
canonical rate between the literal source-localization owners. -/
theorem norm_cmp96SourceSeparatedRegionalPrefixGreen_apply_le_ownerScale
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
    (owner : FinBox 4 (2 * (K * Q)))
    (root : ActiveGaugeRegion.Site
      (cmp96SourceSeparatedRegionalCell P L K Q depth cell))
    (hroot : cmp99Eq342SourceLocalizedActiveOwner L K Q depth root = owner)
    (f : FinitePiLpField
      (ActiveGaugeRegion.Site
        (cmp96SourceSeparatedRegionalCell P L K Q depth cell))
      (SUNLieCoord Nc))
    (hf : FinitePiLpSupportedInOwner
      (cmp99Eq342SourceLocalizedActiveOwner L K Q depth) owner f)
    (target : ActiveGaugeRegion.Site
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
    ‖cmp96SourceSeparatedRegionalPrefixGreen
        (L := L) (K := K) (Q := Q) (Nc := Nc)
        P hL depth hspacing ha background budget fineSmall hsmall cell f
        target‖ ≤
      (2 / c) *
        Real.exp (-(rate *
          (finBoxDist owner
            (cmp99Eq342SourceLocalizedActiveOwner L K Q depth target) : ℝ))) *
        (Real.exp (rate * ((ell - 1 : ℕ) : ℝ)) *
          (ell : ℝ) ^ 2 * finitePiLpSupNorm f) := by
  dsimp only
  let Omega := cmp96SourceSeparatedRegionalCell P L K Q depth cell
  let ell := L ^ (depth + 1)
  let A := cmp89SourceSeparatedPrefixPrecisionUpperBound hL depth
      spacing epsilon a background budget fineSmall *
    Real.exp (decay * (ell : ℕ))
  let c := cmp89SourceSeparatedPrefixCoercivity hL depth
    spacing epsilon a background budget fineSmall
  let rate := finitePiLpExponentialInverseDecayRate A decay
    (cmp99OmegaSiteExpSumBound (decay / 4)) c
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
  have hfine :=
    norm_cmp96SourceSeparatedRegionalPrefixGreen_apply_le_sourceScale
      P hL depth hspacing ha hdecay background budget fineSmall hsmall cell
      owner root hroot f hf target
  have hownerNat :
      finBoxDist owner
          (cmp99Eq342SourceLocalizedActiveOwner L K Q depth target) ≤
        finBoxDist root.1 target.1 := by
    rw [← hroot]
    simpa [cmp99Eq342SourceLocalizedActiveOwner] using
      (cmp99Eq389SourceLocalizationOwner_dist_le_fineDist
        (L := L) (K := K) (Q := Q) depth root.1 target.1)
  have howner :
      (finBoxDist owner
          (cmp99Eq342SourceLocalizedActiveOwner L K Q depth target) : ℝ) ≤
        (finBoxDist root.1 target.1 : ℝ) := by
    exact_mod_cast hownerNat
  have hexp :
      Real.exp (-(rate * (finBoxDist root.1 target.1 : ℝ))) ≤
        Real.exp (-(rate *
          (finBoxDist owner
            (cmp99Eq342SourceLocalizedActiveOwner L K Q depth target) : ℝ))) := by
    apply Real.exp_le_exp.mpr
    nlinarith [hrate.le, howner]
  have htail : 0 ≤
      Real.exp (rate * ((ell - 1 : ℕ) : ℝ)) *
        (ell : ℝ) ^ 2 * finitePiLpSupNorm f := by
    exact mul_nonneg
      (mul_nonneg (Real.exp_pos _).le (sq_nonneg _))
      (finitePiLpSupNorm_nonneg f)
  calc
    ‖cmp96SourceSeparatedRegionalPrefixGreen
        P hL depth hspacing ha background budget fineSmall hsmall cell f
        target‖ ≤
      (2 / c) * Real.exp (-(rate * (finBoxDist root.1 target.1 : ℝ))) *
        (Real.exp (rate * ((ell - 1 : ℕ) : ℝ)) *
          (ell : ℝ) ^ 2 * finitePiLpSupNorm f) := by
      simpa [ell, A, c, rate] using hfine
    _ ≤ (2 / c) *
        Real.exp (-(rate *
          (finBoxDist owner
            (cmp99Eq342SourceLocalizedActiveOwner L K Q depth target) : ℝ))) *
        (Real.exp (rate * ((ell - 1 : ℕ) : ℝ)) *
          (ell : ℝ) ^ 2 * finitePiLpSupNorm f) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hexp
          (div_nonneg (by positivity) hc.le))
        htail

end

end YangMills.RG
