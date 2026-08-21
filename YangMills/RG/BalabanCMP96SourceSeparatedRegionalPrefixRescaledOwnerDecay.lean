/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP96SourceSeparatedRegionalPrefixOwnerInputAction
import YangMills.RG.BalabanCMP99SourceLocalizationOwnerDistanceBridge

/-!
# Rescaled owner decay for the physical P8 regional Green

PRE-VALIDATION: source present, `.olean` not yet materialized, and the result
has not yet been verified by the Lean compiler.

The fine-lattice Combes--Thomas rate is not the rate printed in CMP99 (3.42).
The latter is measured in source-localization blocks of side
`ell = L^(depth+1)`.  This module applies the sealed inverse-scale distance
bridge

`ell * ownerDist <= fineDist + 2 * (ell - 1)`

and therefore exposes the correctly rescaled rate `ell * rate`.  The two
block-boundary payments from that bridge and the one source-fibre payment of
the preceding action theorem remain visible as the factor
`exp (3 * rate * (ell - 1))`.

This is still a per-depth endpoint.  It does not assert that the displayed
amplitude is bounded uniformly from above or that `ell * rate` is bounded
uniformly away from zero, and hence it is not the uniform `B0`/`delta0`
certificate of CMP99 (3.42).
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

variable {L K Q Nc : ℕ}
variable [NeZero L] [NeZero K] [NeZero Q] [NeZero Nc]

/-- The physical P8 Green on one source-owner input has the block-rescaled
rate `ell * rate`; all three boundary payments are explicit. -/
theorem norm_cmp96SourceSeparatedRegionalPrefixGreen_apply_le_rescaledOwnerScale
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
    let ownerRate := (ell : ℝ) * rate
    let ownerAmplitude := (2 / c) *
      Real.exp (3 * rate * ((ell - 1 : ℕ) : ℝ))
    ‖cmp96SourceSeparatedRegionalPrefixGreen
        (L := L) (K := K) (Q := Q) (Nc := Nc)
        P hL depth hspacing ha background budget fineSmall hsmall cell f
        target‖ ≤
      (ownerAmplitude * (ell : ℝ) ^ 2) *
        Real.exp (-(ownerRate *
          (finBoxDist owner
            (cmp99Eq342SourceLocalizedActiveOwner L K Q depth target) : ℝ))) *
        finitePiLpSupNorm f := by
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
  let ownerRate := (ell : ℝ) * rate
  let ownerAmplitude := (2 / c) *
    Real.exp (3 * rate * ((ell - 1 : ℕ) : ℝ))
  let ownerDist : ℝ :=
    (finBoxDist owner
      (cmp99Eq342SourceLocalizedActiveOwner L K Q depth target) : ℝ)
  let fineDist : ℝ := (finBoxDist root.1 target.1 : ℝ)
  let boundary : ℝ := ((ell - 1 : ℕ) : ℝ)
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
  have hbridgeNat :
      ell * finBoxDist owner
          (cmp99Eq342SourceLocalizedActiveOwner L K Q depth target) ≤
        finBoxDist root.1 target.1 + 2 * (ell - 1) := by
    rw [← hroot]
    simpa [ell, cmp99Eq342SourceLocalizedActiveOwner] using
      (cmp99Eq389SourceLocalizationOwner_mul_dist_le_fineDist_add_boundary
        (L := L) (K := K) (Q := Q) depth root.1 target.1)
  have hbridge : (ell : ℝ) * ownerDist ≤ fineDist + 2 * boundary := by
    exact_mod_cast hbridgeNat
  have hexponent :
      -(rate * fineDist) ≤
        2 * rate * boundary - ownerRate * ownerDist := by
    dsimp [ownerRate]
    nlinarith [hrate.le, hbridge]
  have hexp :
      Real.exp (-(rate * fineDist)) ≤
        Real.exp (2 * rate * boundary - ownerRate * ownerDist) :=
    Real.exp_le_exp.mpr hexponent
  have htail : 0 ≤
      Real.exp (rate * boundary) * (ell : ℝ) ^ 2 * finitePiLpSupNorm f := by
    exact mul_nonneg
      (mul_nonneg (Real.exp_pos _).le (sq_nonneg _))
      (finitePiLpSupNorm_nonneg f)
  have hbase :=
    norm_cmp96SourceSeparatedRegionalPrefixGreen_apply_le_sourceScale
      P hL depth hspacing ha hdecay background budget fineSmall hsmall cell
      owner root hroot f hf target
  calc
    ‖cmp96SourceSeparatedRegionalPrefixGreen
        P hL depth hspacing ha background budget fineSmall hsmall cell f
        target‖ ≤
      (2 / c) * Real.exp (-(rate * fineDist)) *
        (Real.exp (rate * boundary) *
          (ell : ℝ) ^ 2 * finitePiLpSupNorm f) := by
      simpa [ell, A, c, rate, fineDist, boundary] using hbase
    _ ≤ (2 / c) *
        Real.exp (2 * rate * boundary - ownerRate * ownerDist) *
        (Real.exp (rate * boundary) *
          (ell : ℝ) ^ 2 * finitePiLpSupNorm f) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hexp
          (div_nonneg (by positivity) hc.le)) htail
    _ = (ownerAmplitude * (ell : ℝ) ^ 2) *
        Real.exp (-(ownerRate * ownerDist)) * finitePiLpSupNorm f := by
      have hsplit :
          Real.exp (2 * rate * boundary - ownerRate * ownerDist) =
            Real.exp (2 * rate * boundary) *
              Real.exp (-(ownerRate * ownerDist)) := by
        rw [show 2 * rate * boundary - ownerRate * ownerDist =
          2 * rate * boundary + (-(ownerRate * ownerDist)) by ring,
          Real.exp_add]
      have hamp :
          Real.exp (2 * rate * boundary) * Real.exp (rate * boundary) =
            Real.exp (3 * rate * boundary) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [hsplit]
      dsimp [ownerAmplitude]
      rw [hamp]
      ring

end

end YangMills.RG
