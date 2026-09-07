/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP96SourceSeparatedRegionalPrefixTiltedCoercivity
import YangMills.RG.BalabanCMP99Eq342SourceOwnerTiltedInput

/-!
# Physical P8 Green action on one source-owner input

This module composes the exact P8 inverse identity and canonical tilted
coercivity with the already sealed source-owner tilted-input estimate.  The
caller supplies neither a regional precision nor a tilted-coercivity witness,
and the one permitted counting-to-sup conversion is spent exactly once.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

variable {L K Q Nc : ℕ}
variable [NeZero L] [NeZero K] [NeZero Q] [NeZero Nc]

/-- The exact P8 Green acts on one source-owner input without expanding that
input into coordinate probes. -/
theorem norm_cmp96SourceSeparatedRegionalPrefixGreen_apply_le_sourceScale
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
      (2 / c) * Real.exp (-(rate * (finBoxDist root.1 target.1 : ℝ))) *
        (Real.exp (rate * ((ell - 1 : ℕ) : ℝ)) *
          (ell : ℝ) ^ 2 * finitePiLpSupNorm f) := by
  dsimp only
  let Omega := cmp96SourceSeparatedRegionalCell P L K Q depth cell
  let Kregional := cmp96SourceSeparatedRegionalPrefixPrecision
    P hL depth spacing epsilon a background budget fineSmall cell
  let Cregional := cmp96SourceSeparatedRegionalPrefixGreen
    P hL depth hspacing ha background budget fineSmall hsmall cell
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
  have hKC : Kregional.comp Cregional = ContinuousLinearMap.id ℝ _ := by
    exact cmp96SourceSeparatedRegionalPrefixPrecision_comp_green
      P hL depth hspacing ha background budget fineSmall hsmall cell
  have htilt : IsCoerciveCLM
      (finitePiLpTiltConjCLM
        (fun target source : ActiveGaugeRegion.Site Omega =>
          finBoxDist target.1 source.1)
        rate root Kregional) (c / 2) := by
    exact
      isCoerciveCLM_cmp96SourceSeparatedRegionalPrefixPrecision_tilt_canonical
        P hL depth hspacing ha hdecay background budget fineSmall hsmall cell
        root
  have haction := norm_finitePiLpInverse_apply_le_of_tilted_coercive
    (fun target source : ActiveGaugeRegion.Site Omega =>
      finBoxDist target.1 source.1)
    hc Kregional Cregional hKC root htilt f target
  have hinput := norm_cmp99Eq342_sourceLocalizedTilt_le_sourceScale
    (L := L) (K := K) (Q := Q) (Nc := Nc)
    depth Omega owner root hroot hrate.le f hf
  calc
    ‖Cregional f target‖ ≤
        (2 / c) * Real.exp (-(rate * (finBoxDist root.1 target.1 : ℝ))) *
          ‖finitePiLpTiltCLM (g := SUNLieCoord Nc)
            (fun target source : ActiveGaugeRegion.Site Omega =>
              finBoxDist target.1 source.1)
            rate root f‖ := haction
    _ ≤ (2 / c) * Real.exp (-(rate * (finBoxDist root.1 target.1 : ℝ))) *
        (Real.exp (rate * ((ell - 1 : ℕ) : ℝ)) *
          (ell : ℝ) ^ 2 * finitePiLpSupNorm f) := by
      simpa [ell] using
        mul_le_mul_of_nonneg_left hinput
          (mul_nonneg (div_nonneg (by positivity) hc.le)
            (Real.exp_pos _).le)

end

end YangMills.RG
