/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP89SourceSeparatedPrefixCombesThomas

/-!
# Canonical tilted coercivity for the physical P8 regional prefix

This is the physical specialization deliberately left visible between the
generic canonical tilt theorem and the arbitrary-input inverse action.  The
operator is the literal P8 Dirichlet compression of the one P7 ambient prefix
precision; its localization, coercivity and exponential row sum are derived
from that same physical tower.  No regional precision and no tilted
coercivity witness is supplied by the caller.

PRE-VALIDATION (C6c.4d0): source is present, its `.olean` has not yet been
materialized, and the result is not yet verified by the Lean compiler.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

variable {L K Q Nc : ℕ}
variable [NeZero L] [NeZero K] [NeZero Q] [NeZero Nc]

/-- The exact P8 regional prefix precision retains half of its transported
coercivity after conjugation by the canonical rooted exponential tilt. -/
theorem isCoerciveCLM_cmp96SourceSeparatedRegionalPrefixPrecision_tilt_canonical
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
    let A := cmp89SourceSeparatedPrefixPrecisionUpperBound
        (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth
        spacing epsilon a background budget fineSmall *
      Real.exp (decay * (L ^ (depth + 1) : ℕ))
    let c := cmp89SourceSeparatedPrefixCoercivity
      (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth
      spacing epsilon a background budget fineSmall
    IsCoerciveCLM
      (finitePiLpTiltConjCLM
        (fun target source : ActiveGaugeRegion.Site
            (cmp96SourceSeparatedRegionalCell P L K Q depth cell) =>
          finBoxDist target.1 source.1)
        (finitePiLpExponentialInverseDecayRate A decay
          (cmp99OmegaSiteExpSumBound (decay / 4)) c)
        root
        (cmp96SourceSeparatedRegionalPrefixPrecision
          (L := L) (K := K) (Q := Q) (Nc := Nc)
          P hL depth spacing epsilon a background budget fineSmall cell))
      (c / 2) := by
  dsimp only
  let Omega := cmp96SourceSeparatedRegionalCell P L K Q depth cell
  let Kambient := cmp89SourceSeparatedAmbientPrefixPrecision
    (L := L) (K := K) (Q := Q) (Nc := Nc) hL depth
    spacing epsilon a background budget fineSmall
  let Kregional := cmp99RegionalDirichletPrecision Omega Kambient
  let A := cmp89SourceSeparatedPrefixPrecisionUpperBound hL depth
      spacing epsilon a background budget fineSmall *
    Real.exp (decay * (L ^ (depth + 1) : ℕ))
  let c := cmp89SourceSeparatedPrefixCoercivity hL depth
    spacing epsilon a background budget fineSmall
  have hc : 0 < c := by
    exact cmp89SourceSeparatedPrefixCoercivity_pos hL depth hspacing ha
      background budget fineSmall hsmall
  have hrow : 0 ≤ cmp99OmegaSiteExpSumBound (decay / 4) := by
    unfold cmp99OmegaSiteExpSumBound
    exact tsum_nonneg fun _ =>
      mul_nonneg (Nat.cast_nonneg _) (Real.exp_pos _).le
  have hKambient : FinitePiLpExponentialKernelBound Kambient
      (finBoxDist : FinBox 4
          (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)) →
        FinBox 4
          (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)) → ℕ)
      A decay := by
    exact cmp89SourceSeparatedAmbientPrefixPrecision_exponentialKernelBound
      hL depth hspacing hdecay background budget fineSmall
  have hKregional : FinitePiLpExponentialKernelBound Kregional
      (fun target source : ActiveGaugeRegion.Site Omega =>
        finBoxDist target.1 source.1) A decay := by
    exact cmp99RegionalDirichletPrecision_exponentialKernelBound
      Omega Kambient hKambient
  have hcoer : IsCoerciveCLM Kregional c := by
    exact isCoerciveCLM_cmp99RegionalDirichletPrecision Omega Kambient
      (isCoerciveCLM_cmp89SourceSeparatedAmbientPrefixPrecision
        hL depth hspacing ha background budget fineSmall hsmall)
  have hsum : ∀ target : ActiveGaugeRegion.Site Omega,
      ∑ source, Real.exp (-((decay / 4) *
        (finBoxDist target.1 source.1 : ℝ))) ≤
          cmp99OmegaSiteExpSumBound (decay / 4) := by
    intro target
    exact activeGaugeRegion_finBoxDist_exp_sum_le Omega target
      (div_pos hdecay (by norm_num))
  change IsCoerciveCLM
    (finitePiLpTiltConjCLM
      (fun target source : ActiveGaugeRegion.Site Omega =>
        finBoxDist target.1 source.1)
      (finitePiLpExponentialInverseDecayRate A decay
        (cmp99OmegaSiteExpSumBound (decay / 4)) c)
      root Kregional) (c / 2)
  exact isCoerciveCLM_finitePiLpTiltConj_inverse_canonical
    (fun target source : ActiveGaugeRegion.Site Omega =>
      finBoxDist target.1 source.1)
    (fun p q => finBoxDist_comm p.1 q.1)
    (fun p q r => finBoxDist_triangle p.1 q.1 r.1)
    Kregional hdecay hc hrow hKregional hcoer hsum root

end

end YangMills.RG
