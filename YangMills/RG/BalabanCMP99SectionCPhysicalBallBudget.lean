/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SectionCFirstVerifiedSpecies

/-!
# The explicit physical ball budget in the CMP99 Section-C shell estimate

The source-facing precision-shell theorem previously exposed a real constant
`NR` together with the assertion that every radius-`R` physical-bond ball has
cardinality at most `NR`.  The physical bond metric already supplies the
volume-uniform count

`#{q : physicalBondDist p q ≤ R} ≤ (2 * (R + 1)) ^ d * d`.

This file inserts that count into the bilateral covariance estimate and into
the first verified Section-C label.  Thus neither endpoint accepts an abstract
ball budget or a renamed ball-count hypothesis.
-/

namespace YangMills.RG

noncomputable section

private abbrev PhysicalEndomorphism (d N Nc : ℕ) [NeZero N] :=
  PhysicalGaugeOneCochain d N Nc →L[ℝ]
    PhysicalGaugeOneCochain d N Nc

/-- The explicit, volume-independent number of oriented physical bonds in the
radius-`R` counting budget used by the shell estimate. -/
def cmp99PhysicalBondRangeBallBudget (d R : ℕ) : ℕ :=
  (2 * (R + 1)) ^ d * d

/-- The physical bond-distance ball is bounded by the literal CMP99 budget.
The orientation in the filter is the one consumed by the shell theorem. -/
theorem physicalBondDist_ball_card_le_cmp99PhysicalBondRangeBallBudget
    {d N : ℕ} [NeZero N] (source : PhysicalBond d N) (R : ℕ) :
    (Finset.univ.filter (fun target : PhysicalBond d N =>
      physicalBondDist target source ≤ R)).card ≤
        cmp99PhysicalBondRangeBallBudget d R := by
  simpa only [physicalBondDist_comm, cmp99PhysicalBondRangeBallBudget] using
    (physicalBondDist_ball_card_le source R)

/-- Common-collar bilateral decay with the physical ball count generated
internally.  No `NR` or `hball` remains in the public interface. -/
theorem cmp99SectionCCovarianceDifference_bilateralDecay_of_commonShellGap_physicalBallBudget
    {d N Nc : ℕ} [NeZero N]
    (K : PhysicalEndomorphism d N Nc)
    {S1 S0 : Finset (PhysicalBond d N)} (hsub : S1 ⊆ S0)
    (R : ℕ) (hrange : PhysicalCovarianceFiniteRange K physicalBondDist R)
    {CK c mass A0 A1 mu : ℝ}
    (hCK : 0 ≤ CK)
    (hkernel : PhysicalCovarianceKernelBound K (fun _ _ => CK))
    (hc : 0 < c) (hmass : 0 < mass) (hcoercive : IsCoerciveCLM K c)
    (hC0 : PhysicalCovarianceExponentialKernelBound
      (cmp99LocalizedPhysicalCovariance K S0 hc hmass hcoercive)
      physicalBondDist A0 mu)
    (hC1 : PhysicalCovarianceExponentialKernelBound
      (cmp99LocalizedPhysicalCovariance K S1 hc hmass hcoercive)
      physicalBondDist A1 mu)
    {source target : PhysicalBond d N} {L : ℕ}
    (htarget : target ∈ cmp99PhysicalBondShellGap
      physicalBondDist (S0 \ S1) R L)
    (hsource : source ∈ cmp99PhysicalBondShellGap
      physicalBondDist (S0 \ S1) R L)
    (v0 : SUNLieCoord Nc) :
    ‖cmp99SectionCCovarianceDifference K S0 S1 hc hmass hcoercive
        (singlePhysicalBondCochain source v0) target‖ ≤
      A0 * A1 *
        ((3 * CK * (cmp99PhysicalBondRangeBallBudget d R : ℝ) + |mass|) *
          (S0 \ S1).card) *
        Real.exp (-(2 * mu * (L : ℝ))) * ‖v0‖ := by
  apply cmp99SectionCCovarianceDifference_bilateralDecay_of_commonShellGap
    K hsub R hrange hCK (by positivity) hkernel
      (fun source' => ?_) hc hmass hcoercive hC0 hC1 htarget hsource v0
  exact_mod_cast
    physicalBondDist_ball_card_le_cmp99PhysicalBondRangeBallBudget source' R

namespace CMP99SectionCPointedFactorDictionary

/-- The verified covariance-difference label inherits common-collar decay
with the literal physical ball budget.  The open species remain untouched. -/
theorem norm_Rop_covarianceDifferenceLabel_le_of_commonShellGap_physicalBallBudget
    {Other : Type*} {Q S d N Nc : ℕ}
    [NeZero Q] [NeZero S] [NeZero N]
    (Base : CMP99SectionCPointedFactorDictionary Other Q S
      (PhysicalEndomorphism d N Nc))
    (K : PhysicalEndomorphism d N Nc)
    (S0 S1 : CMP99SimpleLocalizationDomain
      (cmp116CoarseFaceAdj 4 Q) S → Finset (PhysicalBond d N))
    (X : CMP99SimpleLocalizationDomain (cmp116CoarseFaceAdj 4 Q) S)
    (hsub : S1 X ⊆ S0 X)
    (R : ℕ) (hrange : PhysicalCovarianceFiniteRange K physicalBondDist R)
    {CK c mass A0 A1 mu : ℝ}
    (hCK : 0 ≤ CK)
    (hkernel : PhysicalCovarianceKernelBound K (fun _ _ => CK))
    (hc : 0 < c) (hmass : 0 < mass) (hcoercive : IsCoerciveCLM K c)
    (hC0 : PhysicalCovarianceExponentialKernelBound
      (cmp99LocalizedPhysicalCovariance K (S0 X) hc hmass hcoercive)
      physicalBondDist A0 mu)
    (hC1 : PhysicalCovarianceExponentialKernelBound
      (cmp99LocalizedPhysicalCovariance K (S1 X) hc hmass hcoercive)
      physicalBondDist A1 mu)
    {source target : PhysicalBond d N} {L : ℕ}
    (htarget : target ∈ cmp99PhysicalBondShellGap
      physicalBondDist (S0 X \ S1 X) R L)
    (hsource : source ∈ cmp99PhysicalBondShellGap
      physicalBondDist (S0 X \ S1 X) R L)
    (v0 : SUNLieCoord Nc) :
    ‖(Base.withCovarianceDifference K S0 S1 hc hmass hcoercive).Rop
        cmp99SectionCCovarianceDifferenceLabel X
        (singlePhysicalBondCochain source v0) target‖ ≤
      A0 * A1 *
        ((3 * CK * (cmp99PhysicalBondRangeBallBudget d R : ℝ) + |mass|) *
          (S0 X \ S1 X).card) *
        Real.exp (-(2 * mu * (L : ℝ))) * ‖v0‖ := by
  simpa using
    (cmp99SectionCCovarianceDifference_bilateralDecay_of_commonShellGap_physicalBallBudget
      K hsub R hrange hCK hkernel hc hmass hcoercive hC0 hC1
        htarget hsource v0)

end CMP99SectionCPointedFactorDictionary

end

end YangMills.RG
