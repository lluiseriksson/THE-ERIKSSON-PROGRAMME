/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq220ResidualLedger

/-!
# Equation-(2.26) with a source-generated residual ledger

The Gaussian volume factor only needs a nonnegative domain weight with a
rooted local-volume bound.  It does not depend on the closed form of that
weight.  This module exposes that invariant so the centered source residual
(`center value + contour displacement`) can be consumed without pretending
that it is only the displacement term used by the older route.
-/

namespace YangMills.RG

noncomputable section

/-- A nonnegative, rooted domain weight can replace the specialized
equation-(1.36) displacement weight in the final equation-(2.26) ledger. -/
theorem cmp116Eq226_boundaryProduct_le_sourceTermWeight_of_genericResidualLedger
    {Y I PIndex : Type*}
    [DecidableEq Y] [DecidableEq I] [DecidableEq PIndex]
    (D : Finset Y) (P : Finset PIndex) (Z0 : Finset I)
    (support : Y → Finset I) (weight : Y → ℝ)
    (domainMetric : Y → ℕ)
    {E0 epsilon1 C1 alpha4 : ℝ} {M q : ℕ}
    {C2 kappa1 delta kappa gamma2 gk threshold : ℝ}
    {L gapCard : ℕ}
    {rootBound baseRate Calpha5 alpha5 outerBound : ℝ}
    (hE0 : 0 ≤ E0) (hepsilon1 : 0 ≤ epsilon1)
    (hC1 : 0 ≤ C1) (halpha4 : 0 ≤ alpha4)
    (hgk : gk ≠ 0) (hthreshold : threshold = epsilon1 / gk)
    (houter : outerBound ≤ 1)
    (hweight : ∀ y ∈ D, 0 ≤ weight y)
    (hne : ∀ y ∈ D, (support y).Nonempty)
    (hsub : ∀ y ∈ D, support y ⊆ Z0)
    (hroot : ∀ i ∈ Z0,
      ∑ y ∈ D.filter (fun y => i ∈ support y), weight y ≤ rootBound)
    (hbudget : rootBound + baseRate ≤ Calpha5 * alpha5) :
    ((outerBound *
          Real.exp
            ((∑ y ∈ D, weight y) -
              gamma2 / 2 * threshold ^ 2 * (P.card : ℝ)) *
          Real.exp (baseRate * (Z0.card : ℝ))) *
        cmp116Eq226DomainProduct E0 epsilon1 C1 alpha4 M q
          C2 kappa1 delta kappa domainMetric D) *
        cmp116Eq226GapFactor kappa1 L M gapCard ≤
      cmp116Eq226SourceTermWeight E0 epsilon1 C1 alpha4 M q
        C2 kappa1 delta kappa gamma2 gk L gapCard
        Calpha5 alpha5 Z0.card domainMetric D P := by
  let residualSum := ∑ y ∈ D, weight y
  let domainProduct :=
    cmp116Eq226DomainProduct E0 epsilon1 C1 alpha4 M q
      C2 kappa1 delta kappa domainMetric D
  let pFactor := cmp116Eq226PBondFactor gamma2 epsilon1 gk P
  let gapFactor := cmp116Eq226GapFactor kappa1 L M gapCard
  let gaussianFactor :=
    cmp116Eq226GaussianVolumeFactor Calpha5 alpha5 Z0.card
  have hpenalty :
      Real.exp
          (residualSum - gamma2 / 2 * threshold ^ 2 * (P.card : ℝ)) =
        Real.exp residualSum * pFactor := by
    simpa [pFactor] using
      cmp116Eq222ResidualPenaltyFactor_eq_mul_eq226PBondFactor
        gamma2 epsilon1 gk threshold residualSum P hgk hthreshold
  have hresidual :
      residualSum ≤ rootBound * (Z0.card : ℝ) := by
    dsimp [residualSum]
    exact cmp116Eq136_rootedResidualResummation
      D Z0 support weight hweight hne hsub hroot
  have hvolume :
      Real.exp residualSum * Real.exp (baseRate * (Z0.card : ℝ)) ≤
        gaussianFactor := by
    dsimp [gaussianFactor]
    exact cmp116Eq226_exp_residual_mul_baseVolume_le_gaussianVolumeFactor
      Z0 residualSum rootBound baseRate Calpha5 alpha5 hresidual hbudget
  have hinside :
      outerBound *
          (Real.exp residualSum * Real.exp (baseRate * (Z0.card : ℝ))) ≤
        gaussianFactor := by
    calc
      outerBound *
          (Real.exp residualSum * Real.exp (baseRate * (Z0.card : ℝ))) ≤
          1 * (Real.exp residualSum *
            Real.exp (baseRate * (Z0.card : ℝ))) :=
        mul_le_mul_of_nonneg_right houter
          (mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _))
      _ ≤ gaussianFactor := by simpa using hvolume
  have hdomain : 0 ≤ domainProduct := by
    dsimp [domainProduct, cmp116Eq226DomainProduct]
    exact Finset.prod_nonneg fun y _ =>
      cmp116Eq226DomainFactor_nonneg hE0 hepsilon1 hC1 halpha4
  have hp : 0 ≤ pFactor := by
    dsimp [pFactor, cmp116Eq226PBondFactor]
    exact Real.exp_nonneg _
  have hgap : 0 ≤ gapFactor := by
    dsimp [gapFactor, cmp116Eq226GapFactor]
    exact Real.exp_nonneg _
  have hcommon : 0 ≤ gapFactor * domainProduct * pFactor := by positivity
  rw [hpenalty]
  change
    ((outerBound * (Real.exp residualSum * pFactor) *
          Real.exp (baseRate * (Z0.card : ℝ))) * domainProduct) *
        gapFactor ≤ _
  rw [show
    cmp116Eq226SourceTermWeight E0 epsilon1 C1 alpha4 M q
        C2 kappa1 delta kappa gamma2 gk L gapCard
        Calpha5 alpha5 Z0.card domainMetric D P =
      gapFactor * domainProduct * pFactor * gaussianFactor by rfl]
  calc
    ((outerBound * (Real.exp residualSum * pFactor) *
          Real.exp (baseRate * (Z0.card : ℝ))) * domainProduct) *
        gapFactor =
      (gapFactor * domainProduct * pFactor) *
        (outerBound *
          (Real.exp residualSum * Real.exp (baseRate * (Z0.card : ℝ)))) := by
            ring
    _ ≤ (gapFactor * domainProduct * pFactor) * gaussianFactor :=
      mul_le_mul_of_nonneg_left hinside hcommon

/-- Outer-determinant version of the generic residual ledger. -/
theorem cmp116Eq226_boundaryProduct_le_sourceTermWeight_of_genericResidualLedger_outerCard
    {Y I PIndex : Type*}
    [DecidableEq Y] [DecidableEq I] [DecidableEq PIndex]
    (D : Finset Y) (P : Finset PIndex) (Z0 : Finset I)
    (support : Y → Finset I) (weight : Y → ℝ)
    (domainMetric : Y → ℕ)
    {E0 epsilon1 C1 alpha4 : ℝ} {M q : ℕ}
    {C2 kappa1 delta kappa gamma2 gk threshold : ℝ}
    {L gapCard : ℕ}
    {rootBound baseRate outerCost Calpha5 alpha5 outerBound : ℝ}
    (hE0 : 0 ≤ E0) (hepsilon1 : 0 ≤ epsilon1)
    (hC1 : 0 ≤ C1) (halpha4 : 0 ≤ alpha4)
    (hgk : gk ≠ 0) (hthreshold : threshold = epsilon1 / gk)
    (houter :
      outerBound ≤ Real.exp (outerCost * (Z0.card : ℝ)))
    (hweight : ∀ y ∈ D, 0 ≤ weight y)
    (hne : ∀ y ∈ D, (support y).Nonempty)
    (hsub : ∀ y ∈ D, support y ⊆ Z0)
    (hroot : ∀ i ∈ Z0,
      ∑ y ∈ D.filter (fun y => i ∈ support y), weight y ≤ rootBound)
    (hbudget :
      rootBound + (baseRate + outerCost) ≤ Calpha5 * alpha5) :
    ((outerBound *
          Real.exp
            ((∑ y ∈ D, weight y) -
              gamma2 / 2 * threshold ^ 2 * (P.card : ℝ)) *
          Real.exp (baseRate * (Z0.card : ℝ))) *
        cmp116Eq226DomainProduct E0 epsilon1 C1 alpha4 M q
          C2 kappa1 delta kappa domainMetric D) *
        cmp116Eq226GapFactor kappa1 L M gapCard ≤
      cmp116Eq226SourceTermWeight E0 epsilon1 C1 alpha4 M q
        C2 kappa1 delta kappa gamma2 gk L gapCard
        Calpha5 alpha5 Z0.card domainMetric D P := by
  let residualPenalty :=
    Real.exp
      ((∑ y ∈ D, weight y) -
        gamma2 / 2 * threshold ^ 2 * (P.card : ℝ))
  let domainProduct :=
    cmp116Eq226DomainProduct E0 epsilon1 C1 alpha4 M q
      C2 kappa1 delta kappa domainMetric D
  let gapFactor := cmp116Eq226GapFactor kappa1 L M gapCard
  have hbase :
      outerBound * Real.exp (baseRate * (Z0.card : ℝ)) ≤
        Real.exp ((baseRate + outerCost) * (Z0.card : ℝ)) := by
    calc
      outerBound * Real.exp (baseRate * (Z0.card : ℝ)) ≤
          Real.exp (outerCost * (Z0.card : ℝ)) *
            Real.exp (baseRate * (Z0.card : ℝ)) :=
        mul_le_mul_of_nonneg_right houter (Real.exp_nonneg _)
      _ = Real.exp ((baseRate + outerCost) * (Z0.card : ℝ)) := by
        rw [← Real.exp_add]
        congr 1
        ring
  have hfront :
      outerBound * residualPenalty *
          Real.exp (baseRate * (Z0.card : ℝ)) ≤
        1 * residualPenalty *
          Real.exp ((baseRate + outerCost) * (Z0.card : ℝ)) := by
    calc
      outerBound * residualPenalty *
          Real.exp (baseRate * (Z0.card : ℝ)) =
        residualPenalty *
          (outerBound * Real.exp (baseRate * (Z0.card : ℝ))) := by ring
      _ ≤ residualPenalty *
          Real.exp ((baseRate + outerCost) * (Z0.card : ℝ)) :=
        mul_le_mul_of_nonneg_left hbase (Real.exp_nonneg _)
      _ = 1 * residualPenalty *
          Real.exp ((baseRate + outerCost) * (Z0.card : ℝ)) := by ring
  have hdomain : 0 ≤ domainProduct := by
    dsimp [domainProduct, cmp116Eq226DomainProduct]
    exact Finset.prod_nonneg fun y _ =>
      cmp116Eq226DomainFactor_nonneg hE0 hepsilon1 hC1 halpha4
  have hgap : 0 ≤ gapFactor := by
    dsimp [gapFactor, cmp116Eq226GapFactor]
    exact Real.exp_nonneg _
  calc
    ((outerBound * residualPenalty *
          Real.exp (baseRate * (Z0.card : ℝ))) * domainProduct) *
        gapFactor ≤
      ((1 * residualPenalty *
          Real.exp ((baseRate + outerCost) * (Z0.card : ℝ))) *
        domainProduct) * gapFactor :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hfront hdomain) hgap
    _ ≤ _ := by
      exact
        cmp116Eq226_boundaryProduct_le_sourceTermWeight_of_genericResidualLedger
          D P Z0 support weight domainMetric
          hE0 hepsilon1 hC1 halpha4 hgk hthreshold le_rfl
          hweight hne hsub hroot hbudget

end

end YangMills.RG
