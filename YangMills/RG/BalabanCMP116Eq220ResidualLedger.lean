/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq136To220
import YangMills.RG.BalabanCMP116Eq226SourceLedger

/-!
# Absorbing the CMP116 equation-(1.36) residual into the (2.26) volume ledger

The source estimate (1.36), after multiplication by the contour radius (2.18),
leaves the domain weight formalized in `cmp116Eq220ResidualDomainWeight`.
The rooted resummation bounds its sum by a constant times the localized volume.

This module performs the remaining exponential bookkeeping.  It combines that
localized residual cost with an already obtained Gaussian volume rate and
absorbs both into the single factor

`exp (C_alpha5 * alpha5 * |Z0|)`

printed in equation (2.26).  The only new condition is the literal scalar
budget saying that the two rates fit inside `C_alpha5 * alpha5`; no fieldwise
or residual majorant is introduced.
-/

namespace YangMills.RG

open Finset

noncomputable section

/-- Generic exponential absorption of a local-volume residual cost into the
equation-(2.26) Gaussian volume factor. -/
theorem cmp116Eq226_exp_residual_mul_baseVolume_le_gaussianVolumeFactor
    {I : Type*} [DecidableEq I]
    (Z0 : Finset I) (residualSum rootBound baseRate Calpha5 alpha5 : ℝ)
    (hresidual : residualSum ≤ rootBound * (Z0.card : ℝ))
    (hbudget : rootBound + baseRate ≤ Calpha5 * alpha5) :
    Real.exp residualSum *
        Real.exp (baseRate * (Z0.card : ℝ)) ≤
      cmp116Eq226GaussianVolumeFactor Calpha5 alpha5 Z0.card := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  calc
    residualSum + baseRate * (Z0.card : ℝ) ≤
        rootBound * (Z0.card : ℝ) +
          baseRate * (Z0.card : ℝ) :=
      add_le_add hresidual le_rfl
    _ = (rootBound + baseRate) * (Z0.card : ℝ) := by ring
    _ ≤ (Calpha5 * alpha5) * (Z0.card : ℝ) :=
      mul_le_mul_of_nonneg_right hbudget (Nat.cast_nonneg Z0.card)
    _ = Calpha5 * alpha5 * (Z0.card : ℝ) := by ring

/-- Source-shaped specialization: the literal residual-domain weights left by
(1.36)+(2.18), their rooted domain count, and the scalar allocation together
produce the final volume factor of (2.26).

The `hroot` premise is purely the source geometry/counting statement at one
coarse root.  In particular, it contains no field, residual function or
already exponentiated term bound. -/
theorem cmp116Eq220_residualDomainLedger_le_eq226GaussianVolumeFactor
    {Y I : Type*} [DecidableEq Y] [DecidableEq I]
    (D : Finset Y) (Z0 : Finset I)
    (support : Y → Finset I) (domainDist : Y → ℝ)
    {alpha4 delta kappa rootBound baseRate Calpha5 alpha5 : ℝ}
    (halpha4 : 0 ≤ alpha4)
    (hne : ∀ y ∈ D, (support y).Nonempty)
    (hsub : ∀ y ∈ D, support y ⊆ Z0)
    (hroot : ∀ i ∈ Z0,
      ∑ y ∈ D.filter (fun y => i ∈ support y),
          cmp116Eq220ResidualDomainWeight alpha4 delta kappa
            (domainDist y) ≤ rootBound)
    (hbudget : rootBound + baseRate ≤ Calpha5 * alpha5) :
    Real.exp
        (∑ y ∈ D,
          cmp116Eq220ResidualDomainWeight alpha4 delta kappa
            (domainDist y)) *
        Real.exp (baseRate * (Z0.card : ℝ)) ≤
      cmp116Eq226GaussianVolumeFactor Calpha5 alpha5 Z0.card := by
  apply cmp116Eq226_exp_residual_mul_baseVolume_le_gaussianVolumeFactor
    Z0 _ rootBound baseRate Calpha5 alpha5
  · exact cmp116Eq220_residualDomainWeight_sum_le_localVolume
      D Z0 support domainDist halpha4 hne hsub hroot
  · exact hbudget

/-- Equivalent form with the two exponential costs already combined.  This is
the form used when the physical boundary theorem has accumulated both costs in
one real exponent before applying `Real.exp`. -/
theorem cmp116Eq220_exp_residual_add_baseVolume_le_eq226GaussianVolumeFactor
    {Y I : Type*} [DecidableEq Y] [DecidableEq I]
    (D : Finset Y) (Z0 : Finset I)
    (support : Y → Finset I) (domainDist : Y → ℝ)
    {alpha4 delta kappa rootBound baseRate Calpha5 alpha5 : ℝ}
    (halpha4 : 0 ≤ alpha4)
    (hne : ∀ y ∈ D, (support y).Nonempty)
    (hsub : ∀ y ∈ D, support y ⊆ Z0)
    (hroot : ∀ i ∈ Z0,
      ∑ y ∈ D.filter (fun y => i ∈ support y),
          cmp116Eq220ResidualDomainWeight alpha4 delta kappa
            (domainDist y) ≤ rootBound)
    (hbudget : rootBound + baseRate ≤ Calpha5 * alpha5) :
    Real.exp
        ((∑ y ∈ D,
          cmp116Eq220ResidualDomainWeight alpha4 delta kappa
            (domainDist y)) + baseRate * (Z0.card : ℝ)) ≤
      cmp116Eq226GaussianVolumeFactor Calpha5 alpha5 Z0.card := by
  rw [Real.exp_add]
  exact cmp116Eq220_residualDomainLedger_le_eq226GaussianVolumeFactor
    D Z0 support domainDist halpha4 hne hsub hroot hbudget

/-- Complete scalar landing in the literal equation-(2.26) term weight.

This theorem simultaneously:

* rewrites the cutoff loss using the physical threshold `epsilon1 / gk`;
* absorbs the rooted (1.36) residual and the pre-existing Gaussian rate into
  the declared `C_alpha5 * alpha5` volume budget;
* retains the exact `D`, `P` and gap factors of the source ledger.

Thus a physical term estimate with the left-hand shape below can be compared
to `cmp116Eq226SourceTermWeight` without an arbitrary residual scalar or a
post-hoc term weight. -/
theorem cmp116Eq226_boundaryProduct_le_sourceTermWeight_of_residualLedger
    {Y I PIndex : Type*}
    [DecidableEq Y] [DecidableEq I] [DecidableEq PIndex]
    (D : Finset Y) (P : Finset PIndex) (Z0 : Finset I)
    (support : Y → Finset I)
    (domainDist : Y → ℝ) (domainMetric : Y → ℕ)
    {E0 epsilon1 C1 alpha4 : ℝ} {M q : ℕ}
    {C2 kappa1 delta kappa gamma2 gk threshold : ℝ}
    {L gapCard : ℕ}
    {rootBound baseRate Calpha5 alpha5 outerBound : ℝ}
    (hE0 : 0 ≤ E0) (hepsilon1 : 0 ≤ epsilon1)
    (hC1 : 0 ≤ C1) (halpha4 : 0 ≤ alpha4)
    (hgk : gk ≠ 0) (hthreshold : threshold = epsilon1 / gk)
    (houter : outerBound ≤ 1)
    (hne : ∀ y ∈ D, (support y).Nonempty)
    (hsub : ∀ y ∈ D, support y ⊆ Z0)
    (hroot : ∀ i ∈ Z0,
      ∑ y ∈ D.filter (fun y => i ∈ support y),
          cmp116Eq220ResidualDomainWeight alpha4 delta kappa
            (domainDist y) ≤ rootBound)
    (hbudget : rootBound + baseRate ≤ Calpha5 * alpha5) :
    ((outerBound *
          Real.exp
            ((∑ y ∈ D,
              cmp116Eq220ResidualDomainWeight alpha4 delta kappa
                (domainDist y)) -
              gamma2 / 2 * threshold ^ 2 * (P.card : ℝ)) *
          Real.exp (baseRate * (Z0.card : ℝ))) *
        cmp116Eq226DomainProduct E0 epsilon1 C1 alpha4 M q
          C2 kappa1 delta kappa domainMetric D) *
        cmp116Eq226GapFactor kappa1 L M gapCard ≤
      cmp116Eq226SourceTermWeight E0 epsilon1 C1 alpha4 M q
        C2 kappa1 delta kappa gamma2 gk L gapCard
        Calpha5 alpha5 Z0.card domainMetric D P := by
  let residualSum :=
    ∑ y ∈ D,
      cmp116Eq220ResidualDomainWeight alpha4 delta kappa (domainDist y)
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
  have hvolume :
      Real.exp residualSum * Real.exp (baseRate * (Z0.card : ℝ)) ≤
        gaussianFactor := by
    dsimp [residualSum, gaussianFactor]
    exact cmp116Eq220_residualDomainLedger_le_eq226GaussianVolumeFactor
      D Z0 support domainDist halpha4 hne hsub hroot hbudget
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

/-- The determinant/Jacobian normalization may have a localized exponential
cost rather than being bounded by one.  This variant absorbs
`outerBound ≤ exp (outerCost * |Z₀|)` into the same volume ledger, without
introducing any dependence on the ambient volume. -/
theorem cmp116Eq226_boundaryProduct_le_sourceTermWeight_of_residualLedger_outerCard
    {Y I PIndex : Type*}
    [DecidableEq Y] [DecidableEq I] [DecidableEq PIndex]
    (D : Finset Y) (P : Finset PIndex) (Z0 : Finset I)
    (support : Y → Finset I)
    (domainDist : Y → ℝ) (domainMetric : Y → ℕ)
    {E0 epsilon1 C1 alpha4 : ℝ} {M q : ℕ}
    {C2 kappa1 delta kappa gamma2 gk threshold : ℝ}
    {L gapCard : ℕ}
    {rootBound baseRate outerCost Calpha5 alpha5 outerBound : ℝ}
    (hE0 : 0 ≤ E0) (hepsilon1 : 0 ≤ epsilon1)
    (hC1 : 0 ≤ C1) (halpha4 : 0 ≤ alpha4)
    (hgk : gk ≠ 0) (hthreshold : threshold = epsilon1 / gk)
    (houter :
      outerBound ≤ Real.exp (outerCost * (Z0.card : ℝ)))
    (hne : ∀ y ∈ D, (support y).Nonempty)
    (hsub : ∀ y ∈ D, support y ⊆ Z0)
    (hroot : ∀ i ∈ Z0,
      ∑ y ∈ D.filter (fun y => i ∈ support y),
          cmp116Eq220ResidualDomainWeight alpha4 delta kappa
            (domainDist y) ≤ rootBound)
    (hbudget :
      rootBound + (baseRate + outerCost) ≤ Calpha5 * alpha5) :
    ((outerBound *
          Real.exp
            ((∑ y ∈ D,
              cmp116Eq220ResidualDomainWeight alpha4 delta kappa
                (domainDist y)) -
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
      ((∑ y ∈ D,
        cmp116Eq220ResidualDomainWeight alpha4 delta kappa
          (domainDist y)) -
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
        cmp116Eq226_boundaryProduct_le_sourceTermWeight_of_residualLedger
          D P Z0 support domainDist domainMetric
          hE0 hepsilon1 hC1 halpha4 hgk hthreshold le_rfl
          hne hsub hroot hbudget

end

end YangMills.RG
