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

end

end YangMills.RG
