/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq219RootedResummation

/-!
# From CMP116 equations (1.43) and (2.18) to the kernel in (2.19)

This module formalizes the scalar cancellation visible on the printed page 16
of CMP116.  Equation (1.43) supplies decay in the localization-domain metric
and in `|Y|`; equation (2.18) fixes the contour radius.  Their product cancels
`epsilon1` and `exp (C2 * kappa1)`.  The source conditions

* `C3 ≤ E0 * C1`,
* `8 ≤ q`, and
* `(1 - 3 * delta) * kappa ≤ (kappa1 - 1) / 8`

leave the coefficient `alpha4 * M⁻⁴` printed in (2.19).

The final conversion also exposes the independent geometric input that turns
one quarter of the `|Y|` decay into the internal bond-distance decay.  This is
deliberate: that geometric statement must be proved from the concrete CMP116
localization domains and is not hidden inside a renamed kernel hypothesis.
-/

namespace YangMills.RG

noncomputable section

/-- The right side of the printed inverse-radius identity (2.18). -/
noncomputable def cmp116Eq218TauInverse
    (E0 epsilon1 C1 alpha4 : ℝ) (M q : ℕ)
    (C2 kappa1 delta kappa domainDist : ℝ) : ℝ :=
  E0 * epsilon1 * C1 * alpha4⁻¹ * (M : ℝ) ^ q *
    Real.exp (C2 * kappa1) *
    Real.exp (-((1 - 3 * delta) * kappa * domainDist))

/-- The positive solution for `|tau(Y)|` obtained from (2.18). -/
noncomputable def cmp116Eq218TauAbsSolved
    (E0 epsilon1 C1 alpha4 : ℝ) (M q : ℕ)
    (C2 kappa1 delta kappa domainDist : ℝ) : ℝ :=
  alpha4 * (E0 * epsilon1 * C1)⁻¹ * ((M : ℝ) ^ q)⁻¹ *
    Real.exp (-(C2 * kappa1)) *
    Real.exp ((1 - 3 * delta) * kappa * domainDist)

/-- The exact scalar majorant printed in (1.43). -/
noncomputable def cmp116Eq143QMajorant
    (C3 epsilon1 : ℝ) (M : ℕ) (C2 kappa1 : ℝ)
    (domainDist : ℝ) (domainCard : ℕ) : ℝ :=
  C3 * epsilon1 * (M : ℝ) ^ 4 * Real.exp (C2 * kappa1) *
    Real.exp (-(1 / 8 : ℝ) * (kappa1 - 1) * domainDist -
      (1 / 2 : ℝ) * (kappa1 - 1) * ((M : ℝ) ^ 4)⁻¹ * domainCard)

/-- The explicit geometric budget needed to extract the internal-distance
factor of (2.19) while retaining one quarter of the `|Y|` decay. -/
def CMP116Eq219MetricBudget
    (M : ℕ) (kappa1 delta kappa domainDist : ℝ)
    (domainCard : ℕ) (bondDist : ℝ) : Prop :=
  (1 / 16 : ℝ) * (kappa1 - 1) * (M : ℝ)⁻¹ * bondDist ≤
    ((1 / 8 : ℝ) * (kappa1 - 1) - (1 - 3 * delta) * kappa) * domainDist +
      (1 / 4 : ℝ) * (kappa1 - 1) * ((M : ℝ) ^ 4)⁻¹ * domainCard

/-- The solved contour radius really has the inverse printed in (2.18). -/
theorem cmp116Eq218_tauAbsSolved_inv_eq_tauInverse
    {E0 epsilon1 C1 alpha4 C2 kappa1 delta kappa domainDist : ℝ}
    {M q : ℕ}
    (hE0 : E0 ≠ 0) (hepsilon1 : epsilon1 ≠ 0)
    (hC1 : C1 ≠ 0) (halpha4 : alpha4 ≠ 0) (hM : M ≠ 0) :
    (cmp116Eq218TauAbsSolved E0 epsilon1 C1 alpha4 M q
      C2 kappa1 delta kappa domainDist)⁻¹ =
      cmp116Eq218TauInverse E0 epsilon1 C1 alpha4 M q
        C2 kappa1 delta kappa domainDist := by
  have hMreal : (M : ℝ) ≠ 0 := by exact_mod_cast hM
  unfold cmp116Eq218TauAbsSolved cmp116Eq218TauInverse
  rw [Real.exp_neg, Real.exp_neg]
  field_simp [Real.exp_ne_zero]

/-- The source condition `q ≥ 8` turns the factor `M^(4-q)` into `M⁻⁴`. -/
theorem cmp116Eq218_blockPower_le
    {M q : ℕ} (hM : 1 ≤ M) (hq : 8 ≤ q) :
    (((M : ℝ) ^ q)⁻¹ * (M : ℝ) ^ 4) ≤ ((M : ℝ) ^ 4)⁻¹ := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hq
  rw [pow_add]
  have hM4pos : 0 < (M : ℝ) ^ 4 := by positivity
  have hMr : 1 ≤ (M : ℝ) ^ r := one_le_pow₀ (by exact_mod_cast hM)
  have hprod : (M : ℝ) ^ 4 ≤ (M : ℝ) ^ 4 * (M : ℝ) ^ r := by
    exact le_mul_of_one_le_right hM4pos.le hMr
  have hinv : ((M : ℝ) ^ 4 * (M : ℝ) ^ r)⁻¹ ≤
      ((M : ℝ) ^ 4)⁻¹ := by
    simpa [one_div] using one_div_le_one_div_of_le hM4pos hprod
  calc
    ((((M : ℝ) ^ 8 * (M : ℝ) ^ r)⁻¹) * (M : ℝ) ^ 4) =
        (((M : ℝ) ^ 4 * (M : ℝ) ^ r)⁻¹) := by field_simp
    _ ≤ ((M : ℝ) ^ 4)⁻¹ := hinv

/-- The printed scale inequality and a concrete domain-geometry estimate imply
the full metric budget.  The two inputs remain visibly distinct. -/
theorem cmp116Eq219_metricBudget_of_sourceConditions
    {M domainCard : ℕ}
    {kappa1 delta kappa domainDist bondDist : ℝ}
    (hdomainDist : 0 ≤ domainDist)
    (hkappa : (1 - 3 * delta) * kappa ≤
      (1 / 8 : ℝ) * (kappa1 - 1))
    (hgeometry :
      (1 / 16 : ℝ) * (kappa1 - 1) * (M : ℝ)⁻¹ * bondDist ≤
        (1 / 4 : ℝ) * (kappa1 - 1) *
          ((M : ℝ) ^ 4)⁻¹ * domainCard) :
    CMP116Eq219MetricBudget M kappa1 delta kappa
      domainDist domainCard bondDist := by
  unfold CMP116Eq219MetricBudget
  have hleftover :
      0 ≤ ((1 / 8 : ℝ) * (kappa1 - 1) -
        (1 - 3 * delta) * kappa) * domainDist :=
    mul_nonneg (sub_nonneg.mpr hkappa) hdomainDist
  linarith

/-- The exponent product from (1.43) and (2.18) is bounded by the two
separate exponentials printed in (2.19). -/
theorem cmp116Eq143Eq218_exponential_le_eq219
    {M domainCard : ℕ}
    {kappa1 delta kappa domainDist bondDist : ℝ}
    (hbudget : CMP116Eq219MetricBudget M kappa1 delta kappa
      domainDist domainCard bondDist) :
    Real.exp ((1 - 3 * delta) * kappa * domainDist) *
        Real.exp (-(1 / 8 : ℝ) * (kappa1 - 1) * domainDist -
          (1 / 2 : ℝ) * (kappa1 - 1) *
            ((M : ℝ) ^ 4)⁻¹ * domainCard) ≤
      Real.exp (-(1 / 4 : ℝ) * (kappa1 - 1) *
          ((M : ℝ) ^ 4)⁻¹ * domainCard) *
        Real.exp (-(1 / 16 : ℝ) * (kappa1 - 1) *
          (M : ℝ)⁻¹ * bondDist) := by
  unfold CMP116Eq219MetricBudget at hbudget
  rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  linarith

/-- Multiplying the solved contour radius (2.18) by the majorant (1.43)
produces exactly the two-layer kernel of (2.19). -/
theorem cmp116Eq143QMajorant_mul_tauAbsSolved_le_eq219
    {E0 epsilon1 C1 alpha4 C3 C2 kappa1 delta kappa : ℝ}
    {domainDist bondDist : ℝ} {M q domainCard : ℕ}
    (hE0 : 0 < E0) (hepsilon1 : 0 < epsilon1) (hC1 : 0 < C1)
    (halpha4 : 0 < alpha4) (hC3 : 0 ≤ C3)
    (hC3upper : C3 ≤ E0 * C1) (hM : 1 ≤ M) (hq : 8 ≤ q)
    (hbudget : CMP116Eq219MetricBudget M kappa1 delta kappa
      domainDist domainCard bondDist) :
    cmp116Eq218TauAbsSolved E0 epsilon1 C1 alpha4 M q
        C2 kappa1 delta kappa domainDist *
      cmp116Eq143QMajorant C3 epsilon1 M C2 kappa1
        domainDist domainCard ≤
      cmp116Eq219DomainAmplitude alpha4 M kappa1 domainCard *
        Real.exp (-(cmp116Eq219InternalRate M kappa1 * bondDist)) := by
  have hcoeff :
      (alpha4 * (E0 * epsilon1 * C1)⁻¹ * ((M : ℝ) ^ q)⁻¹) *
          (C3 * epsilon1 * (M : ℝ) ^ 4) ≤
        alpha4 * ((M : ℝ) ^ 4)⁻¹ := by
    have hcancel :
        (E0 * epsilon1 * C1)⁻¹ * (C3 * epsilon1) =
          C3 * (E0 * C1)⁻¹ := by field_simp
    have hdenom : 0 < E0 * C1 := mul_pos hE0 hC1
    have hratio : C3 * (E0 * C1)⁻¹ ≤ 1 := by
      rw [← div_eq_mul_inv]
      exact (div_le_one hdenom).2 hC3upper
    have hratio0 : 0 ≤ C3 * (E0 * C1)⁻¹ :=
      mul_nonneg hC3 (inv_nonneg.mpr hdenom.le)
    have hpow := cmp116Eq218_blockPower_le hM hq
    calc
      (alpha4 * (E0 * epsilon1 * C1)⁻¹ * ((M : ℝ) ^ q)⁻¹) *
            (C3 * epsilon1 * (M : ℝ) ^ 4) =
          alpha4 * (C3 * (E0 * C1)⁻¹) *
            (((M : ℝ) ^ q)⁻¹ * (M : ℝ) ^ 4) := by
              rw [← hcancel]
              ring
      _ ≤ alpha4 * 1 * ((M : ℝ) ^ 4)⁻¹ := by gcongr
      _ = alpha4 * ((M : ℝ) ^ 4)⁻¹ := by ring
  have hexp := cmp116Eq143Eq218_exponential_le_eq219 hbudget
  have hsourceFactor :
      cmp116Eq218TauAbsSolved E0 epsilon1 C1 alpha4 M q
          C2 kappa1 delta kappa domainDist *
        cmp116Eq143QMajorant C3 epsilon1 M C2 kappa1
          domainDist domainCard =
      ((alpha4 * (E0 * epsilon1 * C1)⁻¹ * ((M : ℝ) ^ q)⁻¹) *
          (C3 * epsilon1 * (M : ℝ) ^ 4)) *
        (Real.exp ((1 - 3 * delta) * kappa * domainDist) *
          Real.exp (-(1 / 8 : ℝ) * (kappa1 - 1) * domainDist -
            (1 / 2 : ℝ) * (kappa1 - 1) *
              ((M : ℝ) ^ 4)⁻¹ * domainCard)) := by
    unfold cmp116Eq218TauAbsSolved cmp116Eq143QMajorant
    rw [Real.exp_neg]
    field_simp [Real.exp_ne_zero]
  rw [hsourceFactor]
  calc
    ((alpha4 * (E0 * epsilon1 * C1)⁻¹ * ((M : ℝ) ^ q)⁻¹) *
          (C3 * epsilon1 * (M : ℝ) ^ 4)) *
        (Real.exp ((1 - 3 * delta) * kappa * domainDist) *
          Real.exp (-(1 / 8 : ℝ) * (kappa1 - 1) * domainDist -
            (1 / 2 : ℝ) * (kappa1 - 1) *
              ((M : ℝ) ^ 4)⁻¹ * domainCard)) ≤
      (alpha4 * ((M : ℝ) ^ 4)⁻¹) *
        (Real.exp ((1 - 3 * delta) * kappa * domainDist) *
          Real.exp (-(1 / 8 : ℝ) * (kappa1 - 1) * domainDist -
            (1 / 2 : ℝ) * (kappa1 - 1) *
              ((M : ℝ) ^ 4)⁻¹ * domainCard)) := by
      exact mul_le_mul_of_nonneg_right hcoeff
        (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
    _ ≤ (alpha4 * ((M : ℝ) ^ 4)⁻¹) *
        (Real.exp (-(1 / 4 : ℝ) * (kappa1 - 1) *
            ((M : ℝ) ^ 4)⁻¹ * domainCard) *
          Real.exp (-(1 / 16 : ℝ) * (kappa1 - 1) *
            (M : ℝ)⁻¹ * bondDist)) := by
      exact mul_le_mul_of_nonneg_left hexp
        (mul_nonneg halpha4.le (inv_nonneg.mpr (by positivity)))
    _ = cmp116Eq219DomainAmplitude alpha4 M kappa1 domainCard *
        Real.exp (-(cmp116Eq219InternalRate M kappa1 * bondDist)) := by
      unfold cmp116Eq219DomainAmplitude cmp116Eq219InternalRate
      ring_nf

/-- Physical wrapper: any nonnegative quantity satisfying (1.43), multiplied
by the contour radius fixed by (2.18), obeys the (2.19) kernel bound. -/
theorem cmp116Eq143_bound_mul_tauAbs_le_eq219
    {E0 epsilon1 C1 alpha4 C3 C2 kappa1 delta kappa : ℝ}
    {domainDist bondDist qAbs tauAbs : ℝ} {M q domainCard : ℕ}
    (hE0 : 0 < E0) (hepsilon1 : 0 < epsilon1) (hC1 : 0 < C1)
    (halpha4 : 0 < alpha4) (hC3 : 0 ≤ C3)
    (hC3upper : C3 ≤ E0 * C1) (hM : 1 ≤ M) (hq : 8 ≤ q)
    (hbudget : CMP116Eq219MetricBudget M kappa1 delta kappa
      domainDist domainCard bondDist)
    (htau : tauAbs = cmp116Eq218TauAbsSolved E0 epsilon1 C1 alpha4 M q
      C2 kappa1 delta kappa domainDist)
    (hQ143 : qAbs ≤ cmp116Eq143QMajorant C3 epsilon1 M C2 kappa1
      domainDist domainCard) :
    tauAbs * qAbs ≤
      cmp116Eq219DomainAmplitude alpha4 M kappa1 domainCard *
        Real.exp (-(cmp116Eq219InternalRate M kappa1 * bondDist)) := by
  rw [htau]
  calc
    cmp116Eq218TauAbsSolved E0 epsilon1 C1 alpha4 M q
        C2 kappa1 delta kappa domainDist * qAbs ≤
      cmp116Eq218TauAbsSolved E0 epsilon1 C1 alpha4 M q
          C2 kappa1 delta kappa domainDist *
        cmp116Eq143QMajorant C3 epsilon1 M C2 kappa1
          domainDist domainCard := by
      exact mul_le_mul_of_nonneg_left hQ143 (by
        unfold cmp116Eq218TauAbsSolved
        positivity)
    _ ≤ cmp116Eq219DomainAmplitude alpha4 M kappa1 domainCard *
        Real.exp (-(cmp116Eq219InternalRate M kappa1 * bondDist)) :=
      cmp116Eq143QMajorant_mul_tauAbsSolved_le_eq219
        hE0 hepsilon1 hC1 halpha4 hC3 hC3upper hM hq hbudget

end

end YangMills.RG
