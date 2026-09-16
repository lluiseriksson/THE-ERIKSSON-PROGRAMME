/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq226SourceLedger
import YangMills.RG.BalabanCMP116Eq229

/-!
# The literal domain-product extraction in CMP116 equation (2.28)

After extracting

`alpha6 * exp (-delta * kappa * d_k(Y))`

from every domain factor in equation (2.26), the source leaves one explicit
residual amplitude and uses equation (2.27) to absorb all remaining copies.
This module formalizes that finite-product argument without defining the
residual as a quotient of the original product.
-/

namespace YangMills.RG

open scoped BigOperators

noncomputable section

/-- The source coefficient left after extracting one `alpha6` from a domain
factor in equation (2.26). -/
def cmp116Eq228SourceCoefficient
    (E0 epsilon1 C1 alpha4 alpha6 : ℝ) (M q : ℕ)
    (C2 kappa1 : ℝ) : ℝ :=
  2 * E0 * epsilon1 * C1 * alpha4⁻¹ * alpha6⁻¹ *
    (M : ℝ) ^ q * Real.exp (C2 * kappa1)

/-- The residual factor printed on the second line of equation (2.28). -/
def cmp116Eq228Residual
    (E0 epsilon1 C1 alpha4 alpha6 : ℝ) (M q : ℕ)
    (C2 kappa1 delta kappa metric : ℝ) : ℝ :=
  cmp116Eq228SourceCoefficient
      E0 epsilon1 C1 alpha4 alpha6 M q C2 kappa1 *
    Real.exp (-((1 - 4 * delta) * kappa * metric))

/-- Positivity of the explicit source coefficient under the physical sign
conditions. -/
theorem cmp116Eq228SourceCoefficient_nonneg
    (E0 epsilon1 C1 alpha4 alpha6 : ℝ) (M q : ℕ)
    (C2 kappa1 : ℝ)
    (hE0 : 0 ≤ E0) (hepsilon1 : 0 ≤ epsilon1)
    (hC1 : 0 ≤ C1) (halpha4 : 0 < alpha4)
    (halpha6 : 0 < alpha6) :
    0 ≤
      cmp116Eq228SourceCoefficient
        E0 epsilon1 C1 alpha4 alpha6 M q C2 kappa1 := by
  unfold cmp116Eq228SourceCoefficient
  positivity

/-- The residual decay never exceeds its explicit source coefficient. -/
theorem cmp116Eq228Residual_le_sourceCoefficient
    (E0 epsilon1 C1 alpha4 alpha6 : ℝ) (M q : ℕ)
    (C2 kappa1 delta kappa metric : ℝ)
    (hcoeff :
      0 ≤
        cmp116Eq228SourceCoefficient
          E0 epsilon1 C1 alpha4 alpha6 M q C2 kappa1)
    (hkappa : 0 ≤ kappa)
    (hfourDelta : 4 * delta ≤ 1) (hmetric : 0 ≤ metric) :
    cmp116Eq228Residual
        E0 epsilon1 C1 alpha4 alpha6 M q C2 kappa1
        delta kappa metric ≤
      cmp116Eq228SourceCoefficient
        E0 epsilon1 C1 alpha4 alpha6 M q C2 kappa1 := by
  unfold cmp116Eq228Residual
  calc
    cmp116Eq228SourceCoefficient
          E0 epsilon1 C1 alpha4 alpha6 M q C2 kappa1 *
        Real.exp (-((1 - 4 * delta) * kappa * metric)) ≤
      cmp116Eq228SourceCoefficient
          E0 epsilon1 C1 alpha4 alpha6 M q C2 kappa1 *
        1 := by
      apply mul_le_mul_of_nonneg_left ?_ hcoeff
      calc
        Real.exp (-((1 - 4 * delta) * kappa * metric)) ≤
            Real.exp 0 := by
          apply Real.exp_le_exp.mpr
          exact neg_nonpos.mpr
            (mul_nonneg
              (mul_nonneg (sub_nonneg.mpr hfourDelta) hkappa)
              hmetric)
        _ = 1 := Real.exp_zero
    _ =
      cmp116Eq228SourceCoefficient
        E0 epsilon1 C1 alpha4 alpha6 M q C2 kappa1 := by ring

/-- Exact pointwise extraction of the equation-(2.29) fugacity from the
literal equation-(2.26) domain factor. -/
theorem cmp116Eq226DomainFactor_eq_eq229Weight_mul_eq228Residual
    {ιY : Type*}
    {E0 epsilon1 C1 alpha4 alpha6 : ℝ} {M q : ℕ}
    {C2 kappa1 delta kappa : ℝ}
    {domainMetric : ιY → ℕ} {Y : ιY}
    (halpha6 : alpha6 ≠ 0) :
    cmp116Eq226DomainFactor
        E0 epsilon1 C1 alpha4 M q C2 kappa1 delta kappa
        domainMetric Y =
      cmp116Eq229Weight alpha6 delta kappa domainMetric Y *
        cmp116Eq228Residual
          E0 epsilon1 C1 alpha4 alpha6 M q C2 kappa1
          delta kappa (domainMetric Y : ℝ) := by
  unfold cmp116Eq226DomainFactor cmp116Eq229Weight
    cmp116Eq228Residual cmp116Eq228SourceCoefficient
  have hexp :
      Real.exp
          (-((1 - 3 * delta) * kappa * (domainMetric Y : ℝ))) =
        Real.exp (-(delta * kappa * (domainMetric Y : ℝ))) *
          Real.exp
            (-((1 - 4 * delta) * kappa *
              (domainMetric Y : ℝ))) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hexp]
  field_simp

/-- Algebraic core of equation (2.28).

One residual copy is retained.  Every other copy is absorbed by the source
smallness condition, while the shifted metric inequality (2.27) supplies the
needed five units per additional domain.  Nonemptiness is essential because
the empty product need not be bounded by a small residual. -/
theorem cmp116Eq228_residualProduct_le
    {ιY : Type*} [DecidableEq ιY]
    (D : Finset ιY) (hD : D.Nonempty)
    (metric : ιY → ℝ) (unionMetric A delta kappa : ℝ)
    (hA : 0 ≤ A) (hdelta : 0 ≤ delta) (hkappa : 0 ≤ kappa)
    (hfourDelta : 4 * delta ≤ 1)
    (hsmall : A * Real.exp (5 * kappa) ≤ 1)
    (hEq227 :
      unionMetric + 5 ≤ ∑ Y ∈ D, (metric Y + 5)) :
    (∏ Y ∈ D,
        A * Real.exp (-((1 - 4 * delta) * kappa * metric Y))) ≤
      A *
        Real.exp (-((1 - 4 * delta) * kappa * unionMetric)) := by
  classical
  let lambda : ℝ := (1 - 4 * delta) * kappa
  have hlambda_nonneg : 0 ≤ lambda := by
    exact mul_nonneg (sub_nonneg.mpr hfourDelta) hkappa
  have hlambda_le : lambda ≤ kappa := by
    change (1 - 4 * delta) * kappa ≤ kappa
    calc
      (1 - 4 * delta) * kappa =
          kappa - 4 * (delta * kappa) := by ring
      _ ≤ kappa :=
        sub_le_self _ (mul_nonneg (by norm_num) (mul_nonneg hdelta hkappa))
  have hA_le_kappa : A ≤ Real.exp (-(5 * kappa)) := by
    have hdiv :
        A ≤ 1 / Real.exp (5 * kappa) :=
      (le_div_iff₀ (Real.exp_pos (5 * kappa))).2 hsmall
    simpa [Real.exp_neg] using hdiv
  have hA_le_lambda : A ≤ Real.exp (-(5 * lambda)) := by
    exact hA_le_kappa.trans
      (Real.exp_le_exp.mpr (by linarith))
  obtain ⟨Y, hYD⟩ := hD
  have hYerase : Y ∉ D.erase Y := by simp
  have hDinsert : insert Y (D.erase Y) = D :=
    Finset.insert_erase hYD
  have hmetric :
      unionMetric ≤
        metric Y + ∑ Z ∈ D.erase Y, (metric Z + 5) := by
    rw [← hDinsert] at hEq227
    simp only [Finset.sum_insert, hYerase, not_false_eq_true] at hEq227
    linarith
  have hfactor :
      ∀ Z ∈ D.erase Y,
        A * Real.exp (-(lambda * metric Z)) ≤
          Real.exp (-(lambda * (metric Z + 5))) := by
    intro Z _hZ
    calc
      A * Real.exp (-(lambda * metric Z)) ≤
          Real.exp (-(5 * lambda)) *
            Real.exp (-(lambda * metric Z)) := by
        exact mul_le_mul_of_nonneg_right hA_le_lambda (Real.exp_nonneg _)
      _ = Real.exp (-(lambda * (metric Z + 5))) := by
        rw [← Real.exp_add]
        congr 1
        ring
  have hrest :
      (∏ Z ∈ D.erase Y,
          A * Real.exp (-(lambda * metric Z))) ≤
        Real.exp
          (-(lambda * ∑ Z ∈ D.erase Y, (metric Z + 5))) := by
    calc
      (∏ Z ∈ D.erase Y,
          A * Real.exp (-(lambda * metric Z))) ≤
        ∏ Z ∈ D.erase Y,
          Real.exp (-(lambda * (metric Z + 5))) := by
            exact Finset.prod_le_prod
              (fun _ _ => mul_nonneg hA (Real.exp_nonneg _))
              hfactor
      _ =
        Real.exp
          (∑ Z ∈ D.erase Y, -(lambda * (metric Z + 5))) := by
            rw [Real.exp_sum]
      _ =
        Real.exp
          (-(lambda * ∑ Z ∈ D.erase Y, (metric Z + 5))) := by
            congr 1
            have hsum :
                (∑ Z ∈ D.erase Y, -(lambda * (metric Z + 5))) =
                  (-lambda) * ∑ Z ∈ D.erase Y, (metric Z + 5) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro Z _hZ
              ring
            rw [hsum]
            ring
  rw [← hDinsert, Finset.prod_insert hYerase]
  change
    (A * Real.exp (-(lambda * metric Y))) *
        (∏ Z ∈ D.erase Y,
          A * Real.exp (-(lambda * metric Z))) ≤
      A * Real.exp (-(lambda * unionMetric))
  calc
    (A * Real.exp (-(lambda * metric Y))) *
        (∏ Z ∈ D.erase Y,
          A * Real.exp (-(lambda * metric Z))) ≤
      (A * Real.exp (-(lambda * metric Y))) *
        Real.exp
          (-(lambda * ∑ Z ∈ D.erase Y, (metric Z + 5))) := by
            exact mul_le_mul_of_nonneg_left hrest
              (mul_nonneg hA (Real.exp_nonneg _))
    _ =
      A *
        Real.exp
          (-(lambda *
            (metric Y + ∑ Z ∈ D.erase Y, (metric Z + 5)))) := by
          rw [mul_assoc, ← Real.exp_add]
          congr 1
          ring
    _ ≤ A * Real.exp (-(lambda * unionMetric)) := by
      exact mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr
          (by
            simpa [neg_mul] using
              (mul_le_mul_of_nonpos_left hmetric
                (neg_nonpos.mpr hlambda_nonneg))))
        hA

/-- Convention-robust version of the residual-product estimate.

The actual metric may fail the displayed singleton convention in (2.30).
It is enough to dominate it from below by a metric satisfying (2.27), since
the residual exponential decreases with the metric. -/
theorem cmp116Eq228_residualProduct_le_of_lowerMetric
    {ιY : Type*} [DecidableEq ιY]
    (D : Finset ιY) (hD : D.Nonempty)
    (metric lowerMetric : ιY → ℝ)
    (unionLowerMetric A delta kappa : ℝ)
    (hA : 0 ≤ A) (hdelta : 0 ≤ delta) (hkappa : 0 ≤ kappa)
    (hfourDelta : 4 * delta ≤ 1)
    (hsmall : A * Real.exp (5 * kappa) ≤ 1)
    (hlower : ∀ Y ∈ D, lowerMetric Y ≤ metric Y)
    (hEq227 :
      unionLowerMetric + 5 ≤
        ∑ Y ∈ D, (lowerMetric Y + 5)) :
    (∏ Y ∈ D,
        A * Real.exp (-((1 - 4 * delta) * kappa * metric Y))) ≤
      A *
        Real.exp (-((1 - 4 * delta) * kappa * unionLowerMetric)) := by
  have hlambda :
      0 ≤ (1 - 4 * delta) * kappa :=
    mul_nonneg (sub_nonneg.mpr hfourDelta) hkappa
  calc
    (∏ Y ∈ D,
        A * Real.exp (-((1 - 4 * delta) * kappa * metric Y))) ≤
      ∏ Y ∈ D,
        A * Real.exp
          (-((1 - 4 * delta) * kappa * lowerMetric Y)) := by
      exact Finset.prod_le_prod
        (fun _ _ => mul_nonneg hA (Real.exp_nonneg _))
        (fun Y hY =>
          mul_le_mul_of_nonneg_left
            (Real.exp_le_exp.mpr
              (neg_le_neg
                (mul_le_mul_of_nonneg_left
                  (hlower Y hY) hlambda)))
            hA)
    _ ≤
      A *
        Real.exp
          (-((1 - 4 * delta) * kappa * unionLowerMetric)) :=
      cmp116Eq228_residualProduct_le
        D hD lowerMetric unionLowerMetric A delta kappa
        hA hdelta hkappa hfourDelta hsmall hEq227

/-- Literal equation (2.28): the entire equation-(2.26) domain product is
bounded by the extracted equation-(2.29) product times the single residual
printed in the source. -/
theorem cmp116Eq226DomainProduct_le_eq229Product_mul_eq228Residual
    {ιY : Type*} [DecidableEq ιY]
    (D : Finset ιY) (hD : D.Nonempty)
    (E0 epsilon1 C1 alpha4 alpha6 : ℝ) (M q : ℕ)
    (C2 kappa1 delta kappa : ℝ)
    (domainMetric : ιY → ℕ) (unionMetric : ℝ)
    (hE0 : 0 ≤ E0) (hepsilon1 : 0 ≤ epsilon1)
    (hC1 : 0 ≤ C1) (halpha4 : 0 < alpha4)
    (halpha6 : 0 < alpha6)
    (hdelta : 0 ≤ delta) (hkappa : 0 ≤ kappa)
    (hfourDelta : 4 * delta ≤ 1)
    (hsmall :
      cmp116Eq228SourceCoefficient
          E0 epsilon1 C1 alpha4 alpha6 M q C2 kappa1 *
        Real.exp (5 * kappa) ≤ 1)
    (hEq227 :
      unionMetric + 5 ≤
        ∑ Y ∈ D, ((domainMetric Y : ℝ) + 5)) :
    cmp116Eq226DomainProduct
        E0 epsilon1 C1 alpha4 M q C2 kappa1 delta kappa
        domainMetric D ≤
      (∏ Y ∈ D,
          cmp116Eq229Weight alpha6 delta kappa domainMetric Y) *
        cmp116Eq228Residual
          E0 epsilon1 C1 alpha4 alpha6 M q C2 kappa1
          delta kappa unionMetric := by
  have hcoeff_nonneg :
      0 ≤
        cmp116Eq228SourceCoefficient
          E0 epsilon1 C1 alpha4 alpha6 M q C2 kappa1 := by
    exact
      cmp116Eq228SourceCoefficient_nonneg
        E0 epsilon1 C1 alpha4 alpha6 M q C2 kappa1
        hE0 hepsilon1 hC1 halpha4 halpha6
  have hresidualProduct :=
    cmp116Eq228_residualProduct_le
      D hD (fun Y => (domainMetric Y : ℝ)) unionMetric
      (cmp116Eq228SourceCoefficient
        E0 epsilon1 C1 alpha4 alpha6 M q C2 kappa1)
      delta kappa hcoeff_nonneg hdelta hkappa hfourDelta hsmall hEq227
  unfold cmp116Eq226DomainProduct
  calc
    (∏ Y ∈ D,
        cmp116Eq226DomainFactor
          E0 epsilon1 C1 alpha4 M q C2 kappa1 delta kappa
          domainMetric Y) =
      (∏ Y ∈ D,
          cmp116Eq229Weight alpha6 delta kappa domainMetric Y) *
        (∏ Y ∈ D,
          cmp116Eq228Residual
            E0 epsilon1 C1 alpha4 alpha6 M q C2 kappa1
            delta kappa (domainMetric Y : ℝ)) := by
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro Y _hY
      exact
        cmp116Eq226DomainFactor_eq_eq229Weight_mul_eq228Residual
          halpha6.ne'
    _ ≤
      (∏ Y ∈ D,
          cmp116Eq229Weight alpha6 delta kappa domainMetric Y) *
        cmp116Eq228Residual
          E0 epsilon1 C1 alpha4 alpha6 M q C2 kappa1
          delta kappa unionMetric := by
      exact mul_le_mul_of_nonneg_left hresidualProduct
        (Finset.prod_nonneg fun Y _ =>
          cmp116Eq229Weight_nonneg halpha6.le Y)

/-- Equation-(2.28) domain extraction when equation (2.27) is supplied by a
lower comparison metric.  The equation-(2.29) product still uses the actual
physical metric; only the residual union decay uses the convention-robust
lower metric. -/
theorem cmp116Eq226DomainProduct_le_eq229Product_mul_eq228Residual_of_lowerMetric
    {ιY : Type*} [DecidableEq ιY]
    (D : Finset ιY) (hD : D.Nonempty)
    (E0 epsilon1 C1 alpha4 alpha6 : ℝ) (M q : ℕ)
    (C2 kappa1 delta kappa : ℝ)
    (domainMetric lowerMetric : ιY → ℕ) (unionLowerMetric : ℝ)
    (hE0 : 0 ≤ E0) (hepsilon1 : 0 ≤ epsilon1)
    (hC1 : 0 ≤ C1) (halpha4 : 0 < alpha4)
    (halpha6 : 0 < alpha6)
    (hdelta : 0 ≤ delta) (hkappa : 0 ≤ kappa)
    (hfourDelta : 4 * delta ≤ 1)
    (hsmall :
      cmp116Eq228SourceCoefficient
          E0 epsilon1 C1 alpha4 alpha6 M q C2 kappa1 *
        Real.exp (5 * kappa) ≤ 1)
    (hlower :
      ∀ Y ∈ D, lowerMetric Y ≤ domainMetric Y)
    (hEq227 :
      unionLowerMetric + 5 ≤
        ∑ Y ∈ D, ((lowerMetric Y : ℝ) + 5)) :
    cmp116Eq226DomainProduct
        E0 epsilon1 C1 alpha4 M q C2 kappa1 delta kappa
        domainMetric D ≤
      (∏ Y ∈ D,
          cmp116Eq229Weight alpha6 delta kappa domainMetric Y) *
        cmp116Eq228Residual
          E0 epsilon1 C1 alpha4 alpha6 M q C2 kappa1
          delta kappa unionLowerMetric := by
  have hcoeff_nonneg :=
    cmp116Eq228SourceCoefficient_nonneg
      E0 epsilon1 C1 alpha4 alpha6 M q C2 kappa1
      hE0 hepsilon1 hC1 halpha4 halpha6
  have hresidualProduct :=
    cmp116Eq228_residualProduct_le_of_lowerMetric
      D hD
      (fun Y => (domainMetric Y : ℝ))
      (fun Y => (lowerMetric Y : ℝ))
      unionLowerMetric
      (cmp116Eq228SourceCoefficient
        E0 epsilon1 C1 alpha4 alpha6 M q C2 kappa1)
      delta kappa hcoeff_nonneg hdelta hkappa hfourDelta hsmall
      (fun Y hY => by
        change (lowerMetric Y : ℝ) ≤ (domainMetric Y : ℝ)
        exact_mod_cast hlower Y hY)
      hEq227
  unfold cmp116Eq226DomainProduct
  calc
    (∏ Y ∈ D,
        cmp116Eq226DomainFactor
          E0 epsilon1 C1 alpha4 M q C2 kappa1 delta kappa
          domainMetric Y) =
      (∏ Y ∈ D,
          cmp116Eq229Weight alpha6 delta kappa domainMetric Y) *
        (∏ Y ∈ D,
          cmp116Eq228Residual
            E0 epsilon1 C1 alpha4 alpha6 M q C2 kappa1
            delta kappa (domainMetric Y : ℝ)) := by
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro Y _hY
      exact
        cmp116Eq226DomainFactor_eq_eq229Weight_mul_eq228Residual
          halpha6.ne'
    _ ≤
      (∏ Y ∈ D,
          cmp116Eq229Weight alpha6 delta kappa domainMetric Y) *
        cmp116Eq228Residual
          E0 epsilon1 C1 alpha4 alpha6 M q C2 kappa1
          delta kappa unionLowerMetric := by
      exact mul_le_mul_of_nonneg_left hresidualProduct
        (Finset.prod_nonneg fun Y _ =>
          cmp116Eq229Weight_nonneg halpha6.le Y)

end

end YangMills.RG
