/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq229CardMetric

/-!
# Convention-robust cardinal route for CMP116 equation (2.29)

The printed lower inequality in CMP116 equation (2.30),

`|Y| / 24 ≤ d_k(Y)`,

conflicts with the degenerate zero-length tree on a one-cube localization
domain unless the source uses an additional convention for tree graphs.
The convention-independent estimate is the shifted inequality

`|Y| / 24 ≤ d_k(Y) + 1`.

This file proves that the shift does not obstruct equation (2.29).  We use

`ď(Y) = pred (ceil (|Y| / 24))`.

For nonempty domains, `ď(Y) + 1 = ceil (|Y| / 24)`.  Hence:

* `ď(Y) ≤ d_k(Y)` follows from the shifted comparison;
* equation (2.27) follows from exact union and nonemptiness;
* connected-domain entropy is still geometric, with the prefactor changed
  from `exp (5 λ / 2)` to `exp (3 λ)`; and
* the final uniform absorption leaves `exp (-2 λ) ≤ 1`.

No convention for the metric on a singleton is hidden in the interface.
-/

namespace YangMills.RG

open scoped BigOperators
open Finset

/-- Cardinal lower metric compatible with the shifted source inequality. -/
def cmp116Eq229ShiftedCardMetric
    {V : Type*} (Y : Finset V) : ℕ :=
  (cmp116Eq229CardMetric Y).pred

/-- For every finite set, the unshifted ceiling metric is at most one more
than the shifted metric. -/
theorem cmp116Eq229CardMetric_le_shifted_add_one
    {V : Type*} (Y : Finset V) :
    cmp116Eq229CardMetric Y ≤ cmp116Eq229ShiftedCardMetric Y + 1 := by
  cases hmetric : cmp116Eq229CardMetric Y with
  | zero =>
      simp [cmp116Eq229ShiftedCardMetric, hmetric]
  | succ n =>
      simp [cmp116Eq229ShiftedCardMetric, hmetric]

/-- The robust cardinal comparison holds without any nonemptiness
assumption. -/
theorem card_div_twentyFour_le_shiftedCardMetric_add_one
    {V : Type*} (Y : Finset V) :
    (Y.card : ℝ) / 24 ≤
      (cmp116Eq229ShiftedCardMetric Y : ℝ) + 1 := by
  have hceil :=
    card_div_twentyFour_le_cmp116Eq229CardMetric Y
  have hnat :=
    cmp116Eq229CardMetric_le_shifted_add_one Y
  have hreal :
      (cmp116Eq229CardMetric Y : ℝ) ≤
        (cmp116Eq229ShiftedCardMetric Y : ℝ) + 1 := by
    exact_mod_cast hnat
  exact hceil.trans hreal

/-- On nonempty domains the shift is an exact predecessor. -/
theorem shiftedCardMetric_add_one_eq_cardMetric
    {V : Type*} (Y : Finset V) (hY : Y.Nonempty) :
    cmp116Eq229ShiftedCardMetric Y + 1 =
      cmp116Eq229CardMetric Y := by
  have hcardPos : 0 < Y.card := Finset.card_pos.mpr hY
  have hbound :=
    card_le_twentyFour_mul_cmp116Eq229CardMetric Y
  have hmetricPos : 0 < cmp116Eq229CardMetric Y := by
    omega
  exact Nat.succ_pred_eq_of_pos hmetricPos

/-- Equation (2.27) follows for the shifted cardinal metric on exact-union
families of nonempty physical domains. -/
theorem cmp116Eq229ShiftedCardMetric_eq227
    {V : Type*} [DecidableEq V]
    (domainFamily : Finset (Finset V))
    (hdomains : ∀ Y ∈ domainFamily, Y.Nonempty)
    (Y0 : Finset V) (hY0 : Y0.Nonempty)
    (D : Finset (Finset V))
    (hD : D ∈ cmp116Eq229ExactUnionDIndex domainFamily Y0) :
    (cmp116Eq229ShiftedCardMetric Y0 : ℝ) + 5 ≤
      ∑ Y ∈ D, ((cmp116Eq229ShiftedCardMetric Y : ℝ) + 5) := by
  have hsource :=
    (mem_cmp116Eq229ExactUnionDIndex_iff domainFamily Y0 D).mp hD
  have hDnonempty : D.Nonempty := by
    by_contra hDempty
    rw [Finset.not_nonempty_iff_eq_empty] at hDempty
    subst D
    have : Y0 = ∅ := by
      simpa [cmp116Eq23Y0] using hsource.2.symm
    exact hY0.ne_empty this
  have hunion :
      cmp116Eq229CardMetric Y0 ≤
        ∑ Y ∈ D, cmp116Eq229CardMetric Y := by
    rw [← hsource.2]
    exact cmp116Eq229CardMetric_union_le_sum D
  have hY0shift :=
    shiftedCardMetric_add_one_eq_cardMetric Y0 hY0
  have hterms :
      ∀ Y ∈ D,
        cmp116Eq229ShiftedCardMetric Y + 1 =
          cmp116Eq229CardMetric Y := by
    intro Y hYD
    exact shiftedCardMetric_add_one_eq_cardMetric
      Y (hdomains Y (hsource.1 hYD))
  have hunionR :
      (cmp116Eq229CardMetric Y0 : ℝ) ≤
        ∑ Y ∈ D, (cmp116Eq229CardMetric Y : ℝ) := by
    exact_mod_cast hunion
  have hcardR : (1 : ℝ) ≤ (D.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hDnonempty
  have hsum :
      (∑ Y ∈ D, ((cmp116Eq229ShiftedCardMetric Y : ℝ) + 5)) =
        (∑ Y ∈ D, (cmp116Eq229CardMetric Y : ℝ)) +
          4 * (D.card : ℝ) := by
    calc
      (∑ Y ∈ D, ((cmp116Eq229ShiftedCardMetric Y : ℝ) + 5)) =
          ∑ Y ∈ D, ((cmp116Eq229CardMetric Y : ℝ) + 4) := by
            apply Finset.sum_congr rfl
            intro Y hYD
            have h := hterms Y hYD
            have hR :
                (cmp116Eq229ShiftedCardMetric Y : ℝ) + 1 =
                  (cmp116Eq229CardMetric Y : ℝ) := by
              exact_mod_cast h
            linarith
      _ =
          (∑ Y ∈ D, (cmp116Eq229CardMetric Y : ℝ)) +
            4 * (D.card : ℝ) := by
              rw [Finset.sum_add_distrib]
              simp [nsmul_eq_mul, mul_comm]
  rw [hsum]
  have hY0shiftR :
      (cmp116Eq229ShiftedCardMetric Y0 : ℝ) + 1 =
        (cmp116Eq229CardMetric Y0 : ℝ) := by
    exact_mod_cast hY0shift
  nlinarith

/-- The shifted comparison implies domination by the shifted cardinal
activity. -/
theorem cmp116Eq229Weight_le_shiftedCardMetricWeight_of_eq230Shifted
    {V : Type*}
    (alpha6 delta kappa : ℝ)
    (metric : Finset V → ℕ)
    (Y : Finset V)
    (halpha6 : 0 ≤ alpha6)
    (hdeltaKappa : 0 ≤ delta * kappa)
    (hEq230Shifted :
      (Y.card : ℝ) / 24 ≤ (metric Y : ℝ) + 1) :
    cmp116Eq229Weight alpha6 delta kappa metric Y ≤
      cmp116Eq229Weight
        alpha6 delta kappa cmp116Eq229ShiftedCardMetric Y := by
  have hceil :
      cmp116Eq229CardMetric Y ≤ metric Y + 1 := by
    apply
      (ceilDiv_le_iff_le_mul
        (a := 24) (b := Y.card) (c := metric Y + 1)
        (by norm_num)).mpr
    have hreal :
        (Y.card : ℝ) ≤ 24 * ((metric Y : ℝ) + 1) := by
      nlinarith
    exact_mod_cast hreal
  have hshift :
      cmp116Eq229ShiftedCardMetric Y ≤ metric Y := by
    calc
      cmp116Eq229ShiftedCardMetric Y =
          (cmp116Eq229CardMetric Y).pred := rfl
      _ ≤ (metric Y + 1).pred := Nat.pred_le_pred hceil
      _ = metric Y := by simp
  rw [cmp116Eq229Weight, cmp116Eq229Weight]
  apply mul_le_mul_of_nonneg_left ?_ halpha6
  apply Real.exp_le_exp.mpr
  exact neg_le_neg
    (mul_le_mul_of_nonneg_left
      (by exact_mod_cast hshift)
      hdeltaKappa)

/-- The shifted cardinal metric gives the same geometric decay as the
printed route, with one extra half-rate in the prefactor. -/
theorem cmp116Eq229HalfFugacityWeight_le_cardWeight_shifted
    {V : Type*}
    (alpha6 delta kappa : ℝ)
    (Y : Finset V)
    (halpha6 : 0 ≤ alpha6)
    (hdeltaKappa : 0 ≤ delta * kappa) :
    cmp116Eq229HalfFugacityWeight
        alpha6 delta kappa cmp116Eq229ShiftedCardMetric Y ≤
      (alpha6 * Real.exp (3 * (delta * kappa))) *
        Real.exp (-((delta * kappa) / 48)) ^ Y.card := by
  rw [cmp116Eq229HalfFugacityWeight]
  have hshift :=
    card_div_twentyFour_le_shiftedCardMetric_add_one Y
  have hexp :
      Real.exp
          (((delta * kappa) / 2) *
            (5 - (cmp116Eq229ShiftedCardMetric Y : ℝ))) ≤
        Real.exp (3 * (delta * kappa)) *
          Real.exp (-((delta * kappa) / 48)) ^ Y.card := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hscaled :
        ((delta * kappa) / 2) * ((Y.card : ℝ) / 24) ≤
          ((delta * kappa) / 2) *
            ((cmp116Eq229ShiftedCardMetric Y : ℝ) + 1) :=
      mul_le_mul_of_nonneg_left hshift
        (div_nonneg hdeltaKappa (by norm_num))
    nlinarith
  simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left hexp halpha6

/-- Connected-domain entropy for the convention-robust metric. -/
theorem cmp116Eq229_localHalfFugacitySum_le_shifted
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (domainFamily : Finset (Finset V))
    (Y0 : Finset V)
    (hdomains :
      ∀ Y ∈ domainFamily,
        Y.Nonempty ∧ walkConnected G Y)
    (alpha6 delta kappa : ℝ)
    (halpha6 : 0 ≤ alpha6)
    (hdeltaKappa : 0 ≤ delta * kappa)
    {Δ : ℕ}
    (hΔ : ∀ x, G.degree x ≤ Δ)
    (hΔ1 : 1 ≤ Δ)
    (hCq :
      (Δ : ℝ) ^ 2 * Real.exp (-((delta * kappa) / 48)) < 1) :
    (∑ Y ∈ domainFamily.filter (fun Y => Y ⊆ Y0),
        cmp116Eq229HalfFugacityWeight
          alpha6 delta kappa cmp116Eq229ShiftedCardMetric Y) ≤
      (alpha6 * Real.exp (3 * (delta * kappa))) *
        ((Y0.card : ℝ) *
          (1 -
            (Δ : ℝ) ^ 2 *
              Real.exp (-((delta * kappa) / 48)))⁻¹) := by
  let q : ℝ := Real.exp (-((delta * kappa) / 48))
  let prefactor : ℝ :=
    alpha6 * Real.exp (3 * (delta * kappa))
  have hq0 : 0 ≤ q := Real.exp_nonneg _
  have hprefactor : 0 ≤ prefactor :=
    mul_nonneg halpha6 (Real.exp_nonneg _)
  have hpoint :
      ∀ Y ∈ domainFamily.filter (fun Y => Y ⊆ Y0),
        cmp116Eq229HalfFugacityWeight
            alpha6 delta kappa cmp116Eq229ShiftedCardMetric Y ≤
          prefactor * q ^ Y.card := by
    intro Y _hY
    simpa [q, prefactor] using
      cmp116Eq229HalfFugacityWeight_le_cardWeight_shifted
        alpha6 delta kappa Y halpha6 hdeltaKappa
  have hanimal :
      (∑ Y ∈ domainFamily.filter (fun Y => Y ⊆ Y0),
          q ^ Y.card) ≤
        (Y0.card : ℝ) * (1 - (Δ : ℝ) ^ 2 * q)⁻¹ :=
    connectedDomainFamily_sum_pow_card_le
      domainFamily Y0 hdomains hΔ hΔ1 hq0
        (by simpa [q] using hCq)
  calc
    (∑ Y ∈ domainFamily.filter (fun Y => Y ⊆ Y0),
        cmp116Eq229HalfFugacityWeight
          alpha6 delta kappa cmp116Eq229ShiftedCardMetric Y) ≤
      ∑ Y ∈ domainFamily.filter (fun Y => Y ⊆ Y0),
        prefactor * q ^ Y.card := by
          exact Finset.sum_le_sum fun Y hY => hpoint Y hY
    _ =
      prefactor *
        (∑ Y ∈ domainFamily.filter (fun Y => Y ⊆ Y0),
          q ^ Y.card) := by
            rw [Finset.mul_sum]
    _ ≤
      prefactor *
        ((Y0.card : ℝ) * (1 - (Δ : ℝ) ^ 2 * q)⁻¹) :=
          mul_le_mul_of_nonneg_left hanimal hprefactor
    _ =
      (alpha6 * Real.exp (3 * (delta * kappa))) *
        ((Y0.card : ℝ) *
          (1 -
            (Δ : ℝ) ^ 2 *
              Real.exp (-((delta * kappa) / 48)))⁻¹) := by
          rfl

/-- The uniform shifted smallness threshold absorbs all local-domain entropy.
The residual shift is four half-rates, hence nonpositive. -/
theorem cmp116Eq229_shifted_localSmallness_of_uniform
    (alpha6 delta kappa : ℝ)
    (Y0card metricY0 : ℕ)
    (halpha6 : 0 ≤ alpha6)
    (hdeltaKappa : 0 ≤ delta * kappa)
    (hEq230ShiftedY0 :
      (Y0card : ℝ) / 24 ≤ (metricY0 : ℝ) + 1)
    (hCq :
      64 * Real.exp (-((delta * kappa) / 48)) < 1)
    (huniform :
      (alpha6 * Real.exp (3 * (delta * kappa))) *
          24 *
          (1 -
            64 * Real.exp (-((delta * kappa) / 48)))⁻¹ ≤
        (delta * kappa) / 2) :
    Real.exp
          (-((delta * kappa) / 2) * ((metricY0 : ℝ) + 5)) *
        (Real.exp
            ((alpha6 * Real.exp (3 * (delta * kappa))) *
              ((Y0card : ℝ) *
                (1 -
                  64 *
                    Real.exp (-((delta * kappa) / 48)))⁻¹)) -
          1) ≤
      1 := by
  let halfRate : ℝ := (delta * kappa) / 2
  let entropyCoefficient : ℝ :=
    (alpha6 * Real.exp (3 * (delta * kappa))) *
      (1 -
        64 * Real.exp (-((delta * kappa) / 48)))⁻¹
  let entropy : ℝ := entropyCoefficient * (Y0card : ℝ)
  have hden_pos :
      0 <
        1 - 64 * Real.exp (-((delta * kappa) / 48)) := by
    linarith
  have hcoefficient_nonneg : 0 ≤ entropyCoefficient := by
    exact mul_nonneg
      (mul_nonneg halpha6 (Real.exp_nonneg _))
      (inv_nonneg.mpr hden_pos.le)
  have hhalf_nonneg : 0 ≤ halfRate := by
    exact div_nonneg hdeltaKappa (by norm_num)
  have huniform' : entropyCoefficient * 24 ≤ halfRate := by
    simpa [entropyCoefficient, halfRate, mul_assoc, mul_comm, mul_left_comm]
      using huniform
  have hentropy_le :
      entropy ≤ halfRate * ((metricY0 : ℝ) + 1) := by
    have hcard_nonneg : 0 ≤ (Y0card : ℝ) / 24 := by positivity
    have hfirst :
        (entropyCoefficient * 24) * ((Y0card : ℝ) / 24) ≤
          halfRate * ((Y0card : ℝ) / 24) :=
      mul_le_mul_of_nonneg_right huniform' hcard_nonneg
    have hsecond :
        halfRate * ((Y0card : ℝ) / 24) ≤
          halfRate * ((metricY0 : ℝ) + 1) :=
      mul_le_mul_of_nonneg_left hEq230ShiftedY0 hhalf_nonneg
    calc
      entropy =
          (entropyCoefficient * 24) * ((Y0card : ℝ) / 24) := by
            simp [entropy]
            ring
      _ ≤ halfRate * ((Y0card : ℝ) / 24) := hfirst
      _ ≤ halfRate * ((metricY0 : ℝ) + 1) := hsecond
  have hexponent :
      -(halfRate * ((metricY0 : ℝ) + 5)) + entropy ≤
        -(halfRate * 4) := by
    linarith
  calc
    Real.exp
          (-((delta * kappa) / 2) * ((metricY0 : ℝ) + 5)) *
        (Real.exp
            ((alpha6 * Real.exp (3 * (delta * kappa))) *
              ((Y0card : ℝ) *
                (1 -
                  64 *
                    Real.exp (-((delta * kappa) / 48)))⁻¹)) -
          1) ≤
      Real.exp (-(halfRate * ((metricY0 : ℝ) + 5))) *
        Real.exp entropy := by
          have hsubexp : Real.exp entropy - 1 ≤ Real.exp entropy :=
            sub_le_self _ (by norm_num)
          have hmul :=
            mul_le_mul_of_nonneg_left hsubexp
              (Real.exp_nonneg
                (-(halfRate * ((metricY0 : ℝ) + 5))))
          simpa [halfRate, entropy, entropyCoefficient,
            mul_assoc, mul_comm, mul_left_comm] using hmul
    _ =
      Real.exp
        (-(halfRate * ((metricY0 : ℝ) + 5)) + entropy) := by
          rw [Real.exp_add]
    _ ≤ Real.exp (-(halfRate * 4)) :=
      Real.exp_le_exp.mpr hexponent
    _ ≤ Real.exp 0 := by
      apply Real.exp_le_exp.mpr
      exact neg_nonpos.mpr (mul_nonneg hhalf_nonneg (by norm_num))
    _ = 1 := Real.exp_zero

/-- Convention-robust four-dimensional fixed-union estimate for the shifted
cardinal metric itself. -/
theorem cmp116Eq229ExactUnion_sum_prod_le_one_shiftedCardMetric_uniform
    {N' : ℕ} [NeZero N']
    (domainFamily : Finset (Finset (FinBox 4 N')))
    (Y0 : Finset (FinBox 4 N')) (hY0 : Y0.Nonempty)
    (hdomains :
      ∀ Y ∈ domainFamily,
        Y.Nonempty ∧
          walkConnected (cmp116CoarseFaceAdj 4 N') Y)
    (alpha6 delta kappa : ℝ)
    (halpha6 : 0 ≤ alpha6)
    (hdeltaKappa : 0 ≤ delta * kappa)
    (hCq :
      64 * Real.exp (-((delta * kappa) / 48)) < 1)
    (huniform :
      (alpha6 * Real.exp (3 * (delta * kappa))) *
          24 *
          (1 -
            64 * Real.exp (-((delta * kappa) / 48)))⁻¹ ≤
        (delta * kappa) / 2) :
    (∑ D ∈ cmp116Eq229ExactUnionDIndex domainFamily Y0,
        ∏ Y ∈ D,
          cmp116Eq229Weight
            alpha6 delta kappa cmp116Eq229ShiftedCardMetric Y) ≤
      1 := by
  apply
    cmp116Eq229ExactUnion_sum_prod_le_one_of_eq227_and_localSmallness
      domainFamily Y0 hY0 alpha6 delta kappa
      cmp116Eq229ShiftedCardMetric
      halpha6 hdeltaKappa
      (fun D hD =>
        cmp116Eq229ShiftedCardMetric_eq227
          domainFamily (fun Y hY => (hdomains Y hY).1)
          Y0 hY0 D hD)
  have hlocal :=
    cmp116Eq229_localHalfFugacitySum_le_shifted
      domainFamily Y0 hdomains alpha6 delta kappa
      halpha6 hdeltaKappa
      (Δ := 8)
      (cmp116CoarseFaceAdj_degree_le_eight N')
      (by norm_num)
      (by
        norm_num at hCq ⊢
        exact hCq)
  have hsmall :=
    cmp116Eq229_shifted_localSmallness_of_uniform
      alpha6 delta kappa Y0.card
      (cmp116Eq229ShiftedCardMetric Y0)
      halpha6 hdeltaKappa
      (card_div_twentyFour_le_shiftedCardMetric_add_one Y0)
      hCq huniform
  have hlocal' :
      (∑ Y ∈ domainFamily.filter (fun Y => Y ⊆ Y0),
          cmp116Eq229HalfFugacityWeight
            alpha6 delta kappa cmp116Eq229ShiftedCardMetric Y) ≤
        (alpha6 * Real.exp (3 * (delta * kappa))) *
          ((Y0.card : ℝ) *
            (1 -
              64 *
                Real.exp (-((delta * kappa) / 48)))⁻¹) := by
    norm_num at hlocal ⊢
    exact hlocal
  calc
    Real.exp
          (-((delta * kappa) / 2) *
            ((cmp116Eq229ShiftedCardMetric Y0 : ℝ) + 5)) *
        (Real.exp
            (∑ Y ∈ domainFamily.filter (fun Y => Y ⊆ Y0),
              cmp116Eq229HalfFugacityWeight
                alpha6 delta kappa
                cmp116Eq229ShiftedCardMetric Y) -
          1) ≤
      Real.exp
          (-((delta * kappa) / 2) *
            ((cmp116Eq229ShiftedCardMetric Y0 : ℝ) + 5)) *
        (Real.exp
            ((alpha6 * Real.exp (3 * (delta * kappa))) *
              ((Y0.card : ℝ) *
                (1 -
                  64 *
                    Real.exp (-((delta * kappa) / 48)))⁻¹)) -
          1) := by
            exact mul_le_mul_of_nonneg_left
              (sub_le_sub_right (Real.exp_le_exp.mpr hlocal') 1)
              (Real.exp_nonneg _)
    _ ≤ 1 := hsmall

/-- Physical equation-(2.29) from the convention-robust shifted comparison.

Neither equation (2.27) nor equation (2.29) is a hypothesis. -/
theorem cmp116Eq229ExactUnion_sum_prod_le_one_of_eq230Shifted_uniform
    {N' : ℕ} [NeZero N']
    (domainFamily : Finset (Finset (FinBox 4 N')))
    (Y0 : Finset (FinBox 4 N')) (hY0 : Y0.Nonempty)
    (hdomains :
      ∀ Y ∈ domainFamily,
        Y.Nonempty ∧
          walkConnected (cmp116CoarseFaceAdj 4 N') Y)
    (alpha6 delta kappa : ℝ)
    (metric : Finset (FinBox 4 N') → ℕ)
    (halpha6 : 0 ≤ alpha6)
    (hdeltaKappa : 0 ≤ delta * kappa)
    (hEq230Shifted :
      ∀ Y ∈ domainFamily,
        (Y.card : ℝ) / 24 ≤ (metric Y : ℝ) + 1)
    (hCq :
      64 * Real.exp (-((delta * kappa) / 48)) < 1)
    (huniform :
      (alpha6 * Real.exp (3 * (delta * kappa))) *
          24 *
          (1 -
            64 * Real.exp (-((delta * kappa) / 48)))⁻¹ ≤
        (delta * kappa) / 2) :
    (∑ D ∈ cmp116Eq229ExactUnionDIndex domainFamily Y0,
        ∏ Y ∈ D, cmp116Eq229Weight alpha6 delta kappa metric Y) ≤
      1 := by
  calc
    (∑ D ∈ cmp116Eq229ExactUnionDIndex domainFamily Y0,
        ∏ Y ∈ D, cmp116Eq229Weight alpha6 delta kappa metric Y) ≤
      ∑ D ∈ cmp116Eq229ExactUnionDIndex domainFamily Y0,
        ∏ Y ∈ D,
          cmp116Eq229Weight
            alpha6 delta kappa cmp116Eq229ShiftedCardMetric Y := by
      refine Finset.sum_le_sum fun D hD => ?_
      have hsource :=
        (mem_cmp116Eq229ExactUnionDIndex_iff
          domainFamily Y0 D).mp hD |>.1
      exact Finset.prod_le_prod
        (fun Y _hY =>
          cmp116Eq229Weight_nonneg
            (metric := metric) halpha6 Y)
        (fun Y hY =>
          cmp116Eq229Weight_le_shiftedCardMetricWeight_of_eq230Shifted
            alpha6 delta kappa metric Y halpha6 hdeltaKappa
            (hEq230Shifted Y (hsource hY)))
    _ ≤ 1 :=
      cmp116Eq229ExactUnion_sum_prod_le_one_shiftedCardMetric_uniform
        domainFamily Y0 hY0 hdomains
        alpha6 delta kappa halpha6 hdeltaKappa hCq huniform

/-- Legacy-consumer adapter for the convention-robust physical estimate. -/
theorem CMP116Eq229Summability.of_exactUnion_fourDimensional_eq230Shifted_uniform
    {N' : ℕ} [NeZero N']
    (domainFamily : Finset (Finset (FinBox 4 N')))
    (hdomains :
      ∀ Y ∈ domainFamily,
        Y.Nonempty ∧
          walkConnected (cmp116CoarseFaceAdj 4 N') Y)
    (alpha6 delta kappa : ℝ)
    (metric : Finset (FinBox 4 N') → ℕ)
    (halpha6 : 0 ≤ alpha6)
    (hdeltaKappa : 0 ≤ delta * kappa)
    (hEq230Shifted :
      ∀ Y ∈ domainFamily,
        (Y.card : ℝ) / 24 ≤ (metric Y : ℝ) + 1)
    (hCq :
      64 * Real.exp (-((delta * kappa) / 48)) < 1)
    (huniform :
      (alpha6 * Real.exp (3 * (delta * kappa))) *
          24 *
          (1 -
            64 * Real.exp (-((delta * kappa) / 48)))⁻¹ ≤
        (delta * kappa) / 2) :
    CMP116Eq229Summability
      (fun Y0 : {Y0 : Finset (FinBox 4 N') // Y0.Nonempty} =>
        cmp116Eq229ExactUnionDIndex domainFamily Y0.1)
      (fun _Y0 D => D)
      alpha6 delta kappa
      (fun _Y0 Y => metric Y) := by
  intro Y0
  exact
    cmp116Eq229ExactUnion_sum_prod_le_one_of_eq230Shifted_uniform
      domainFamily Y0.1 Y0.2 hdomains
      alpha6 delta kappa metric halpha6 hdeltaKappa
      hEq230Shifted hCq huniform

end YangMills.RG
