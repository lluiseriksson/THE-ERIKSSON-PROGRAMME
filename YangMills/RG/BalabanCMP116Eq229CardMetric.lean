/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq229ConnectedDomainSum

/-!
# Literal printed-cardinality route for CMP116 equation (2.29)

CMP116 equation (2.30) states, in four dimensions,

`|Y| / 24 ≤ d_k(Y)`.

This file treats that printed inequality as an explicit input.  The definition
of `d_k` in CMP109 also permits a degenerate zero-length tree for a one-cube
domain unless an additional convention is imposed, whereas the displayed
lower bound would then read `1 / 24 ≤ 0`.  Consequently this module is the
literal-display route, not a derivation of (2.30).

`BalabanCMP116Eq229ShiftedCardMetric` supplies the convention-robust route
based on `|Y| / 24 ≤ d_k(Y) + 1`; it preserves the volume-uniform conclusion
with one explicit extra half-rate in the scalar prefactor.

Therefore the physical activity is dominated by the one obtained from the
integer cardinal metric

`d̂(Y) = ceil (|Y| / 24)`.

For this canonical metric equation (2.27) is a theorem, not a premise:
exact union gives `|Y₀| ≤ ∑ |Y|`, ceiling division is subadditive, and the
shift by `5` is harmless because an exact-union family over nonempty `Y₀` is
nonempty.

This removes equation (2.27) from the public equation-(2.29) producer.  The
remaining source input is precisely the lower comparison in equation (2.30),
plus the explicit uniform smallness threshold.
-/

namespace YangMills.RG

open scoped BigOperators
open Finset

/-- Four-dimensional cardinal lower metric `ceil (|Y| / 24)`. -/
def cmp116Eq229CardMetric
    {V : Type*} (Y : Finset V) : ℕ :=
  Y.card ⌈/⌉ 24

/-- The defining ceiling-division bound. -/
theorem card_le_twentyFour_mul_cmp116Eq229CardMetric
    {V : Type*} (Y : Finset V) :
    Y.card ≤ 24 * cmp116Eq229CardMetric Y := by
  exact
    (ceilDiv_le_iff_le_mul (a := 24) (b := Y.card)
      (c := cmp116Eq229CardMetric Y) (by norm_num)).mp (by rfl)

/-- The real form of the cardinal lower bound, matching equation (2.30). -/
theorem card_div_twentyFour_le_cmp116Eq229CardMetric
    {V : Type*} (Y : Finset V) :
    (Y.card : ℝ) / 24 ≤ (cmp116Eq229CardMetric Y : ℝ) := by
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 24)).mpr
  have h := card_le_twentyFour_mul_cmp116Eq229CardMetric Y
  exact_mod_cast (by simpa [Nat.mul_comm] using h)

/-- Ceiling cardinality is subadditive over a finite union. -/
theorem cmp116Eq229CardMetric_union_le_sum
    {V : Type*} [DecidableEq V]
    (D : Finset (Finset V)) :
    cmp116Eq229CardMetric (cmp116Eq23Y0 D) ≤
      ∑ Y ∈ D, cmp116Eq229CardMetric Y := by
  apply
    (ceilDiv_le_iff_le_mul
      (a := 24)
      (b := (cmp116Eq23Y0 D).card)
      (c := ∑ Y ∈ D, cmp116Eq229CardMetric Y)
      (by norm_num)).mpr
  calc
    (cmp116Eq23Y0 D).card =
        (D.biUnion fun Y => Y).card := by rfl
    _ ≤ ∑ Y ∈ D, Y.card := Finset.card_biUnion_le
    _ ≤ ∑ Y ∈ D, 24 * cmp116Eq229CardMetric Y := by
      exact Finset.sum_le_sum fun Y _hY =>
        card_le_twentyFour_mul_cmp116Eq229CardMetric Y
    _ = 24 * (∑ Y ∈ D, cmp116Eq229CardMetric Y) := by
      rw [Finset.mul_sum]

/-- Equation (2.27) follows automatically for the cardinal lower metric on
every nonempty exact-union fiber. -/
theorem cmp116Eq229CardMetric_eq227
    {V : Type*} [DecidableEq V]
    (domainFamily : Finset (Finset V))
    (Y0 : Finset V) (hY0 : Y0.Nonempty)
    (D : Finset (Finset V))
    (hD : D ∈ cmp116Eq229ExactUnionDIndex domainFamily Y0) :
    (cmp116Eq229CardMetric Y0 : ℝ) + 5 ≤
      ∑ Y ∈ D, ((cmp116Eq229CardMetric Y : ℝ) + 5) := by
  have hUnion :=
    (mem_cmp116Eq229ExactUnionDIndex_iff domainFamily Y0 D).mp hD |>.2
  have hDnonempty : D.Nonempty := by
    by_contra hDempty
    rw [Finset.not_nonempty_iff_eq_empty] at hDempty
    subst D
    have : Y0 = ∅ := by
      simpa [cmp116Eq23Y0] using hUnion.symm
    exact hY0.ne_empty this
  have hmetric :
      cmp116Eq229CardMetric Y0 ≤
        ∑ Y ∈ D, cmp116Eq229CardMetric Y := by
    rw [← hUnion]
    exact cmp116Eq229CardMetric_union_le_sum D
  have hcard : 1 ≤ D.card := Finset.card_pos.mpr hDnonempty
  have hmetricR :
      (cmp116Eq229CardMetric Y0 : ℝ) ≤
        ∑ Y ∈ D, (cmp116Eq229CardMetric Y : ℝ) := by
    exact_mod_cast hmetric
  have hcardR : (1 : ℝ) ≤ (D.card : ℝ) := by
    exact_mod_cast hcard
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const, nsmul_eq_mul]
  nlinarith

/-- Equation (2.30) implies pointwise domination of the physical (2.29)
activity by the canonical cardinal-metric activity. -/
theorem cmp116Eq229Weight_le_cardMetricWeight_of_eq230
    {V : Type*}
    (alpha6 delta kappa : ℝ)
    (metric : Finset V → ℕ)
    (Y : Finset V)
    (halpha6 : 0 ≤ alpha6)
    (hdeltaKappa : 0 ≤ delta * kappa)
    (hEq230 : (Y.card : ℝ) / 24 ≤ (metric Y : ℝ)) :
    cmp116Eq229Weight alpha6 delta kappa metric Y ≤
      cmp116Eq229Weight
        alpha6 delta kappa cmp116Eq229CardMetric Y := by
  have hcardMetric :
      cmp116Eq229CardMetric Y ≤ metric Y := by
    apply
      (ceilDiv_le_iff_le_mul
        (a := 24) (b := Y.card) (c := metric Y) (by norm_num)).mpr
    have hreal :
        (Y.card : ℝ) ≤ 24 * (metric Y : ℝ) := by
      nlinarith
    exact_mod_cast hreal
  rw [cmp116Eq229Weight, cmp116Eq229Weight]
  apply mul_le_mul_of_nonneg_left ?_ halpha6
  apply Real.exp_le_exp.mpr
  exact neg_le_neg
    (mul_le_mul_of_nonneg_left
      (by exact_mod_cast hcardMetric)
      hdeltaKappa)

/-- Product domination on a physical exact-union family. -/
theorem cmp116Eq229Product_le_cardMetricProduct_of_eq230
    {V : Type*} [DecidableEq V]
    (domainFamily : Finset (Finset V))
    (D : Finset (Finset V))
    (alpha6 delta kappa : ℝ)
    (metric : Finset V → ℕ)
    (halpha6 : 0 ≤ alpha6)
    (hdeltaKappa : 0 ≤ delta * kappa)
    (hEq230 :
      ∀ Y ∈ domainFamily,
        (Y.card : ℝ) / 24 ≤ (metric Y : ℝ))
    (hDsource : D ⊆ domainFamily) :
    (∏ Y ∈ D, cmp116Eq229Weight alpha6 delta kappa metric Y) ≤
      ∏ Y ∈ D,
        cmp116Eq229Weight
          alpha6 delta kappa cmp116Eq229CardMetric Y := by
  exact Finset.prod_le_prod
    (fun Y _hY => cmp116Eq229Weight_nonneg
      (metric := metric) halpha6 Y)
    (fun Y hY =>
      cmp116Eq229Weight_le_cardMetricWeight_of_eq230
        alpha6 delta kappa metric Y halpha6 hdeltaKappa
        (hEq230 Y (hDsource hY)))

/-- Four-dimensional equation-(2.29) fiber estimate conditional on the
literal printed lower comparison, with equation (2.27) fully derived.

The physical metric occurs only through the lower comparison (2.30). -/
theorem cmp116Eq229ExactUnion_sum_prod_le_one_of_eq230_uniform
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
    (hEq230 :
      ∀ Y ∈ domainFamily,
        (Y.card : ℝ) / 24 ≤ (metric Y : ℝ))
    (hCq :
      64 * Real.exp (-((delta * kappa) / 48)) < 1)
    (huniform :
      (alpha6 * Real.exp (5 * (delta * kappa) / 2)) *
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
            alpha6 delta kappa cmp116Eq229CardMetric Y := by
      refine Finset.sum_le_sum fun D hD => ?_
      exact
        cmp116Eq229Product_le_cardMetricProduct_of_eq230
          domainFamily D alpha6 delta kappa metric
          halpha6 hdeltaKappa hEq230
          ((mem_cmp116Eq229ExactUnionDIndex_iff
            domainFamily Y0 D).mp hD).1
    _ ≤ 1 := by
      exact
        cmp116Eq229ExactUnion_sum_prod_le_one_fourDimensional_of_uniform
          domainFamily Y0 hY0 hdomains
          alpha6 delta kappa cmp116Eq229CardMetric
          halpha6 hdeltaKappa
          (fun D hD =>
            cmp116Eq229CardMetric_eq227 domainFamily Y0 hY0 D hD)
          (fun Y _hY =>
            card_div_twentyFour_le_cmp116Eq229CardMetric Y)
          (card_div_twentyFour_le_cmp116Eq229CardMetric Y0)
          hCq huniform

/-- Final literal-display equation-(2.29) producer for all nonempty fixed
unions.

This is the interface consumed by the downstream Lemma-3/KP pipeline.  It has
no hypothesis equivalent to equation (2.27) or equation (2.29): the only
geometric analytic input is the literal lower comparison from equation
(2.30). -/
theorem CMP116Eq229Summability.of_exactUnion_fourDimensional_eq230_uniform
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
    (hEq230 :
      ∀ Y ∈ domainFamily,
        (Y.card : ℝ) / 24 ≤ (metric Y : ℝ))
    (hCq :
      64 * Real.exp (-((delta * kappa) / 48)) < 1)
    (huniform :
      (alpha6 * Real.exp (5 * (delta * kappa) / 2)) *
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
    cmp116Eq229ExactUnion_sum_prod_le_one_of_eq230_uniform
      domainFamily Y0.1 Y0.2 hdomains
      alpha6 delta kappa metric halpha6 hdeltaKappa
      hEq230 hCq huniform

end YangMills.RG
